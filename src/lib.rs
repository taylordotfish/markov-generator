/*
 * Copyright (C) 2022, 2024 taylor.fish <contact@taylor.fish>
 *
 * This file is part of markov-generator.
 *
 * markov-generator is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * markov-generator is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with markov-generator. If not, see <https://www.gnu.org/licenses/>.
 */

#![warn(missing_docs)]
#![deny(unsafe_code)]
#![cfg_attr(not(any(feature = "std", doc)), no_std)]
#![cfg_attr(feature = "doc_cfg", feature(doc_cfg))]

//! A highly customizable Rust library for building [Markov chains] and
//! generating random sequences from them.
//!
//! [Markov chains]: https://en.wikipedia.org/wiki/Markov_chain
//!
//! [`Chain`] implements [Serde]’s [`Serialize`] and [`Deserialize`] traits, so
//! you can reuse chains without having to regenerate them every time (which
//! can be a lengthy process).
//!
//! Example
//! -------
//!
//! ```rust
//! use markov_generator::{AddEdges, HashChain};
//! # use std::fs::File;
//! # use std::io::{self, BufRead, BufReader, BufWriter, Write};
//!
//! # (|| -> std::io::Result<()> {
//! const DEPTH: usize = 6;
//! // Maps each sequence of 6 items to a list of possible next items.
//! // `HashChain` uses hash maps internally; b-trees can also be used.
//! let mut chain = HashChain::new(DEPTH);
//!
//! // In this case, corpus.txt contains one paragraph per line.
//! let file = File::open("examples/corpus.txt")?;
//! let mut reader = BufReader::new(file);
//! let mut line = String::new();
//! // The previous `DEPTH` characters before `line`.
//! let mut prev = Vec::<char>::new();
//!
//! while let Ok(1..) = reader.read_line(&mut line) {
//!     // `Both` means that the generated random output could start with the
//!     // beginning of `line` or end after the end of `line`.
//!     chain.add_all(line.chars(), AddEdges::Both);
//!
//!     // This makes sure there's a chance that the end of the previous line
//!     // could be followed by the start of the current line when generating
//!     // random output.
//!     chain.add_all(
//!         prev.iter().copied().chain(line.chars().take(DEPTH)),
//!         AddEdges::Neither,
//!     );
//!
//!     if let Some((n, (i, _c))) =
//!         line.char_indices().rev().enumerate().take(DEPTH).last()
//!     {
//!         // Keep only the most recent `DEPTH` characters.
//!         prev.drain(0..prev.len().saturating_sub(DEPTH - n - 1));
//!         prev.extend(line[i..].chars());
//!     }
//!     line.clear();
//! }
//!
//! // Generate and print random Markov data.
//! let mut stdout = BufWriter::new(io::stdout().lock());
//! let mut prev_newline = false;
//! for &c in chain.generate() {
//!     if prev_newline {
//!         writeln!(stdout)?;
//!     }
//!     prev_newline = c == '\n';
//!     write!(stdout, "{c}")?;
//! }
//! stdout.flush()?;
//! # Ok(())
//! # })().unwrap();
//! ```
//!
//! Crate features
//! --------------
//!
//! * `std` (default: enabled): Use [`std`]. If disabled, this crate is marked
//!   `no_std`.
//! * `serde` (default: enabled): Implement [Serde]’s [`Serialize`] and
//!   [`Deserialize`] traits for [`Chain`].
//!
//! [Serde]: serde

extern crate alloc;

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use core::borrow::Borrow;
use core::fmt::{self, Debug};
use core::iter::{DoubleEndedIterator, ExactSizeIterator};
use core::mem;
use rand::Rng;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub mod map;
use map::{Map, MapFrom, MapFromSlice, MapOps, MapOpsSlice};
use map::{OwnedSliceKey, SliceKey};

#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound(serialize = "T: Serialize, M: Map<T>")),
    serde(bound(deserialize = "T: Deserialize<'de>, M: Map<T>"))
)]
struct FrequencyMap<T, M: Map<T>> {
    #[cfg_attr(
        feature = "serde",
        serde(serialize_with = "MapOps::serialize"),
        serde(deserialize_with = "MapOps::deserialize")
    )]
    map: <M as MapFrom<T>>::To<usize>,
    total: usize,
}

impl<T: Debug, M: Map<T>> Debug for FrequencyMap<T, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FrequencyMap")
            .field("map", &map::MapDebug::new(&self.map))
            .field("total", &self.total)
            .finish()
    }
}

impl<T: Clone, M: Map<T>> Clone for FrequencyMap<T, M> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
            total: self.total,
        }
    }
}

impl<T, M: Map<T>> Default for FrequencyMap<T, M> {
    fn default() -> Self {
        Self {
            map: Default::default(),
            total: 0,
        }
    }
}

#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound(serialize = "T: Serialize, M: Map<T>")),
    serde(bound(deserialize = "T: Deserialize<'de>, M: Map<T>"))
)]
/// A Markov chain.
///
/// This type implements [`Serialize`] and [`Deserialize`] when the
/// `serde` feature is enabled (which it is by default).
pub struct Chain<T, M: Map<T> = map::BTree> {
    #[cfg_attr(
        feature = "serde",
        serde(serialize_with = "MapOps::serialize"),
        serde(deserialize_with = "MapOps::deserialize")
    )]
    map: <M as MapFromSlice<T>>::To<Box<FrequencyMap<T, M>>>,
    depth: usize,
    #[cfg_attr(feature = "serde", serde(skip))]
    buf: VecDeque<T>,
}

/// Alias of <code>[Chain]<T, [map::BTree]></code>.
pub type BTreeChain<T> = Chain<T, map::BTree>;

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
/// Alias of <code>[Chain]<T, [map::Hash]></code>.
pub type HashChain<T> = Chain<T, map::Hash>;

impl<T, M: Map<T>> Chain<T, M> {
    /// Creates a new chain.
    ///
    /// See [`Self::depth`] for an explanation of the depth.
    pub fn new(depth: usize) -> Self {
        Self {
            map: Default::default(),
            depth,
            buf: Default::default(),
        }
    }

    /// Gets the chain's depth.
    ///
    /// A depth of `n` means the chain maps sequences of `n` items of type `T`
    /// to a list of possible next items.
    pub fn depth(&self) -> usize {
        self.depth
    }

    fn take_buf(&mut self) -> VecDeque<T> {
        let mut buf = mem::take(&mut self.buf);
        buf.clear();
        if buf.capacity() == 0 {
            buf.reserve_exact(self.depth);
        }
        buf
    }

    /// Adds all items in an iterator to the chain.
    ///
    /// This essentially calls [`Self::add`] on every overlapping window
    /// of [`self.depth()`] elements plus the item following each window.
    /// (Smaller windows at the start of the sequence may also be added
    /// depending on the value of `edges`.)
    ///
    /// `edges` controls whether the start or end of `items` may be used as the
    /// start or end of a generated sequence from the chain. See the
    /// documentation for [`AddEdges`] for more information.
    ///
    /// [`self.depth()`]: Self::depth
    pub fn add_all<I>(&mut self, items: I, edges: AddEdges)
    where
        I: IntoIterator<Item = T>,
        T: Clone,
    {
        let mut buf = self.take_buf();
        let mut iter = items.into_iter();
        let mut item_opt = iter.next();
        while let Some(item) = item_opt {
            debug_assert!(buf.len() <= self.depth);
            let next = iter.next();
            if buf.len() == self.depth || edges.has_start() {
                if next.is_some() || edges.has_end() {
                    self.add_with_key(&buf, Some(item.clone()));
                } else {
                    self.add_with_key(&mut buf, Some(item));
                    break;
                }
            }
            if buf.len() == self.depth {
                buf.pop_front();
            }
            buf.push_back(item);
            item_opt = next;
        }
        if !buf.is_empty() && edges.has_end() {
            self.add_with_key(&mut buf, None);
        }
        self.buf = buf;
    }

    /// Adds items to the chain.
    ///
    /// If `items` yields at least [`self.depth()`] items, this increases the
    /// chance that the first [`self.depth()`] items will be followed by `next`
    /// in a generated sequence (additional items in `items` are ignored).
    ///
    /// If `items` yields fewer than [`self.depth()`] items, this method
    /// increases the chance that those items, when they are the only items
    /// that have been generated so far in a sequence (i.e., the start of a
    /// sequence), will be followed by `next`. In the case where `items` yields
    /// no elements, this increases the chance that `item` will be produced as
    /// the first element of a generated sequence.
    ///
    /// If `next` is `None`, this method increases the chance that `items` will
    /// be considered the end of a sequence.
    ///
    /// [`self.depth()`]: Self::depth
    pub fn add<I>(&mut self, items: I, next: Option<T>)
    where
        I: IntoIterator<Item = T>,
    {
        let mut buf = self.take_buf();
        buf.extend(items.into_iter().take(self.depth));
        self.add_with_key(&mut buf, next);
        self.buf = buf;
    }

    fn add_with_key<S>(&mut self, key: S, next: Option<T>)
    where
        S: SliceKey<T> + Into<OwnedSliceKey<T>>,
    {
        debug_assert!(key.get(self.depth()).is_none());
        let freq = self.map.slice_get_or_insert_with(key, Default::default);
        if let Some(v) = next {
            *freq.map.get_or_insert_with(v, Default::default) += 1;
        }
        freq.total += 1;
    }

    #[cfg(feature = "std")]
    #[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
    /// Generates random Markov chain data.
    ///
    /// Returns an iterator that yields the elements by reference. If you want
    /// them by value, simply use [`Iterator::cloned`] (as long as `T` is
    /// [`Clone`]).
    pub fn generate(&self) -> Generator<'_, T, rand::rngs::ThreadRng, M> {
        self.generate_with_rng(rand::thread_rng())
    }

    /// Like [`Self::generate`], but takes a custom random number generator.
    pub fn generate_with_rng<R: Rng>(&self, rng: R) -> Generator<'_, T, R, M> {
        Generator::new(self, rng)
    }

    #[cfg(feature = "std")]
    #[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
    /// Gets a random item that has followed `items` in the added data.
    ///
    /// If `items` yields more than [`self.depth()`] items, only the first
    /// [`self.depth()`] items are considered. If `items` yields fewer than
    /// [`self.depth()`] items (potentially zero), those items are interpreted
    /// as the beginning of a generated sequence.
    ///
    /// [`self.depth()`]: Self::depth
    pub fn get<'a, B>(&'a self, items: &[B]) -> Option<&'a T>
    where
        B: Borrow<T>,
    {
        self.get_with_rng(items, rand::thread_rng())
    }

    /// Like [`Self::get`], but takes a custom random number generator.
    pub fn get_with_rng<'a, B, R>(
        &'a self,
        items: &[B],
        rng: R,
    ) -> Option<&'a T>
    where
        B: Borrow<T>,
        R: Rng,
    {
        self.get_with_key(items, rng)
    }

    fn get_with_key<S, R>(&self, items: S, mut rng: R) -> Option<&T>
    where
        S: SliceKey<T>,
        R: Rng,
    {
        let freq = self.map.slice_get(&items)?;
        let mut n = rng.gen_range(0..freq.total);
        for (item, count) in freq.map.iter() {
            n = if let Some(n) = n.checked_sub(*count) {
                n
            } else {
                return Some(item);
            }
        }
        None
    }
}

impl<T: Debug, M: Map<T>> Debug for Chain<T, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Chain")
            .field("map", &map::MapDebug::new(&self.map))
            .field("depth", &self.depth)
            .field("buf", &self.buf)
            .finish()
    }
}

impl<T: Clone, M: Map<T>> Clone for Chain<T, M> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
            depth: self.depth,
            buf: Default::default(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
/// Controls the behavior of [`Chain::add_all`].
///
/// This enum determines whether the start or end of the provided items can be
/// used as start or end data for the chain (see individual variants'
/// descriptions).
pub enum AddEdges {
    /// Allows any of the first [`Chain::depth`] items of the provided iterator
    /// to be returned by calling [`Chain::get`] with the items preceding it
    /// (of which there are necessarily fewer than [`Chain::depth`], and
    /// potentially none). This also means that [`Chain::generate`] may yield
    /// these items as its initial elements.
    Start,

    /// Allows the last [`Chain::depth`] items of the provided iterator (or
    /// fewer, if it doesn't yield that many) to be considered the end of the
    /// sequence, represented by a return value of [`None`] from
    /// [`Chain::get`].
    End,

    /// Performs the behavior of both [`Self::Start`] and [`Self::End`].
    Both,

    /// Performs the behavior of neither [`Self::Start`] nor [`Self::End`].
    Neither,
}

impl AddEdges {
    fn has_start(&self) -> bool {
        matches!(self, Self::Start | Self::Both)
    }

    fn has_end(&self) -> bool {
        matches!(self, Self::End | Self::Both)
    }
}

/// Iterator returned by [`Chain::generate`].
pub struct Generator<'a, T, R, M: Map<T>> {
    chain: &'a Chain<T, M>,
    rng: R,
    buf: VecDeque<&'a T>,
}

impl<'a, T, R, M: Map<T>> Generator<'a, T, R, M> {
    /// Creates a new random Markov data generator. See [`Chain::generate`].
    pub fn new(chain: &'a Chain<T, M>, rng: R) -> Self {
        let mut buf = VecDeque::new();
        buf.reserve_exact(chain.depth);
        Self {
            chain,
            rng,
            buf,
        }
    }

    /// Gets the generator's state.
    ///
    /// This is a sequence of exactly [`self.chain.depth()`](Chain::depth)
    /// items. [`Self::next`] will pass the state to [`Chain::get`] and then
    /// update the state accordingly by popping the front item and pushing the
    /// result of [`Chain::get`] to the back.
    ///
    /// The initial state is empty.
    #[rustfmt::skip]
    pub fn state(
        &self,
    ) -> impl '_
        + Clone
        + DoubleEndedIterator<Item = &T>
        + ExactSizeIterator
    {
        self.buf.iter().copied()
    }

    /// Sets the generator's state.
    ///
    /// This method sets the generator's state to (up to) the first
    /// [`self.chain.depth()`](Chain::depth) items in `state`.
    ///
    /// See [`Self::state`] for an explanation of how the state is used.
    pub fn set_state<I>(&mut self, state: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.buf.clear();
        let iter = state.into_iter().take(self.chain.depth());
        self.buf.extend(iter);
    }
}

impl<'a, T, R, M> Iterator for Generator<'a, T, R, M>
where
    T: Clone,
    R: Rng,
    M: Map<T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let next = self.chain.get_with_key(&self.buf, &mut self.rng)?;
        debug_assert!(self.buf.len() <= self.chain.depth());
        if self.buf.len() == self.chain.depth() {
            self.buf.pop_front();
        }
        self.buf.push_back(next);
        Some(next)
    }
}
