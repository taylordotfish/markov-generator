/*
 * Copyright (C) 2022 taylor.fish <contact@taylor.fish>
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

#![forbid(unsafe_code)]
#![cfg_attr(not(any(feature = "std", doc)), no_std)]
#![cfg_attr(feature = "doc_cfg", feature(doc_cfg))]

//! A highly customizable Rust library for building [Markov chains] and
//! generating sequences of data from them.
//!
//! [Markov chains]: https://en.wikipedia.org/wiki/Markov_chain
//!
//! [`Chain`] implements [Serde]'s [`Serialize`] and [`Deserialize`] traits, so
//! you can use a chain multiple times without having to regenerate it every
//! time (which can be a lengthy process).
//!
//! Example
//! -------
//!
//! ```rust
//! use markov_generator::{AddEdges, Chain};
//! # use std::fs::File;
//! # use std::io::{BufReader, BufRead};
//! # use std::iter;
//!
//! const DEPTH: usize = 6;
//! // Maps each sequence of 6 items to a list of possible next items.
//! let mut chain = Chain::new(DEPTH);
//!
//! // In this case, corpus.txt contains one paragraph per line.
//! let file = File::open("examples/corpus.txt").unwrap();
//! let mut reader = BufReader::new(file);
//! let mut line = String::new();
//! let mut prev_line = String::new();
//!
//! while let Ok(1..) = reader.read_line(&mut line) {
//!     // `Both` means that the generated random output could start with the
//!     // beginning of `line`, and that the generated output could end after
//!     // the end of `line`.
//!     chain.add_all(line.chars(), AddEdges::Both);
//!
//!     // Starting index of last `DEPTH` chars in `prev_line`.
//!     let prev_tail =
//!         prev_line.char_indices().nth_back(DEPTH - 1).map_or(0, |(i, _)| i);
//!
//!     // This makes sure there's a chance that the end of the previous line
//!     // could be followed by the start of the current line when generating
//!     // random output.
//!     chain.add_all(
//!         prev_line[prev_tail..].chars().chain(line.chars().take(DEPTH)),
//!         AddEdges::Neither,
//!     );
//!
//!     std::mem::swap(&mut line, &mut prev_line);
//!     line.clear();
//! }
//!
//! // Generate and print random Markov data.
//! let output: String = chain
//!     .generate()
//!     .flat_map(|c| iter::repeat(c).take(1 + (*c == '\n') as usize))
//!     .collect();
//! print!("{}", &output[..output.len() - 1]);
//! ```
//!
//! Crate features
//! --------------
//!
//! * `std` (default: enabled): Use [`std`]. If disabled, this crate is marked
//!   `no_std`.
//! * `hash` (default: enabled): Use hash maps internally. If disabled, B-trees
//!   will be used instead. This feature requires `std`.
//! * `serde` (default: enabled): Implement [Serde]'s [`Serialize`] and
//!   [`Deserialize`] traits for [`Chain`].

#![doc = "\n"]
#![cfg_attr(feature = "serde", doc = "[Serde]: serde")]
#![cfg_attr(
    not(feature = "serde"),
    doc = "
[Serde]: https://docs.rs/serde/1.0/serde/
[`Serialize`]: https://docs.rs/serde/1.0/serde/trait.Serialize.html
[`Deserialize`]: https://docs.rs/serde/1.0/serde/trait.Deserialize.html
"
)]

extern crate alloc;

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::iter::{self, DoubleEndedIterator, ExactSizeIterator};
use core::mem;
use rand::Rng;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "hash")]
type Map<K, V> = std::collections::HashMap<K, V>;

#[cfg(not(feature = "hash"))]
type Map<K, V> = alloc::collections::BTreeMap<K, V>;

#[cfg(feature = "hash")]
/// An alias of the traits that `T` must implement for [`Chain<T>`].
///
/// There is no need to implement this trait manually; it has a blanket
/// implementation.
///
/// If the `hash` feature is disabled, this trait will be an alias of [`Ord`]
/// instead of <code>[Eq] + [Hash](std::hash::Hash)</code>.
pub trait Item: Eq + std::hash::Hash {}

#[cfg(not(feature = "hash"))]
/// An alias of the traits that `T` must implement for [`Chain<T>`].
///
/// There is no need to implement this trait manually; it has a blanket
/// implementation.
///
/// If the `hash` feature is enabled, this trait will be an alias of
/// <code>[Eq] + [Hash](std::hash::Hash)</code> instead of [`Ord`].
pub trait Item: Ord {}

#[cfg(feature = "hash")]
impl<T: Eq + std::hash::Hash> Item for T {}

#[cfg(not(feature = "hash"))]
impl<T: Ord> Item for T {}

#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound(serialize = "T: Item + Serialize")),
    serde(bound(deserialize = "T: Item + Deserialize<'de>"))
)]
enum Node<T> {
    Internal(InternalNode<T>),
    Leaf(LeafNode<T>),
}

#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound(serialize = "T: Item + Serialize")),
    serde(bound(deserialize = "T: Item + Deserialize<'de>"))
)]
struct InternalNode<T> {
    map: Map<T, Node<T>>,
    null_next: Option<Box<Node<T>>>,
}

#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound(serialize = "T: Item + Serialize")),
    serde(bound(deserialize = "T: Item + Deserialize<'de>"))
)]
struct LeafNode<T> {
    map: Map<T, usize>,
    total: usize,
}

impl<T> Default for InternalNode<T> {
    fn default() -> Self {
        Self {
            map: Default::default(),
            null_next: None,
        }
    }
}

impl<T> Default for LeafNode<T> {
    fn default() -> Self {
        Self {
            map: Default::default(),
            total: 0,
        }
    }
}

macro_rules! define_chain_struct {
    (
        $(#[$attrs:meta])*
        $vis:vis struct $name:ident<T> $({
            $($extra:tt)*
        })? $(;)?
    ) => {
        #[cfg_attr(
            feature = "serde",
            derive(Deserialize),
            serde(bound(deserialize = "T: Item + Deserialize<'de>")),
        )]
        $(#[$attrs])*
        $vis struct $name<T> {
            root: Node<T>,
            depth: usize,
            $($($extra)*)?
        }
    };
}

define_chain_struct! {
    #[cfg_attr(feature = "serde", serde(rename = "Chain"))]
    struct SerializableChain<T>;
}

define_chain_struct! {
    #[cfg_attr(
        feature = "serde",
        derive(Serialize),
        serde(bound(serialize = "T: Item + Serialize")),
        serde(from = "SerializableChain<T>"),
    )]
    /// A Markov chain.
    ///
    /// This type implements [`Serialize`] and [`Deserialize`] when the
    /// `serde` feature is enabled (which it is by default).
    pub struct Chain<T> {
        #[cfg_attr(feature = "serde", serde(skip))]
        /// Internal buffer used by [`Self::add`].
        buf: VecDeque<Option<T>>,
    }
}

impl<T> From<SerializableChain<T>> for Chain<T> {
    fn from(chain: SerializableChain<T>) -> Self {
        let mut buf = VecDeque::new();
        buf.reserve_exact(chain.depth + 1);
        Self {
            root: chain.root,
            depth: chain.depth,
            buf,
        }
    }
}

impl<T> Chain<T> {
    /// Creates a new chain.
    ///
    /// See [`Self::depth`] for an explanation of the depth.
    pub fn new(depth: usize) -> Self {
        SerializableChain {
            root: if depth == 0 {
                Node::Leaf(LeafNode::default())
            } else {
                Node::Internal(InternalNode::default())
            },
            depth,
        }
        .into()
    }

    /// Gets the chain's depth.
    ///
    /// A depth of `n` means the chain maps sequences of `n` items of type `T`
    /// to a list of possible next items.
    pub fn depth(&self) -> usize {
        self.depth
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
/// Controls the behavior of [`Chain::add_all`].
///
/// This enum determines whether the start or end of the provided items can be
/// used as start or end data for the chain (see individual variants'
/// descriptions).
pub enum AddEdges {
    /// Allows the start (first [`Chain::depth`] items) of the provided
    /// iterator to be returned by a call to [`Chain::get_start`] (or
    /// increases the chance of this happening).
    ///
    /// Specifically, this increases the chance that a sequence of [`None`]s
    /// could be followed by those starting items in the provided iterator.
    Start,

    /// Increases the chance that the last [`Chain::depth`] items of the
    /// provided iterator could be followed by [`None`].
    End,

    /// Performs the behavior of both [`Self::Start`] and [`Self::End`].
    Both,

    /// Performs neither the behavior of [`Self::Start`] nor [`Self::End`].
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

impl<T: Item> Chain<T> {
    /// Adds all items in an iterator to the chain.
    ///
    /// This essentially calls [`Self::add_next`] on every overlapping window
    /// of <code>[self.depth()](Self::depth) + 1</code> elements.
    ///
    /// `edges` controls whether the start or end of `items` can be used as
    /// start or end data for the chain. See the documentation for [`AddEdges`]
    /// for more information.
    pub fn add_all<I>(&mut self, items: I, edges: AddEdges)
    where
        I: IntoIterator<Item = T>,
        T: Clone,
    {
        let mut buf = mem::take(&mut self.buf);
        buf.clear();
        buf.resize(self.depth, None);

        let mut iter = items.into_iter();
        let mut next = iter.next();

        while let Some(item) = next {
            buf.push_back(Some(item));
            next = iter.next();
            if !edges.has_start() && buf[0].is_none() {
                // Do nothing
            } else if edges == AddEdges::Start && next.is_none() {
                self.add_unchecked(buf.drain(..));
            } else {
                self.add_unchecked(buf.iter().cloned());
            }
        }

        if edges.has_end() {
            self.add_unchecked(buf.drain(..));
        }
        self.buf = buf;
    }

    /// Adds items to the chain.
    ///
    /// The first <code>[self.depth()](Self::depth) + 1</code> items are added,
    /// increasing the chance that the first [`self.depth()`](Self::depth)
    /// items will be followed by the remaining item.
    ///
    /// If [`items.into_iter()`](IntoIterator::into_iter) yields fewer than
    /// [`self.depth()`] items, this function is a no-op. If it yields exactly
    /// [`self.depth()`] items, the remaining item is treated as [`None`].
    ///
    /// [`self.depth()`]: Self::depth
    pub fn add<I: IntoIterator<Item = Option<T>>>(&mut self, items: I) {
        let mut buf = mem::take(&mut self.buf);
        buf.clear();
        buf.extend(items.into_iter().take(self.depth + 1));
        if self.buf.len() >= self.depth {
            self.add_unchecked(buf.drain(..));
        }
        self.buf = buf;
    }

    /// Like [`Self::add`], but doesn't check the length of `items`.
    fn add_unchecked<I: IntoIterator<Item = Option<T>>>(&mut self, items: I) {
        let mut iter = items.into_iter();
        let mut node = &mut self.root;

        for (i, item) in iter.by_ref().take(self.depth).enumerate() {
            let internal = if let Node::Internal(internal) = node {
                internal
            } else {
                panic!("expected internal node");
            };

            let make_node = || {
                if i < self.depth - 1 {
                    Node::Internal(InternalNode::default())
                } else {
                    Node::Leaf(LeafNode::default())
                }
            };

            node = if let Some(item) = item {
                internal.map.entry(item).or_insert_with(make_node)
            } else {
                internal.null_next.get_or_insert_with(|| Box::new(make_node()))
            };
        }

        let leaf = if let Node::Leaf(leaf) = node {
            leaf
        } else {
            panic!("expected leaf node");
        };

        if let Some(item) = iter.next().flatten() {
            *leaf.map.entry(item).or_default() += 1;
        }
        leaf.total += 1;
    }

    /// Adds items preceded by various amounts of `None`s so that
    /// [`Self::get_start`] has a chance of returning those items.
    ///
    /// Specifically, this function calls [`Self::add`] with `i` [`None`]s
    /// followed by the items in `items` for every `i` from 1 to
    /// [`self.depth()`] (inclusive). This increases the chance that the
    /// first [`self.depth()`] items of `items` will be returned by
    /// [`Self::get_start`].
    ///
    /// Note that this function does not increase the chance that the first
    /// [`self.depth()`] items of `items` will be followed by the
    /// <code>[self.depth()](Self::depth) + 1</code>st item;
    /// [`Self::add_next`] or [`Self::add`] must be called.
    ///
    /// [`self.depth()`]: Self::depth
    ///
    /// If this function's trait bounds (<code>[I::IntoIter]: [Clone]</code>)
    /// are a problem, you can use [`Self::add_all`] instead if `T` is
    /// [`Clone`]:
    ///
    /// [I::IntoIter]: IntoIterator::IntoIter
    ///
    /// ```
    /// # use markov_generator::{AddEdges, Chain};
    /// # let mut chain = Chain::new(3);
    /// # let items = [1, 2, 3, 4];
    /// chain.add_all(items.into_iter().take(chain.depth()), AddEdges::Start);
    /// ```
    pub fn add_start<I>(&mut self, items: I)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: Clone,
    {
        let iter = items.into_iter().map(Some);
        for i in (2..self.depth).rev() {
            self.add(iter::repeat_with(|| None).take(i).chain(iter.clone()));
        }
        if self.depth > 0 {
            self.add(iter::once(None).chain(iter));
        }
    }

    /// Convenience function that wraps each item in [`Some`] and calls
    /// [`Self::add`].
    ///
    /// Note that this function alone does not increase the chance that
    /// `items` will be returned by [`Self::get_start`]; [`Self::add_start`]
    /// (or manually passing [`None`]-prefixed sequences to [`Self::add`]) must
    /// be used.
    pub fn add_next<I: IntoIterator<Item = T>>(&mut self, items: I) {
        self.add(items.into_iter().map(Some));
    }

    #[cfg(feature = "std")]
    #[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
    /// Generates random Markov chain data.
    ///
    /// Returns an iterator that yields the elements by reference. If you want
    /// them by value, simply use [`Iterator::cloned`] (as long as `T` is
    /// [`Clone`]).
    pub fn generate(&self) -> Generator<'_, T, rand::rngs::ThreadRng> {
        self.generate_with_rng(rand::thread_rng())
    }

    /// Like [`Self::generate`], but takes a custom random number generator.
    pub fn generate_with_rng<R: Rng>(&self, rng: R) -> Generator<'_, T, R> {
        Generator::new(self, rng)
    }

    #[cfg(feature = "std")]
    #[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
    /// Gets a random item that has followed `items` in the added data.
    ///
    /// Only the first [`self.depth()`](Self::depth) items are considered.
    /// A return value of [`None`] either means those items were never followed
    /// by anything in the data passed to [`Self::add`], or that [`None`]
    /// sometimes followed those items and that possibility happened to be
    /// picked by the random number generator.
    ///
    /// Given `iter` as [`items.into_iter()`](IntoIterator::into_iter), if
    /// [`iter.next()`](Iterator::next) returns [`None`], it is treated as if
    /// it returned <code>[Some]\([None])</code>.
    pub fn get<'a, I>(&'a self, items: I) -> Option<&'a T>
    where
        I: IntoIterator<Item = Option<&'a T>>,
    {
        self.get_with_rng(items, rand::thread_rng())
    }

    /// Like [`Self::get`], but takes a custom random number generator.
    pub fn get_with_rng<'a, I, R>(
        &'a self,
        items: I,
        mut rng: R,
    ) -> Option<&'a T>
    where
        I: IntoIterator<Item = Option<&'a T>>,
        R: Rng,
    {
        let mut iter = items.into_iter();
        let mut node = &self.root;

        for _ in 0..self.depth {
            let internal = if let Node::Internal(internal) = node {
                internal
            } else {
                panic!("expected internal node");
            };

            node = if let Some(item) = iter.next().flatten() {
                internal.map.get(item)?
            } else {
                internal.null_next.as_ref()?
            };
        }

        let leaf = if let Node::Leaf(leaf) = node {
            leaf
        } else {
            panic!("expected leaf node");
        };

        if leaf.total == 0 {
            return None;
        }

        let mut n = rng.gen_range(0..leaf.total);
        for (item, count) in &leaf.map {
            n = if let Some(n) = n.checked_sub(*count) {
                n
            } else {
                return Some(item);
            }
        }
        None
    }

    #[cfg(feature = "std")]
    #[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
    /// Gets some initial items that have appeared at the start of a sequence
    /// (see [`Self::add_start`]).
    ///
    /// The returned iterator will yield up to [`self.depth()`](Self::depth)
    /// items.
    pub fn get_start(&self) -> impl Iterator<Item = &T> {
        self.get_start_with_rng(rand::thread_rng())
    }

    /// Like [`Self::get_start`], but takes a custom random number generator.
    pub fn get_start_with_rng<R: Rng>(
        &self,
        mut rng: R,
    ) -> impl Iterator<Item = &T> {
        let mut items = Vec::with_capacity(self.depth);
        for i in (1..=self.depth).rev() {
            if let Some(item) = self.get_with_rng(
                iter::repeat_with(|| None)
                    .take(i)
                    .chain(items.iter().copied().map(Some)),
                &mut rng,
            ) {
                items.push(item);
            } else {
                break;
            }
        }
        items.into_iter()
    }

    #[cfg(feature = "std")]
    #[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
    /// Convenience function that wraps each item in [`Some`] and calls
    /// [`Self::get`].
    pub fn get_next<'a, I>(&'a self, items: I) -> Option<&'a T>
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.get_next_with_rng(items, rand::thread_rng())
    }

    /// Like [`Self::get_next`], but takes a custom random number generator.
    pub fn get_next_with_rng<'a, I, R>(
        &'a self,
        items: I,
        rng: R,
    ) -> Option<&'a T>
    where
        I: IntoIterator<Item = &'a T>,
        R: Rng,
    {
        self.get_with_rng(items.into_iter().map(Some), rng)
    }
}

/// Iterator returned by [`Chain::generate`].
pub struct Generator<'a, T, R> {
    chain: &'a Chain<T>,
    rng: R,
    buf: VecDeque<Option<&'a T>>,
}

impl<'a, T, R> Generator<'a, T, R> {
    /// Creates a new random Markov data generator. See [`Chain::generate`].
    pub fn new(chain: &'a Chain<T>, rng: R) -> Self {
        let mut buf = VecDeque::new();
        buf.resize(chain.depth, None);
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
    /// The initial state consists entirely of [`None`]s.
    #[rustfmt::skip]
    pub fn state(
        &self,
    ) -> impl '_
    + Clone
    + DoubleEndedIterator<Item = Option<&T>>
    + ExactSizeIterator {
        self.buf.iter().copied()
    }

    /// Sets the generator's state.
    ///
    /// This method sets the generator's state to the first
    /// [`self.chain.depth()`](Chain::depth) items in `state`, filling in with
    /// [`None`] if `state` yields fewer items.
    ///
    /// See [`Self::state`] for an explanation of how the state is used.
    pub fn set_state<I>(&mut self, state: I)
    where
        I: IntoIterator<Item = Option<&'a T>>,
    {
        self.buf.clear();
        self.buf.extend(
            state
                .into_iter()
                .chain(iter::repeat(None))
                .take(self.chain.depth()),
        );
    }
}

impl<'a, T: Clone + Item, R: Rng> Iterator for Generator<'a, T, R> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let result =
            self.chain.get_with_rng(self.buf.iter().copied(), &mut self.rng);
        self.buf.pop_front();
        self.buf.push_back(result);
        result
    }
}
