/*
 * Copyright (C) 2024 taylor.fish <contact@taylor.fish>
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

//! Options for customizing the map type used by [`Chain`].
//!
//! The types in this module that implement [`Map`] can be provided as the
//! second type parameter to [`Chain`] in order to change the type of map it
//! uses for internal storage. For example, <code>[Chain]<T, [BTree]></code>
//! will use [`BTreeMap`]s, while <code>[Chain]<T, [Hash]></code> will use
//! [`HashMap`]s.
//!
//! [`Chain`]: crate::Chain
//! [Chain]: crate::Chain
//! [`BTreeMap`]: alloc::collections::BTreeMap
//! [Hash]: self::Hash
//! [`HashMap`]: std::collections::HashMap

use alloc::collections::VecDeque;
use core::borrow::Borrow;
use core::fmt::{self, Debug};

/// Represents a [`BTreeMap`].
///
/// [`Chain`] will use [`BTreeMap`]s internally when this type is provided as
/// its second type parameter.
///
/// [`BTreeMap`]: alloc::collections::BTreeMap
/// [`Chain`]: crate::Chain
pub struct BTree(());

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
/// Represents a [`HashMap`].
///
/// [`Chain`] will use [`HashMap`]s internally when this type is provided as
/// its second type parameter.
///
/// [`HashMap`]: std::collections::HashMap
/// [`Chain`]: crate::Chain
pub struct Hash(());

pub(crate) mod detail {
    use alloc::boxed::Box;
    use core::fmt::{self, Debug};
    #[cfg(feature = "serde")]
    use serde::{Deserialize, Serialize};

    pub trait MapFrom<K> {
        type To<V>: MapOps<K, V>;
    }

    pub trait MapFromSlice<K>: MapFrom<OwnedSliceKey<K>> {
        type To<V>: MapOpsSlice<K, V>;
    }

    pub trait MapOps<K, V>: Default {
        type Iter<'a>: Iterator<Item = (&'a K, &'a V)>
        where
            K: 'a,
            V: 'a,
            Self: 'a;

        type IterMut<'a>: Iterator<Item = (&'a K, &'a mut V)>
        where
            K: 'a,
            V: 'a,
            Self: 'a;

        fn iter(&self) -> Self::Iter<'_>;
        #[allow(dead_code)]
        fn iter_mut(&mut self) -> Self::IterMut<'_>;
        #[allow(dead_code)]
        fn get(&self, k: &K) -> Option<&V>;
        fn get_or_insert_with<F>(&mut self, k: K, v: F) -> &mut V
        where
            F: FnOnce() -> V;

        fn debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
        where
            V: Debug,
            K: Debug;

        fn clone(&self) -> Self
        where
            K: Clone,
            V: Clone;

        #[cfg(feature = "serde")]
        fn serialize<S>(&self, s: S) -> Result<S::Ok, S::Error>
        where
            K: serde::Serialize,
            V: serde::Serialize,
            S: serde::Serializer;

        #[cfg(feature = "serde")]
        fn deserialize<'de, D>(d: D) -> Result<Self, D::Error>
        where
            K: serde::Deserialize<'de>,
            V: serde::Deserialize<'de>,
            D: serde::Deserializer<'de>;
    }

    pub trait MapOpsSlice<K, V>: MapOps<OwnedSliceKey<K>, V> {
        fn slice_get<'a, S>(&'a self, k: &S) -> Option<&'a V>
        where
            S: SliceKey<K>;

        fn slice_get_or_insert_with<S, F>(&mut self, k: S, v: F) -> &mut V
        where
            S: SliceKey<K> + Into<OwnedSliceKey<K>>,
            F: FnOnce() -> V;
    }

    pub trait SliceKey<T> {
        fn get(&self, i: usize) -> Option<&T>;
    }

    #[derive(Clone, Debug)]
    #[cfg_attr(
        feature = "serde",
        derive(Serialize, Deserialize),
        serde(transparent)
    )]
    pub struct OwnedSliceKey<T>(pub Box<[T]>);

    pub trait Map<K>: MapFrom<K> + MapFromSlice<K> {}

    impl<T, K> Map<K> for T where T: MapFrom<K> + MapFromSlice<K> {}

    pub use Map as Sealed;
}

pub(crate) use detail::{MapFrom, MapFromSlice, MapOps, MapOpsSlice};
pub(crate) use detail::{OwnedSliceKey, SliceKey};

#[cfg(feature = "std")]
impl<K: Eq + std::hash::Hash> MapFrom<K> for Hash {
    type To<V> = std::collections::HashMap<K, V>;
}

#[cfg(feature = "std")]
impl<K: Eq + std::hash::Hash> MapFromSlice<K> for Hash {
    type To<V> = std::collections::HashMap<OwnedSliceKey<K>, V>;
}

#[cfg(feature = "std")]
impl<K, V> MapOps<K, V> for std::collections::HashMap<K, V>
where
    K: Eq + std::hash::Hash,
{
    type Iter<'a>
        = std::collections::hash_map::Iter<'a, K, V>
    where
        K: 'a,
        V: 'a;

    type IterMut<'a>
        = std::collections::hash_map::IterMut<'a, K, V>
    where
        K: 'a,
        V: 'a;

    fn iter(&self) -> Self::Iter<'_> {
        self.iter()
    }

    fn iter_mut(&mut self) -> Self::IterMut<'_> {
        self.iter_mut()
    }

    fn get(&self, k: &K) -> Option<&V> {
        self.get(k)
    }

    fn get_or_insert_with<F>(&mut self, k: K, v: F) -> &mut V
    where
        F: FnOnce() -> V,
    {
        self.entry(k).or_insert_with(v)
    }

    fn debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        V: Debug,
        K: Debug,
    {
        Debug::fmt(self, f)
    }

    fn clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        Clone::clone(self)
    }

    #[cfg(feature = "serde")]
    fn serialize<S>(&self, s: S) -> Result<S::Ok, S::Error>
    where
        K: serde::Serialize,
        V: serde::Serialize,
        S: serde::Serializer,
    {
        serde::Serialize::serialize(self, s)
    }

    #[cfg(feature = "serde")]
    fn deserialize<'de, D>(d: D) -> Result<Self, D::Error>
    where
        K: serde::Deserialize<'de>,
        V: serde::Deserialize<'de>,
        D: serde::Deserializer<'de>,
    {
        serde::Deserialize::deserialize(d)
    }
}

#[cfg(feature = "std")]
impl<K, V> MapOpsSlice<K, V> for std::collections::HashMap<OwnedSliceKey<K>, V>
where
    K: Eq + std::hash::Hash,
{
    fn slice_get<'a, S>(&'a self, k: &S) -> Option<&'a V>
    where
        S: SliceKey<K>,
    {
        Self::get::<dyn SliceKey<K> + '_>(self, k)
    }

    fn slice_get_or_insert_with<S, F>(&mut self, k: S, v: F) -> &mut V
    where
        S: SliceKey<K> + Into<OwnedSliceKey<K>>,
        F: FnOnce() -> V,
    {
        if let Some(v) = Self::get_mut::<dyn SliceKey<K> + '_>(self, &k) {
            #[allow(
                unsafe_code,
                /* reason = "workaround for rust issue #51545" */
            )]
            // SAFETY: `v` is borrowed from `m` (and only `m`), so it is sound
            // to return it with the same lifetime as `m`. Due to issues with
            // Rust's borrow checker (#51545, #54663), this requires a lifetime
            // extension, performed here by converting to a pointer and
            // immediately dereferencing.
            return unsafe { core::ptr::NonNull::from(v).as_mut() };
        }
        MapOps::get_or_insert_with(self, k.into(), v)
    }
}

impl<K: Ord> MapFrom<K> for BTree {
    type To<V> = alloc::collections::BTreeMap<K, V>;
}

impl<K: Ord> MapFromSlice<K> for BTree {
    type To<V> = alloc::collections::BTreeMap<OwnedSliceKey<K>, V>;
}

impl<K: Ord, V> MapOps<K, V> for alloc::collections::BTreeMap<K, V> {
    type Iter<'a>
        = alloc::collections::btree_map::Iter<'a, K, V>
    where
        K: 'a,
        V: 'a;

    type IterMut<'a>
        = alloc::collections::btree_map::IterMut<'a, K, V>
    where
        K: 'a,
        V: 'a;

    fn iter(&self) -> Self::Iter<'_> {
        self.iter()
    }

    fn iter_mut(&mut self) -> Self::IterMut<'_> {
        self.iter_mut()
    }

    fn get(&self, k: &K) -> Option<&V> {
        self.get(k)
    }

    fn get_or_insert_with<F>(&mut self, k: K, v: F) -> &mut V
    where
        F: FnOnce() -> V,
    {
        self.entry(k).or_insert_with(v)
    }

    fn debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        V: Debug,
        K: Debug,
    {
        Debug::fmt(self, f)
    }

    fn clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        Clone::clone(self)
    }

    #[cfg(feature = "serde")]
    fn serialize<S>(&self, s: S) -> Result<S::Ok, S::Error>
    where
        K: serde::Serialize,
        V: serde::Serialize,
        S: serde::Serializer,
    {
        serde::Serialize::serialize(self, s)
    }

    #[cfg(feature = "serde")]
    fn deserialize<'de, D>(d: D) -> Result<Self, D::Error>
    where
        K: serde::Deserialize<'de>,
        V: serde::Deserialize<'de>,
        D: serde::Deserializer<'de>,
    {
        serde::Deserialize::deserialize(d)
    }
}

impl<K, V> MapOpsSlice<K, V>
    for alloc::collections::BTreeMap<OwnedSliceKey<K>, V>
where
    K: Ord,
{
    fn slice_get<'a, S>(&'a self, k: &S) -> Option<&'a V>
    where
        S: SliceKey<K>,
    {
        Self::get::<dyn SliceKey<K> + '_>(self, k)
    }

    fn slice_get_or_insert_with<S, F>(&mut self, k: S, v: F) -> &mut V
    where
        S: SliceKey<K> + Into<OwnedSliceKey<K>>,
        F: FnOnce() -> V,
    {
        if let Some(v) = Self::get_mut::<dyn SliceKey<K> + '_>(self, &k) {
            #[allow(
                unsafe_code,
                /* reason = "workaround for rust issue #51545" */
            )]
            // SAFETY: `v` is borrowed from `m` (and only `m`), so it is sound
            // to return it with the same lifetime as `m`. Due to issues with
            // Rust's borrow checker (#51545, #54663), this requires a lifetime
            // extension, performed here by converting to a pointer and
            // immediately dereferencing.
            return unsafe { core::ptr::NonNull::from(v).as_mut() };
        }
        MapOps::get_or_insert_with(self, k.into(), v)
    }
}

pub(crate) struct MapDebug<'a, K, V, T>(
    &'a T,
    core::marker::PhantomData<fn() -> (K, V)>,
);

impl<'a, K, V, T> MapDebug<'a, K, V, T>
where
    T: MapOps<K, V>,
{
    pub fn new(map: &'a T) -> Self {
        Self(map, core::marker::PhantomData)
    }
}

impl<K, V, T> Debug for MapDebug<'_, K, V, T>
where
    K: Debug,
    V: Debug,
    T: MapOps<K, V>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.debug(f)
    }
}

#[cfg(feature = "std")]
impl<T: std::hash::Hash> std::hash::Hash for OwnedSliceKey<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.iter().for_each(|v| v.hash(state));
    }
}

impl<T: Ord> Ord for OwnedSliceKey<T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.iter().cmp(other.0.iter())
    }
}

impl<T: Ord> PartialOrd for OwnedSliceKey<T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: PartialEq> PartialEq for OwnedSliceKey<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().eq(other.0.iter())
    }
}

impl<T: Eq> Eq for OwnedSliceKey<T> {}

fn slice_key_iter<'a, T, S>(key: &'a S) -> impl Iterator<Item = &'a T>
where
    T: 'a,
    S: SliceKey<T> + ?Sized,
{
    (0..).map_while(|i| key.get(i))
}

impl<T, S> SliceKey<T> for &S
where
    S: SliceKey<T> + ?Sized,
{
    fn get(&self, i: usize) -> Option<&T> {
        S::get(*self, i)
    }
}

impl<T, S> SliceKey<T> for &mut S
where
    S: SliceKey<T> + ?Sized,
{
    fn get(&self, i: usize) -> Option<&T> {
        S::get(*self, i)
    }
}

impl<T> SliceKey<T> for OwnedSliceKey<T> {
    fn get(&self, i: usize) -> Option<&T> {
        self.0.get(i)
    }
}

impl<T: Clone> From<&[T]> for OwnedSliceKey<T> {
    fn from(v: &[T]) -> Self {
        Self(Vec::from(v).into_boxed_slice())
    }
}

impl<T, R: Borrow<T>> SliceKey<T> for VecDeque<R> {
    fn get(&self, i: usize) -> Option<&T> {
        self.get(i).map(|r| r.borrow())
    }
}

impl<T: Clone> From<&VecDeque<T>> for OwnedSliceKey<T> {
    fn from(v: &VecDeque<T>) -> Self {
        Self(v.iter().cloned().collect())
    }
}

impl<T> From<&mut VecDeque<T>> for OwnedSliceKey<T> {
    fn from(v: &mut VecDeque<T>) -> Self {
        Self(v.drain(..).collect())
    }
}

impl<T, R: Borrow<T>> SliceKey<T> for [R] {
    fn get(&self, i: usize) -> Option<&T> {
        self.get(i).map(|r| r.borrow())
    }
}

#[cfg(feature = "std")]
impl<T: std::hash::Hash> std::hash::Hash for dyn SliceKey<T> + '_ {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        slice_key_iter(self).for_each(|v| v.hash(state));
    }
}

impl<T: Ord> Ord for dyn SliceKey<T> + '_ {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        slice_key_iter(self).cmp(slice_key_iter(other))
    }
}

impl<T: Ord> PartialOrd for dyn SliceKey<T> + '_ {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: PartialEq> PartialEq for dyn SliceKey<T> + '_ {
    fn eq(&self, other: &Self) -> bool {
        slice_key_iter(self).eq(slice_key_iter(other))
    }
}

impl<T: Eq> Eq for dyn SliceKey<T> + '_ {}

impl<'b, T: 'b> Borrow<dyn SliceKey<T> + 'b> for OwnedSliceKey<T> {
    fn borrow(&self) -> &(dyn SliceKey<T> + 'b) {
        self
    }
}

/// Represents a possible map type for [`Chain`](crate::Chain).
pub trait Map<K>: detail::Sealed<K> {}

#[cfg(feature = "std")]
impl<K: Eq + std::hash::Hash> Map<K> for Hash {}

impl<K: Ord> Map<K> for BTree {}
