/*
 * Copyright (c) 2021, TU Dresden.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

//! This is a formally verified implementation of a sparse map that uses [Vec] underneath.
//! Entries are retained in sorted order by key to facilitate fast search.

#![feature(min_specialization)]
extern crate creusot_contracts;

use creusot_contracts::{
    logic::{Int, Seq},
    invariant::Invariant,
    Clone, DeepModel, OrdLogic, *,
};

use ::std::cmp::Ordering;

/// A sparse map representation over a totally ordered key type.
pub struct VecMap<K, V>
where
    K: Eq + Ord,
{
    v: Vec<(K, V)>,
}

impl<K, V> VecMap<K, V>
where
    K: Eq + Ord + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    #[logic]
    fn key_seq(self) -> Seq<K::DeepModelTy> {
        key_seq_internal(self.v)
    }
}

impl<K, V> Invariant for VecMap<K, V>
where
    K: Eq + Ord + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        self.key_seq().sorted()
    }
}

impl<K, V> VecMap<K, V>
where
    K: Eq + Ord + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    pub fn new() -> Self {
        Self { v: Vec::new() }
    }

    /// Find an entry with assumption that the key is random access.
    /// Logarithmic complexity.
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        match self.find_k(&key) {
            Ok(index) => Entry::Occupied(OccupiedEntry { map: self, index, key }),
            Err(index) => Entry::Vacant(VacantEntry { map: self, index, key }),
        }
    }

    /// Find the entry matching `key`. Use `key_hint` to accelerate search.
    /// The function will use the provided hint to skip items before it.\
    /// **Note**: This function makes two assumptions about your input:
    /// - `key_hint` is valid, i.e. the underlying key is in the map and since extracting
    ///   the reference, no item has been removed from the map
    /// - `key_hint.key <= key`
    ///
    /// If either of these assumptions is violated, you might obtain an entry which allows
    /// destroying the well-kept order of the items.
    #[requires(self.is_valid_keyref_lg(key_hint))]
    #[requires(key_hint.key.deep_model() <= key.deep_model())]
    pub fn entry_from_ref(&mut self, key_hint: KeyRef<K>, key: K) -> Entry<K, V> {
        debug_assert!(self.is_valid_keyref(&key_hint.as_ref()));
        let KeyRef { min_idx, .. } = key_hint;

        #[invariant(true)]
        for i in min_idx..self.v.len() {
            match self.v[i].0.cmp(&key) {
                Ordering::Equal => {
                    return Entry::Occupied(OccupiedEntry { map: self, index: i, key })
                }
                Ordering::Greater => {
                    assert!(i >= 1); // otherwise min_idx
                    return Entry::Vacant(VacantEntry { map: self, index: i, key });
                }
                _ => {}
            }
        }
        let i = self.v.len();
        Entry::Vacant(VacantEntry { map: self, index: i, key })
    }

    /// Finds entry reference, either directly associated with `min_key_inclusive`, or the entry with the
    /// closest key (in terms of sorting order) greater than `min_key_inclusive`. Returns `None` if
    /// map does not contain entry with key greater or equal to `min_key_inclusive`.
    #[ensures(result == None ==> forall<i: Int> i >= 0 && i < (self.v@).len() ==>
              self.key_seq()[i] < min_key_inclusive.deep_model())]
    #[ensures(forall<mapping: _, i: Int> result == Some(mapping) && i >= 0 && i < mapping.0.min_idx@ ==>
              self.key_seq()[i] < min_key_inclusive.deep_model())]
    #[ensures(forall<mapping: _, i: Int> result == Some(mapping) && i >= mapping.0.min_idx@ && i < (self.v@).len() ==>
              self.key_seq()[i] >= min_key_inclusive.deep_model())]
    #[ensures(forall<mapping: _> result == Some(mapping)  ==>
              (self.v@)[mapping.0.min_idx@].1 == *mapping.1)]
    pub fn find_random_mapping_after(&self, min_key_inclusive: K) -> Option<(KeyRef<&K>, &V)> {
        match self.find_k(&min_key_inclusive) {
            Ok(index) => {
                let (key, value) = &self.v[index];
                Some((KeyRef { key, min_idx: index }, value))
            }
            Err(index) => match self.v.get(index) {
                Some((key, value)) => {
                    assert!(key >= &min_key_inclusive);
                    Some((KeyRef { key, min_idx: index }, value))
                }
                None => None,
            },
        }
    }

    /// Insert `value` for `key` in the map. If `key` is already contained, the function
    /// replaces the previously held value and returns it.
    #[ensures(exists<i: Int> i >= 0 && i < ((^self).v@).len() ==>
              (^self).key_seq()[i] == key.deep_model() && ((^self).v@)[i].1 == value)]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.find_k(&key) {
            Ok(index) => Some(std::mem::replace(&mut self.v[index].1, value)),
            Err(index) => {
                insert_internal(&mut self.v, index, key, value);
                None
            }
        }
    }

    /// Removes the item with `key` and returns its value. If no such item exists,
    /// it does nothing.
    #[ensures(result == None ==>
              !self.key_seq().contains(key.deep_model()) &&
              *self == ^self)]
    #[ensures(forall<v: V> result == Some(v) ==>
              exists<i: Int> i >= 0 && i < (self.v@).len() ==>
              self.key_seq()[i] == key.deep_model() && (self.v@)[i].1 == v &&
              ((^self).v@) == (self.v@).subsequence(0, i).concat(
                  (self.v@).subsequence(i + 1, (self.v@).len())
              ))]
    pub fn remove(&mut self, key: &K) -> Option<V> {
        match self.find_k(key) {
            Ok(index) => Some(self.v.remove(index).1),
            Err(_) => None,
        }
    }

    /// Get the value associated with `key`, if it exists.
    #[ensures(result == None ==> !self.key_seq().contains(key.deep_model()))]
    #[ensures(forall<v: _> result == Some(v) ==>
              exists<i: Int> i >= 0 && i < (self.v@).len() ==>
              self.key_seq()[i] == key.deep_model() && (self.v@)[i].1 == *v)]
    pub fn get(&self, key: &K) -> Option<&V> {
        match self.find_k(key) {
            Ok(index) => Some(&self.v[index].1),
            Err(_) => None,
        }
    }

    /// Checks if `key` is contained in the map.
    #[ensures(result == self.key_seq().contains(key.deep_model()))]
    pub fn contains_key(&self, key: &K) -> bool {
        self.find_k(key).is_ok()
    }

    /// Produces the first mapping that follows the given key
    /// in the ascending order of keys.
    #[ensures(result == None ==>
              forall<i: Int> i >= 0 && i < (self.v@).len() ==>
              self.key_seq()[i] <= key.key.deep_model())]
    #[ensures(forall<entry: _> result == Some(entry) ==>
              exists<i: Int> i >= 0 && i < (self.v@).len() ==>
              self.key_seq()[i] == entry.0.key.deep_model() &&
              self.key_seq()[i] > key.key.deep_model() &&
              (self.v@)[i].1 == *entry.1 &&
              forall<j: Int> j >= 0 && j < i ==>
              self.key_seq()[j] < entry.0.key.deep_model() &&
              self.key_seq()[j] <= key.key.deep_model())]
    pub fn next_mapping(&self, key: KeyRef<&K>) -> Option<(KeyRef<&K>, &V)> {
        let from = if self.is_valid_keyref(&key) {
            key.min_idx
        } else {
            0 // it's not, maybe it was produced by another vecmap
        };

        #[invariant(forall<j: Int> j >= 0 && j < produced.len() + from@ ==>
                    self.key_seq()[j] <= key.key.deep_model())]
        for idx in from..self.v.len() {
            if self.v[idx].0 > *key.key {
                let (key, value) = &self.v[idx];
                return Some((KeyRef { min_idx: idx, key }, value));
            }
        }
        None
    }

    #[ensures(result == self.is_valid_keyref_lg((*key).to_owned()))]
    #[ensures(result ==> key.min_idx@ < (self.v@).len())]
    #[ensures(result ==> forall<i: Int> i >= 0 && i <= key.min_idx@ ==>
              self.key_seq()[i] <= key.key.deep_model())]
    fn is_valid_keyref(&self, key: &KeyRef<&K>) -> bool {
        match self.v.get(key.min_idx) {
            Some((k, _)) => k <= key.key,
            _ => false,
        }
    }

    #[predicate]
    fn is_valid_keyref_lg(self, key: KeyRef<K>) -> bool {
        pearlite! {
            match self.key_seq().get(key.min_idx@) {
                Some(k) => {
                    k <= key.key.deep_model()
                },
                _ => false
            }
        }
    }

    /// Obtain keyref-value pair of the item with the smallest key, unless the map is empty.
    #[ensures(result == None ==> (self.v@).len() == 0)]
    #[ensures(forall<entry: _> result == Some(entry) ==> (self.v@)[0] == ((*entry.0.key, *entry.1)))]
    #[ensures(forall<entry: _> result == Some(entry) ==> entry.0.min_idx@ == 0)]
    #[ensures(forall<entry: _> result == Some(entry) ==>
              forall<i: Int> i >= 0 && i < (self.v@).len() ==> self.key_seq()[i] >= entry.0.key.deep_model()
    )]
    pub fn min_entry(&self) -> Option<(KeyRef<&K>, &V)> {
        match self.v.first() {
            Some((key, value)) => Some((KeyRef { key, min_idx: 0 }, value)),
            None => None,
        }
    }

    /// Obtain the key of the item with the greatest key, unless the map is empty.
    #[ensures(result == None ==> (self.v@).len() == 0)]
    #[ensures(forall<k: &K> result == Some(k) ==>
              forall<i: Int> i >= 0 && i < (self.v@).len() ==>
              self.key_seq()[i] <= k.deep_model()
    )]
    pub fn max_key(&self) -> Option<&K> {
        match self.v.last() {
            Some(e) => Some(&e.0),
            None => None,
        }
    }

    /// Attempts to find the given `key`. If found, it returns `Ok` with the index of the key in the
    /// underlying `Vec`. Otherwise it returns `Err` with the index where a matching element could be
    /// inserted while maintaining sorted order.
    #[ensures(match result {
        Ok(_) => self.key_seq().contains(key.deep_model()),
        Err(_) => !self.key_seq().contains(key.deep_model()),
    })]
    #[ensures(forall<i: usize> result == Ok(i) ==> self.key_seq()[i@] == key.deep_model())]
    #[ensures(forall<i: usize, j: Int> result == Err(i) ==> j >= i@ && j < (self.v@).len() ==>
              self.key_seq()[j] > key.deep_model())]
    #[ensures(forall<i: usize, j: Int> result == Err(i) && j >= 0 && j < i@ ==>
              self.key_seq()[j] < key.deep_model())]
    #[ensures(match result {
        Ok(idx) => idx@ < (self.v@).len(),
        Err(idx) => idx@ <= (self.v@).len(),
    })]
    fn find_k(&self, key: &K) -> Result<usize, usize> {
        let mut size = self.v.len();
        let mut left = 0;
        let mut right = size;
        let mut mid;

        #[invariant(size@ >= 0 && size@ <= (self.v@).len())]
        #[invariant(left@ >= 0 && left@ <= (self.v@).len())]
        #[invariant(right@ >= 0 && right@ <= (self.v@).len())]
        #[invariant(left@ < right@ ==> (left@ + (size@ / 2)) < (self.v@).len())]
        #[invariant(left@ < right@ ==> right@ > (left@ + (size@ / 2)))]
        #[invariant(forall<i: Int> i >= right@ && i < (self.v@).len() ==>
                    self.key_seq()[i] > key.deep_model())]
        #[invariant(forall<i: Int> i >= 0 && i < left@ ==>
                    self.key_seq()[i] < key.deep_model())]
        while left < right {
            mid = left + size / 2;

            let cmp = self.v[mid].0.cmp(key);

            match cmp {
                Ordering::Less => left = mid + 1,
                Ordering::Greater => right = mid,
                Ordering::Equal => return Ok(mid),
            }

            size = right - left;
        }
        Err(left)
    }
}

/// Directly insert into a `Vec`. This does not maintain the sorting of elements
/// by itself.
#[requires(idx@ <= (v@).len())]
#[ensures(((^v)@).len() == (v@).len() + 1)]
#[ensures(forall<i: Int> 0 <= i && i < idx@ ==> ((^v)@)[i] == (v@)[i])]
#[ensures(((^v)@)[idx@] == (key, value))]
#[ensures(forall<i: Int> idx@ < i && i < ((^v)@).len() ==> ((^v)@)[i] == (v@)[i - 1])]
#[ensures(key_seq_internal(*v).sorted() && (v@).len() == 0 ==> key_seq_internal(^v).sorted())]
#[ensures(key_seq_internal(*v).sorted() && (v@).len() > 0 && idx@ > 0 && idx@ < (v@).len() &&
            (v@)[idx@].0.deep_model() > key.deep_model() &&
            (v@)[idx@ - 1].0.deep_model() < key.deep_model() ==>
            key_seq_internal(^v).sorted()
)]
#[ensures(key_seq_internal(*v).sorted() && (v@).len() > 0 && idx@ == 0 &&
            (v@)[idx@].0.deep_model() > key.deep_model() ==>
            key_seq_internal(^v).sorted()
)]
#[ensures(key_seq_internal(*v).sorted() && (v@).len() > 0 && idx@ == (v@).len() &&
            (v@)[idx@ - 1].0.deep_model() < key.deep_model() ==>
            key_seq_internal(^v).sorted()
)]
fn insert_internal<K, V>(v: &mut Vec<(K, V)>, idx: usize, key: K, value: V)
where
    K: Eq + Ord + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    v.insert(idx, (key, value))
}

#[logic]
fn key_seq_internal<K, V>(v: Vec<(K, V)>) -> Seq<K::DeepModelTy>
where
    K: Eq + Ord + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    pearlite! {
        Seq::new((v@).len(), |i| (v@)[i].0.deep_model())
    }
}

impl<K: Clone + Eq + Ord, V: Clone> Clone for VecMap<K, V> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        VecMap { v: self.v.clone() }
    }
}

impl<K: Ord + Eq, V> ::std::default::Default for VecMap<K, V> {
    #[ensures(result.is_default())]
    fn default() -> Self {
        Self { v: Vec::new() }
    }
}

impl<K, V> creusot_contracts::Default for VecMap<K, V>
where
    K: Ord,
{
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { (self.v@).len() == 0 }
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, K, V>
where
    K: Ord + Eq,
{
    /// A vacant Entry
    Vacant(VacantEntry<'a, K, V>),

    /// An occupied Entry
    Occupied(OccupiedEntry<'a, K, V>),
}

/// A vacant Entry.
pub struct VacantEntry<'a, K, V>
where
    K: Ord + Eq,
{
    map: &'a mut VecMap<K, V>,
    key: K,
    index: usize,
}

/// An occupied Entry.
pub struct OccupiedEntry<'a, K, V>
where
    K: Ord + Eq,
{
    map: &'a mut VecMap<K, V>,
    key: K,
    index: usize,
}

impl<K, V> Entry<'_, K, V>
where
    K: Ord + Eq + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    pub fn keyref(&self) -> KeyRef<&K> {
        match self {
            Entry::Vacant(VacantEntry { key, index, .. }) => KeyRef { min_idx: *index, key },
            Entry::Occupied(OccupiedEntry { key, index, .. }) => KeyRef { min_idx: *index, key },
        }
    }
}

#[trusted]
impl<K, V> Resolve for VacantEntry<'_, K, V>
where
    K: Eq + Ord,
{
    #[predicate]
    #[open]
    fn resolve(self) -> bool {
        self.map.resolve() && self.key.resolve()
    }
}

impl<K, V> Invariant for VacantEntry<'_, K, V>
where
    K: Eq + Ord + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            self.index@ <= (self.map.v@).len()
        }
    }
}

impl<K, V> VacantEntry<'_, K, V>
where
    K: Ord + Eq + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    /// Sets the value of the entry with the VacantEntry's key.
    #[requires(forall<i: Int> i >= 0 && i < self.index@ ==>
               self.map.key_seq()[i] < self.key.deep_model())]
    #[requires(forall<i: Int> i >= self.index@ && i < (self.map.v@).len() ==>
               self.map.key_seq()[i] > self.key.deep_model())]
    pub fn insert(self, value: V) {
        insert_internal(&mut self.map.v, self.index, self.key, value);
        proof_assert!(self.invariant());
    }
}

impl<K, V> Invariant for OccupiedEntry<'_, K, V>
where
    K: Eq + Ord + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
                (self.map.v@).len() > self.index@ &&
                self.map.key_seq()[self.index@] == self.key.deep_model()
        }
    }
}

impl<K, V> OccupiedEntry<'_, K, V>
where
    K: Ord + Eq + DeepModel,
    K::DeepModelTy: OrdLogic,
{
    /// Replaces the entry's value with `value`.
    #[ensures(((^self).map.v@)[self.index@].1 == value)]
    pub fn replace(&mut self, value: V) {
        self.map.v[self.index].1 = value;
    }

    /// Gets the mutable ref to the entry's value.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map.v[self.index].1
    }
}

/// A key zipped with its internal index in this map.
/// For some operations, like manually implemented iteration,
/// the index can be used for optimisation.
#[derive(Copy, Clone)]
pub struct KeyRef<K> {
    pub key: K,
    /// This is a lower bound on the actual index of key K,
    /// it doesn't need to be the index (though it usually will be).
    min_idx: usize,
}

impl<K: DeepModel> DeepModel for KeyRef<K> {
    type DeepModelTy = (K::DeepModelTy, Int);

    #[ghost]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! {(self.key.deep_model(), self.min_idx@)}
    }
}

impl<K: Clone> KeyRef<&K> {
    #[inline]
    pub fn cloned(self) -> KeyRef<K> {
        KeyRef { min_idx: self.min_idx, key: self.key.clone() }
    }
}

impl<K: DeepModel> KeyRef<K> {
    #[inline]
    #[ensures(self.deep_model() == result.deep_model())]
    pub fn as_ref(&self) -> KeyRef<&K> {
        KeyRef { min_idx: self.min_idx, key: &self.key }
    }
}

impl<K: DeepModel> KeyRef<&K> {
    #[logic]
    #[ensures(self.deep_model() == result.deep_model())]
    fn to_owned(self) -> KeyRef<K> {
        KeyRef { key: *self.key, min_idx: self.min_idx }
    }
}

impl<K> From<K> for KeyRef<K> {
    fn from(key: K) -> Self {
        Self { key, min_idx: 0 }
    }
}
