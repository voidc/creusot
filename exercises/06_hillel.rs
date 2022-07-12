#![feature(allocator_api)]
#![allow(dead_code)]

extern crate creusot_contracts;
use creusot_contracts::*;

// Implement and prove the following:

// Leftpad. Takes a padding character, a string, and a total length, returns
// the string padded to that length with that character. If length is less
// than the length of the string, does nothing.

#[ensures((@^str).len() >= @len && (@^str).len() >= (@str).len())]
#[ensures((@^str).len() == @len || (@^str).len() == (@str).len())]
#[ensures(@len <= (@str).len() ==> (@^str).len() == (@str).len())]
#[ensures(@len > (@str).len() ==> (@^str).len() == @len)]
#[ensures(forall<i: Int> 0 <= i && i < (@str).len() ==> (@^str)[i] == (@str)[i])]
#[ensures(forall<i: Int> (@str).len() <= i && i < @len ==> (@^str)[i] == pad)]
fn right_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T) {
    let old_str = ghost! { str };

    #[invariant(proph_const, ^str == ^*old_str)]
    #[invariant(old_str_bound, (@old_str).len() <= (@str).len())]
    #[invariant(len_bound, (@old_str).len() < @len ==> (@str).len() <= @len)]
    #[invariant(len_bound, (@str).len() > @len ==> (@str).len() == (@old_str).len())]
    #[invariant(old_elem, forall<i: Int> 0 <= i && i < (@old_str).len() ==> (@str)[i] == (@old_str)[i])]
    #[invariant(pad_elem, forall<i: Int> (@old_str).len() <= i && i < (@str).len() ==> (@str)[i] == pad)]
    while str.len() < len {
        str.push(pad);
    }
}

use std::alloc::Allocator;
extern_spec! {
    mod std {
        mod vec {
            impl<T, A : Allocator> Vec<T, A> {
                #[ensures((@^self).len() == (@self).len() + 1)]
                #[ensures(forall<i: Int> 0 <= i && i < @index ==> (@^self)[i] == (@self)[i])]
                #[ensures((@^self)[@index] == element)]
                #[ensures(forall<i: Int> @index < i && i < (@^self).len() ==> (@^self)[i] == (@self)[i - 1])]
                fn insert(&mut self, index: usize, element: T);
            }
        }
    }
}

#[ensures((@^str).len() >= @len && (@^str).len() >= (@str).len())]
#[ensures((@^str).len() == @len || (@^str).len() == (@str).len())]
#[ensures(forall<i: Int> 0 <= i && i < ((@^str).len() - (@str).len()) ==> (@^str)[i] == pad)]
#[ensures(forall<i: Int> 0 <= i && i < (@str).len() ==> (@^str)[i + ((@^str).len() - (@str).len())] == (@str)[i])]
fn left_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T) {
    let old_str = ghost! { str };
    let mut c: Ghost<usize> = ghost! { 0 };

    #[invariant(proph_const, ^str == ^*old_str)]
    #[invariant(old_str_bound, (@old_str).len() <= (@str).len())]
    #[invariant(len_bound, (@old_str).len() < @len ==> (@str).len() <= @len)]
    #[invariant(len_bound, (@str).len() > @len ==> (@str).len() == (@old_str).len())]
    #[invariant(count, @c == (@str).len() - (@old_str).len())]
    #[invariant(old_elem, forall<i: Int> @c <= i && i < (@str).len() ==> (@str)[i] == (@old_str)[i - @c])]
    #[invariant(pad_elem, forall<i: Int> 0 <= i && i < @c ==> (@str)[i] == pad)]
    while str.len() < len {
        str.insert(0, pad);
        c = ghost! { (1 + c.inner()) };
    }
}

#[predicate]
fn is_unique<T: Eq + Model>(s: Seq<T>) -> bool {
    pearlite! {
        forall<i: Int, j :Int> 0 <= i && i < s.len() && 0 <= j && j < s.len() ==> @(s[i]) == @(s[j]) ==> i == j
    }
}

#[predicate]
fn contains<T: Eq + Model>(seq: Seq<T>, elem: T) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < seq.len() && @(seq[i]) == @elem
    }
}

#[predicate]
fn is_subset<T: Eq + Model>(sub: Seq<T>, sup: Seq<T>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < sub.len() ==> contains(sup, sub[i])
    }
}

#[logic]
#[ensures(is_subset(s, s))]
fn subset_refl<T: Eq + Model>(s: Seq<T>) {}

#[logic]
#[ensures(is_subset(s, s.push(elem)))]
fn subset_push<T: Eq + Model>(s: Seq<T>, elem: T) {}

#[logic]
#[ensures(contains(s, elem) ==> is_subset(s.push(elem), s))]
fn subset_push2<T: Eq + Model>(s: Seq<T>, elem: T) {}

#[logic]
#[ensures(is_subset(sub, sup) && contains(sup, elem) ==> is_subset(sub.push(elem), sup))]
fn subset_push3<T: Eq + Model>(sub: Seq<T>, sup: Seq<T>, elem: T) {}

#[requires(is_unique(@vec))]
#[ensures(is_unique(@^vec))]
#[ensures(is_subset(@vec, @^vec))]
#[ensures(is_subset(@^vec, (@vec).push(elem)))]
#[ensures(contains(@^vec, elem))]
fn insert_unique<T: Eq + Model>(vec: &mut Vec<T>, elem: T) {
    ghost! { pearlite! { subset_push(@vec, elem) } };
    proof_assert! { is_subset(@vec, (@vec).push(elem)) };

    let mut i = 0;

    #[invariant(not_elem, forall<j: Int> 0 <= j && j < @i ==> @((@vec)[j]) != @elem)]
    while i < vec.len() {
        if vec[i] == elem {
            proof_assert! { contains(@vec, elem) };
            return;
        }
        i += 1;
    }

    proof_assert! { is_unique((@vec).push(elem)) };
    vec.push(elem);
}

#[logic]
#[ensures(s.subsequence(0, s.len()).ext_eq(s))]
fn subseq_eq_seq<T: Eq>(s: Seq<T>) {}

// Unique. Takes a sequence of integers, returns the unique elements of that
// list. There is no requirement on the ordering of the returned values.
// Hint: Use a helper function to insert new elements into your unique vector
#[ensures(is_unique(@result))]
#[ensures(is_subset(@result, @str))]
#[ensures(is_subset(@str, @result))]
fn unique<T: Eq + Model + Copy>(str: &[T]) -> Vec<T> {
    let mut unique = Vec::new();
    let mut sub_str: Ghost<Seq<T>> = ghost! { Seq::new() };
    let mut i: usize = 0;

    #[invariant(i_bound, @i <= (@str).len())]
    #[invariant(sub_str, sub_str.ext_eq((@str).subsequence(0, @i)))]
    #[invariant(unique, is_unique(@unique))]
    #[invariant(unique_subset, is_subset(@unique, @str))]
    #[invariant(unique_subset, is_subset(*sub_str, @unique))]
    while i < str.len() {
        let elem: T = str[i];
        insert_unique(&mut unique, elem);
        sub_str = ghost! { sub_str.push(elem) };
        i += 1;
    }

    proof_assert! { is_subset((@str).subsequence(0, (@str).len()), @unique) }
    // use subseq_eq_seq(@str)
    proof_assert! { (@str).subsequence(0, (@str).len()).ext_eq(@str) }
    unique
}

#[logic]
#[ensures(result >= 0)]
fn abs_diff(a: Int, b: Int) -> Int {
    if a < b {
        b - a
    } else {
        a - b
    }
}

extern_spec! {
    mod std {
        mod primitive {
            impl u32 {
                #[ensures(@result == abs_diff(@self, @other))]
                fn abs_diff(self, other: u32) -> u32;
            }
        }
    }
}

#[logic]
#[variant(to - from)]
#[requires(0 <= from && from <= to && to <= seq.len())]
fn sum_range(seq: Seq<u32>, from: Int, to: Int) -> Int {
    if to - from > 0 {
        pearlite! { @(seq[from]) + sum_range(seq, from + 1, to) }
    } else {
        0
    }
}

#[logic]
#[requires(0 <= from && from <= to && to <= seq.len())]
#[ensures(forall<i: Int> from <= i && i <= to ==> sum_range(seq, from, to) == sum_range(seq, from, i) + sum_range(seq, i, to))]
fn sum_range_split(seq: Seq<u32>, from: Int, to: Int) {}

#[logic]
#[requires(0 <= i && i <= to && to <= seq.len())]
#[ensures(0 <= result && result < sum_range(seq, 0 , to))]
fn score_to(seq: Seq<u32>, i: Int, to: Int) -> Int {
    abs_diff(sum_range(seq, 0, i), sum_range(seq, i, to))
}

#[logic]
#[requires(0 <= i && i <= seq.len())]
#[ensures(0 <= result && result < sum_range(seq, 0 , seq.len()))]
fn score(seq: Seq<u32>, i: Int) -> Int {
    score_to(seq, i, seq.len())
}

// Fulcrum. Given a sequence of integers, returns the index i that minimizes
// |sum(seq[..i]) - sum(seq[i..])|. Does this in O(n) time and O(n) memory.
// Hard
#[ensures(0 <= @result && @result < (@s).len())]
#[ensures(forall<i: Int> 0 <= i && i < (@s).len() ==> score(@s, @result) <= score(@s, i))]
fn fulcrum(s: &[u32]) -> usize {
    let mut total: u32 = 0;
    let mut i: usize = 0;
    #[invariant(total, @total == sum_range(@s, 0, @i))]
    while i < s.len() {
        total += s[i];
        i += 1;
    }

    let mut min_i: usize = 0;
    let mut min_dist: u32 = total;

    let mut sum: u32 = 0;
    let mut i: usize = 0;
    #[invariant(sum, @sum == sum_range(@s, 0, @i))]
    #[invariant(min_dist, @min_dist == score_to(@s, @min_i, @i))]
    #[invariant(min_i, forall<j: Int> 0 <= j && j < @i ==> score_to(@s, @min_i, @i) <= score_to(@s, j, @i))]
    while i < s.len() {
        let dist = sum.abs_diff(total - sum);
        if dist < min_dist {
            min_i = i;
            min_dist = dist;
        }

        sum += s[i];
        i += 1;
    }

    min_i
}
