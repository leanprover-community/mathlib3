/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import combinatorics.composition
import data.nat.parity
import tactic.apply_fun

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/


variables {α : Type*}

open multiset
open_locale big_operators

namespace nat

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext, derive decidable_eq] structure partition (n : ℕ) :=
(parts : multiset ℕ)
(parts_pos : ∀ {i}, i ∈ parts → 0 < i)
(parts_sum : parts.sum = n)

namespace partition

/-- A composition induces a partition (just convert the list to a multiset). -/
def of_composition (n : ℕ) (c : composition n) : partition n :=
{ parts := c.blocks,
  parts_pos := λ i hi, c.blocks_pos hi,
  parts_sum := by rw [multiset.coe_sum, c.blocks_sum] }

lemma of_composition_surj {n : ℕ} : function.surjective (of_composition n) :=
begin
  rintro ⟨b, hb₁, hb₂⟩,
  rcases quotient.exists_rep b with ⟨b, rfl⟩,
  refine ⟨⟨b, λ i hi, hb₁ hi, _⟩, partition.ext _ _ rfl⟩,
  simpa using hb₂
end

/--
Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
-- The argument `n` is kept explicit here since it is useful in tactic mode proofs to generate the
-- proof obligation `l.sum = n`.
def of_sums (n : ℕ) (l : multiset ℕ) (hl : l.sum = n) : partition n :=
{ parts := l.filter (≠ 0),
  parts_pos := λ i hi, nat.pos_of_ne_zero $ by apply of_mem_filter hi,
  parts_sum :=
  begin
    have lt : l.filter (= 0) + l.filter (≠ 0) = l := filter_add_not _ l,
    apply_fun multiset.sum at lt,
    have lz : (l.filter (= 0)).sum = 0,
    { rw multiset.sum_eq_zero_iff,
      simp },
    simpa [lz, hl] using lt,
  end }

/-- A `multiset ℕ` induces a partition on its sum. -/
def of_multiset (l : multiset ℕ) : partition l.sum :=
of_sums _ l rfl

/-- The partition of exactly one part. -/
def indiscrete_partition (n : ℕ) : partition n :=
of_sums n {n} rfl

instance {n : ℕ} : inhabited (partition n) := ⟨indiscrete_partition n⟩

/--
The number of times a positive integer `i` appears in the partition `of_sums n l hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `partition.non_zero` combined with `multiset.count_eq_zero_of_not_mem` gives that
this is `0` instead.)
-/
lemma count_of_sums_of_ne_zero {n : ℕ} {l : multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
  (of_sums n l hl).parts.count i = l.count i :=
count_filter_of_pos hi

lemma count_of_sums_zero {n : ℕ} {l : multiset ℕ} (hl : l.sum = n) :
  (of_sums n l hl).parts.count 0 = 0 :=
count_filter_of_neg (λ h, h rfl)

/--
Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
instance (n : ℕ) : fintype (partition n) :=
fintype.of_surjective (of_composition n) of_composition_surj

/-- The finset of those partitions in which every part is odd. -/
def odds (n : ℕ) : finset (partition n) :=
finset.univ.filter (λ c, ∀ i ∈ c.parts, ¬ even i)

/-- The finset of those partitions in which each part is used at most once. -/
def distincts (n : ℕ) : finset (partition n) :=
finset.univ.filter (λ c, c.parts.nodup)

/-- The finset of those partitions in which every part is odd and used at most once. -/
def odd_distincts (n : ℕ) : finset (partition n) := odds n ∩ distincts n

end partition
end nat
