/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import data.list.basic
import data.nat.prime
import order.order_iso_nat
import set_theory.fincard

/-!
# Counting on ℕ

This file defines ways to get basic properties of a predicate on ℕ, such as "how many numbers
under `k` satisfy the predicate" and "what is the `n`th number that satisifies this predicate".
We define these as two functions, `count` and `nth`, that answer these questions, and prove
the expected theorems about them.

## Main definitions

* `count p n`: The number of naturals `k < n` such that `p k`.
* `nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `nth p n = 0`.

## Main results

* `nat.nth_eq_order_iso_of_nat`: An infinite set of natural numbers is order-isomorphic to the
  natural numbers.

## TODO

There has been some discussion on the subject of whether both of `nth` and
`nat.subtype.order_iso_of_nat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/

-- TODO open a new PR for these three lemmas
lemma list.range_add (a : ℕ) :
  ∀ b, list.range (a + b) = list.range a ++ (list.range b).map (λ x, a + x)
| 0 := by rw [add_zero, list.range_zero, list.map_nil, list.append_nil]
| (b + 1) := by rw [nat.add_succ, list.range_succ, list.range_add b, list.range_succ,
  list.map_append, list.map_singleton, list.append_assoc]

lemma multiset.range_add (a b : ℕ) :
  multiset.range (a + b) = multiset.range a ∪ (multiset.range b).map (λ x, a + x) :=
begin
  rw [multiset.range, list.range_add, ←multiset.coe_add, ←multiset.coe_map],
  refine multiset.add_eq_union_iff_disjoint.2 (λ x hxa hxb, _),
  rw [multiset.mem_coe, list.mem_range] at hxa,
  obtain ⟨c, _, rfl⟩ := multiset.mem_map.1 hxb,
  exact (self_le_add_right _ _).not_lt hxa,
end

lemma finset.range_add (a b : ℕ) :
  finset.range (a + b) = finset.range a ∪ (finset.range b).image (λ x, a + x) :=
begin
  rw [←finset.val_inj, finset.range, finset.union_val,
    finset.image_val_of_inj_on ((add_right_injective a).inj_on _)],
  exact multiset.range_add a b,
end

-- TODO this is in #10702, remove this when that is merged
lemma galois_connection.lt_iff_lt {α β : Type*} [linear_order α] [linear_order β] {l : α → β}
  {u : β → α} (gc : galois_connection l u) {a : α} {b : β} :
  b < l a ↔ u b < a :=
lt_iff_lt_of_le_iff_le (gc a b)

open finset

namespace nat
variable (p : ℕ → Prop)

section count
variable [decidable_pred p]

/-- Count the number of naturals `k < n` satisfying `p k`. -/
def count (n : ℕ) : ℕ := (list.range n).countp p

@[simp] lemma count_zero : count p 0 = 0 :=
by rw [count, list.range_zero, list.countp]

/-- A fintype instance for the set relevant to `nat.count`. Locally an instance in locale `count` -/
def count_set.fintype (n : ℕ) : fintype {i // i < n ∧ p i} :=
begin
  apply fintype.of_finset ((finset.range n).filter p),
  intro x,
  rw [mem_filter, mem_range],
  refl,
end

localized "attribute [instance] count_set.fintype" in count

lemma count_eq_card_filter_range (n : ℕ) : count p n = ((range n).filter p).card :=
by { rw [count, list.countp_eq_length_filter], refl,}

/-- `count p n` can be expressed as the cardinality of `{k // k < n ∧ p k}`. -/
lemma count_eq_card_fintype (n : ℕ) : count p n = fintype.card {k : ℕ // k < n ∧ p k} :=
begin
  rw [count_eq_card_filter_range, ←fintype.card_of_finset],
  congr,
  intro i,
  rw [mem_filter, mem_range],
  refl,
end

lemma count_monotone : monotone (count p) :=
begin
  intros a b h,
  rw [count, list.countp_eq_length_filter, count, list.countp_eq_length_filter],
  exact list.length_le_of_sublist (list.sublist.filter p (list.range_sublist.mpr h)),
end

lemma count_succ (n : ℕ) : count p (n + 1) = count p n + (if p n then 1 else 0) :=
by split_ifs; simp [count, list.range_succ, h]

lemma count_add (a b : ℕ) : count p (a + b) = count p a + count (λ k, p (a + k)) b :=
begin
  rw [count_eq_card_filter_range, count_eq_card_filter_range, count_eq_card_filter_range, range_add,
    filter_union, card_disjoint_union, image_filter,
    card_image_of_injective _ (add_right_injective a)],
  intros x hx,
  simp_rw [inf_eq_inter, mem_inter, mem_filter, mem_image, mem_range] at hx,
  obtain ⟨⟨hx, _⟩, ⟨c, _, rfl⟩, _⟩ := hx,
  exact (self_le_add_right _ _).not_lt hx,
end

lemma count_add' (a b : ℕ) : count p (a + b) = count (λ k, p (k + b)) a + count p b :=
by { rw [add_comm, count_add, add_comm], simp_rw add_comm b, congr' 2 }

lemma count_one : count p 1 = if p 0 then 1 else 0 := by simp [count_succ]

lemma count_succ' (n : ℕ) : count p (n + 1) = count (λ k, p (k + 1)) n + if p 0 then 1 else 0 :=
by rw [count_add', count_one]

variables {p}

lemma count_succ_eq_succ_count_iff {n : ℕ} : count p (n + 1) = count p n + 1 ↔ p n :=
by by_cases h : p n; simp [h, count_succ]

lemma count_succ_eq_count_iff {n : ℕ} : count p (n + 1) = count p n ↔ ¬p n :=
by by_cases h : p n; simp [h, count_succ]

alias count_succ_eq_succ_count_iff ↔ _ count_succ_eq_succ_count
alias count_succ_eq_count_iff ↔ _ count_succ_eq_count

lemma count_le_cardinal (n : ℕ) : (count p n : cardinal) ≤ cardinal.mk (set_of p) :=
begin
  obtain h | h := lt_or_le (cardinal.mk (set_of p)) cardinal.omega,
  { haveI := (cardinal.lt_omega_iff_fintype.mp h).some,
    simp [cardinal.mk_fintype],
    rw count_eq_card_fintype,
    apply fintype.card_le_of_injective,
    swap,
    exact λ ⟨i, _, hi⟩, ⟨i, hi⟩,
    tidy, },
  { exact trans (le_of_lt (cardinal.nat_lt_omega (count p n))) h},
end

variables {p}

lemma lt_of_count_lt_count {a b : ℕ} (h : count p a < count p b) : a < b :=
(count_monotone p).reflect_lt h

end count

end
