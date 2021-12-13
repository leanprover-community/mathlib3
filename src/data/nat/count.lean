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

This file defines the `count` function, which gives, for any predicate on the natural numbers,
"how many numbers under `k` satisfy this predicate?".
We then prove several expected lemmas about `count`, relating it to the cardinality of other
objects, and helping to evaluate it for specific `k`.

-/

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
    filter_union, card_disjoint_union, map_filter, add_left_embedding, card_map, function.embedding.coe_fn_mk],
  intros x hx,
  simp_rw [inf_eq_inter, mem_inter, mem_filter, mem_map, mem_range] at hx,
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

end nat
