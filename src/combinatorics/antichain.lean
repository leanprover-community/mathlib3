/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import data.finset
import data.fintype.basic

/-!
# Antichains

Investigating the structure of the lattice of subsets of a finite set
Basic definitions for finite sets which are useful for combinatorics.
We define antichains, and a proposition asserting that a set is a set of r-sets.

## Main definitions

* `antichain` is a family of sets where no set is a subset of another.
* `all_sized` is a proposition that

-/

open finset

variable {α : Type*}
variable {r : ℕ}

/--
A family of sets is an antichain if no set is a subset of another. For example,
`{{1}, {4,6,7}, {2,4,5,6}}` is an antichain.
-/
def antichain (𝒜 : finset (finset α)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ¬(A ⊆ B)

/-- `all_sized 𝒜 r` states that every set in 𝒜 has size r. -/
@[reducible]
def all_sized (𝒜 : finset (finset α)) (r : ℕ) : Prop := ∀ A ∈ 𝒜, card A = r

lemma antichain_of_all_sized {𝒜 : finset (finset α)} {r : ℕ} (a : all_sized 𝒜 r) :
  antichain 𝒜 :=
begin
  intros A h1 B h2 h3,
  have h4 : card A = card B,
  { rw a A h1,
    rw a B h2},
  contrapose! h3,
  convert eq_of_subset_of_card_le h3 _,
  rw h4,
end

/--
All sets in the union have size `r` iff both sets individually have this
property.
-/
lemma union_layer [decidable_eq α] {A B : finset (finset α)} :
  all_sized A r ∧ all_sized B r ↔ all_sized (A ∪ B) r :=
begin
  split; intros p,
  { rw all_sized,
    intros,
    rw mem_union at H,
    exact H.elim (p.1 _) (p.2 _) },
  { split,
    all_goals {rw all_sized, intros, apply p, rw mem_union, tauto} },
end


lemma mem_powerset_len_iff_card [fintype α] {r : ℕ} : ∀ (x : finset α),
  x ∈ powerset_len r (fintype.elems α) ↔ card x = r :=
by intro x; rw mem_powerset_len; exact and_iff_right (subset_univ _)

lemma powerset_len_iff_all_sized [fintype α] {𝒜 : finset (finset α)} :
  all_sized 𝒜 r ↔ 𝒜 ⊆ powerset_len r (fintype.elems α) :=
by rw all_sized; apply forall_congr _; intro A; rw mem_powerset_len_iff_card

lemma card_le_of_all_sized [fintype α] {𝒜 : finset (finset α)} (h : all_sized 𝒜 r) :
  card 𝒜 ≤ nat.choose (fintype.card α) r :=
begin
  rw [fintype.card, ← card_powerset_len],
  apply card_le_of_subset,
  rwa [univ, ← powerset_len_iff_all_sized]
end
