/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import data.finset.basic
import data.finset.powerset
import data.fintype.basic

/-!
# Finsets of finsets of a certain size
-/

namespace finset

variable {α : Type*}
variable {r : ℕ}

/-! ### all_sized -/


/-- `all_sized 𝒜 r` states that every set in 𝒜 has size r. -/
@[reducible]
def all_sized (𝒜 : finset (finset α)) (r : ℕ) : Prop := ∀ A ∈ 𝒜, card A = r

/--
All sets in the union have size `r` iff both sets individually have this
property.
-/
lemma union_layer [decidable_eq α] {A B : finset (finset α)} :
  all_sized (A ∪ B) r ↔ all_sized A r ∧ all_sized B r := finset.forall_mem_union

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


end finset
