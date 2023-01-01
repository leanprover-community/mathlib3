/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import combinatorics.additive.mathlib
import data.nat.prime
import set_theory.cardinal.finite

/-!
# The Cauchy-Davenport theorem

This file proves the Cauchy-Davenport theorem as a corollary to a more general result.

## Main declarations

* `subgroup.nontrivial_size`: The minimum size of a finite nontrivial subgroup of a given group. If
  the group is trivial, it is `1` by convention.
* `finset.card_add_card_sub_one_le_min_nontrivial_size_card_mul`: A generalisation of Károlyi's
  theorem.
* `zmod.card_add_card_sub_one_le_min_card_add_zmod`: The Cauchy-Davenport theorem.

## References

* Matt DeVos, *On a generalization of the Cauchy-Davenport theorem*

## Tags

additive combinatorics, sumset, karolyi, cauchy-davenport, number theory
-/

namespace subgroup
variables (α : Type*) [group α]

@[to_additive] noncomputable def nontrivial_size : ℕ :=
if nat.card α = 1 then 1 else ⨅ s ≠ (⊥ : subgroup α), nat.card s

variables {α} {s : subgroup α}

@[to_additive]
lemma nontrivial_size_le_nat_card (hs : (s : set α).finite) : nontrivial_size α ≤ nat.card s :=
begin
  rw nontrivial_size,
  split_ifs,
  sorry,
  sorry,
end

end subgroup

namespace add_subgroup

@[simp] lemma nontrivial_size_zmod {n : ℕ} (hn : n ≠ 0) : nontrivial_size (zmod n) = n.min_fac :=
sorry

@[simp] lemma nontrivial_size_zmod_prime {p : ℕ} [fact p.prime] : nontrivial_size (zmod p) = p :=
by rw [nontrivial_size_zmod (ne_zero.out : p ≠ 0), (fact.out p.prime).min_fac_eq]

end add_subgroup

open mul_opposite order_dual subgroup
open_locale pointwise

namespace finset
variables {α : Type*} [group α] [decidable_eq α] {s t : finset α}

@[to_additive]
def devos_mul_rel (x y : finset α × finset α) : Prop :=
prod.lex (<) (prod.lex (>) (<)) ((x.1 * x.2).card, x.1.card + x.2.card, x.1.card)
  ((y.1 * y.2).card, y.1.card + y.2.card, y.1.card)

@[to_additive]
lemma well_founded_devos_mul_rel :
  well_founded (devos_mul_rel : finset α × finset α → finset α × finset α → Prop) := sorry

@[to_additive]
instance : is_well_founded (finset α × finset α) devos_mul_rel := sorry

@[to_additive card_add_card_sub_one_le_min_nontrivial_size_card_add]
lemma card_add_card_sub_one_le_min_nontrivial_size_card_mul (hs : s.nonempty) (ht : t.nonempty) :
  min (nontrivial_size α) (s.card + t.card - 1) ≤ (s * t).card :=
begin
  set x := (s, t) with hx,
  clear_value x,
  simp only [prod.ext_iff] at hx,
  obtain ⟨rfl, rfl⟩ := hx,
  revert hs ht,
  refine well_founded_devos_mul_rel.induction x _,
  clear x,
  rintro ⟨s, t⟩ ih hs ht,
  dsimp at *,
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial,
  { simp },
  obtain ⟨g, hg⟩ : ∃ g : α, (op g • s ∩ s).nonempty,
  { refine ⟨b⁻¹ * a, _, mem_inter.2 ⟨mem_smul_finset.2 ⟨_, hb, _⟩, ha⟩⟩,
    simp },
  obtain hgs | hgs := eq_or_ne (g • s) s,
    obtain ⟨S, hS⟩ : ∃ S : subgroup α, (S : set α) ⊆ s := sorry,
  { refine min_le_of_left_le ((nontrivial_size_le_nat_card $ s.finite_to_set.subset hS).trans $
      le_trans _ $ card_le_card_mul_right _ ht),
    sorry },
  sorry,
end

end finset

open finset

namespace zmod
variables {p : ℕ} [fact p.prime] {s t : finset (zmod p)}

/-- The **Cauchy-Davenport theorem**. -/
lemma card_add_card_sub_one_le_min_card_add_zmod (hs : s.nonempty) (ht : t.nonempty) :
  min p (s.card + t.card - 1) ≤ (s + t).card :=
by simpa using card_add_card_sub_one_le_min_nontrivial_size_card_add hs ht

end zmod
