/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


import tactic.group
import group_theory.solvable
import group_theory.subgroup.basic
import group_theory.specific_groups.alternating
import .commutators

/-!
* `three_cycle_is_commutator`, `three_cycle_mem_commutator` : every 3-cycle
is a commutor of even permutations, resp belongs to the commutator subgroup of the alternating group.
* `alternating_group.is_perfect` : the alternating group is perfect (aka equal to its wn
commutator subgroup).
* `alternating_group.commutator_group_eq` : the commutator subgroup of `perm α` is the alternating group.
-/

-- → group_theory.specific_groups.alternating

variable {β : Type*}

section three_cycles

open equiv function finset
open equiv.perm subgroup

variables (α: Type*) [fintype α] [decidable_eq α]
variables {α}

lemma three_cycle_is_commutator -- {α : Type*} [decidable_eq α] [fintype α]
  (h5: 5 ≤ fintype.card α) {g : alternating_group α} (hg : is_three_cycle (g : perm α)) :
  g ∈ commutator_set (alternating_group α) :=
--  ∃ (p q : alternating_group α), g = p * q * p⁻¹ * q⁻¹  :=
begin
  apply mem_commutator_set_of_is_conj_sq,
  apply alternating_group.is_three_cycle_is_conj h5 hg,
  exact hg.is_three_cycle_sq,
end

lemma three_cycle_is_commutator' (h5: 5 ≤ fintype.card α) {g : perm α}
  (hg : g.is_three_cycle) :
  ∃ (p q : alternating_group α), g = p * q * p⁻¹ * q⁻¹  :=
begin
  let g_mem : g ∈ alternating_group α := equiv.perm.is_three_cycle.sign hg,
  let γ : alternating_group α := ⟨g, g_mem⟩,
  rw ← set_like.coe_mk g g_mem at hg,
  obtain ⟨p, q, h⟩ := three_cycle_is_commutator h5 hg,
  use p, use q,
  simp only [← subgroup.coe_mul, ← subgroup.coe_inv, ← commutator_element_def, h, coe_mk],
end

lemma three_cycle_mem_commutator -- {α : Type*} [decidable_eq α] [fintype α]
  (h5: 5 ≤ fintype.card α) {g : alternating_group α} (hg : is_three_cycle (g:perm α)) :
  g ∈ commutator (alternating_group α)  :=
begin
  rw commutator_eq_closure ,
  apply subgroup.subset_closure,
  exact three_cycle_is_commutator h5 hg,
end

end three_cycles

section perfect

variables (α: Type*) [fintype α] [decidable_eq α]
variables {α}

open subgroup equiv equiv.perm

/-- If n ≥ 5, then the alternating group on n letters is perfect -/
theorem alternating_group_is_perfect (h5 : 5 ≤ fintype.card α) :
  commutator (alternating_group α) = ⊤ :=
begin
  suffices : closure {b : alternating_group α | (b : perm α).is_three_cycle} = ⊤,
  { rw [eq_top_iff, ← this, subgroup.closure_le],
    intros b hb,
    exact three_cycle_mem_commutator h5 hb, },
  rw ← closure_three_cycles_eq_alternating,
  apply subgroup.closure_closure_coe_preimage
end

theorem alternating_group_is_perfect' (h5 : 5 ≤ fintype.card α) :
  ⁅alternating_group α, alternating_group α⁆ = alternating_group α :=
by rw [← subgroup.commutator_eq', alternating_group_is_perfect h5,
  subgroup.map_top_eq_range, subgroup.subtype_range]

lemma alternating_group.commutator_group_le :
  commutator (perm α) ≤ alternating_group α :=
begin
  rw [commutator_eq_closure, subgroup.closure_le],
  intro x,
  rintros ⟨p,q, rfl⟩,
  simp only [set_like.mem_coe, mem_alternating_group, map_commutator_element, commutator_element_eq_one_iff_commute],
  apply commute.all,
end

/-- The commutator subgroup of the permutation group is the alternating group -/
theorem alternating_group.commutator_group_eq (h5 : 5 ≤ fintype.card α) :
  commutator (perm α) = alternating_group α :=
begin
  apply le_antisymm alternating_group.commutator_group_le,
  --  rw commutator_def (equiv.perm α),
  have : (alternating_group α : subgroup (perm α)) ≤ ⊤ := le_top,
  apply le_trans _ (commutator_mono this this),
  simp only [alternating_group_is_perfect' h5, le_refl],
end

end perfect
