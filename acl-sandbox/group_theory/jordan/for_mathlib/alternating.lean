/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


import tactic.group
import group_theory.solvable
import group_theory.subgroup.basic
import group_theory.specific_groups.alternating

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
  (h5: 5 ≤ fintype.card α) {g : alternating_group α} :
   is_three_cycle (g : perm α)
   → ∃ (p q : alternating_group α), g = p * q * p⁻¹ * q⁻¹  :=
begin
  intro hg,
     -- g^2 est conjugué de g : g^2 = h g h⁻¹ , donc hg = [h,g]
  let hg2 := hg.is_three_cycle_sq, -- g^2 is a 3-cycle
  rw ← subgroup.coe_mul at hg2,
  obtain ⟨h, hh⟩ := alternating_group.is_three_cycle_is_conj h5 hg hg2,
  -- g^2 is conjugate to g ;  hh :  g^2 * h = h * g
  have : g = h * g * h⁻¹ * g⁻¹ ,
    exact calc g = (g * g * h) * h⁻¹ * g⁻¹ : by group
      ... = (h * g) * h⁻¹ * g⁻¹ : by rw hh.symm
      ... = h * g * h⁻¹ * g⁻¹ : by group ,
  exact ⟨h, g, this⟩,
end

lemma three_cycle_is_commutator'
  (h5: 5 ≤ fintype.card α) {g : perm α} :
   g.is_three_cycle → ∃ (p q : alternating_group α), g = p * q * p⁻¹ * q⁻¹  :=
begin
  intro hg,
  let g_mem : g ∈ alternating_group α := equiv.perm.is_three_cycle.sign hg,
  let γ : alternating_group α := ⟨g, g_mem⟩,
  rw ← set_like.coe_mk g g_mem at hg,
  obtain ⟨p, q, h⟩ := three_cycle_is_commutator h5 hg,
  use p, use q,
  simp only [← subgroup.coe_mul, ← subgroup.coe_inv],
  rw ← h, apply symm,
  exact set_like.coe_mk g g_mem,
end

lemma three_cycle_mem_commutator -- {α : Type*} [decidable_eq α] [fintype α]
  (h5: 5 ≤ fintype.card α) {g : alternating_group α} :
   is_three_cycle (g:perm α)
   → g ∈ commutator (alternating_group α)  :=
begin
  intro hg,
  rw commutator_eq_closure ,
  apply subgroup.subset_closure,
  rw set.mem_set_of_eq,
  obtain ⟨p, q, hpq⟩ := three_cycle_is_commutator h5 hg,
  use ⟨p, q, hpq.symm⟩,
end

end three_cycles

section perfect

variables (α: Type*) [fintype α] [decidable_eq α]
variables {α}

open subgroup equiv equiv.perm

/-- If n ≥ 5, then the alternating group on n letters is perfect -/
theorem alternating_group_is_perfect (h5 : 5 ≤ fintype.card α) : commutator (alternating_group α) = ⊤ :=
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
begin
  apply le_antisymm,
  refine  subgroup.commutator_le_left _ _,
  suffices : closure {b : perm α | (b : perm α).is_three_cycle} = alternating_group α,
  { intros b hb,
    rw ← this at hb,
    apply subgroup.mem_closure.mp hb _ _,
    intros b hb,
    rw set.mem_set_of_eq at hb,
    have hb' : b ∈ alternating_group α := equiv.perm.is_three_cycle.sign hb,
    let β : ↥(alternating_group α) := ⟨b, hb'⟩,
    let hβ_eq : ↑β= b := set_like.coe_mk b hb',
    rw ← hβ_eq  at hb ⊢,
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, hpq⟩ := three_cycle_is_commutator h5 hb,
    rw set_like.mem_coe,
    rw hpq,
    simp only [submonoid.coe_mul, coe_inv, coe_mk],
    rw ← commutator_element_def,
    apply subgroup.commutator_mem_commutator hp hq, },
  rw ← closure_three_cycles_eq_alternating,
end


/-- The commutator subgroup of the permutation group is the alternating group -/
theorem alternating_group.commutator_group_eq (h5 : 5 ≤ fintype.card α) :
  commutator (perm α) = alternating_group α :=
begin
  apply le_antisymm,
  { rw commutator_eq_closure,
    apply (subgroup.closure_le _).mpr,
    intro x,
    -- Ridiculous argument that the commutators belong to the alternating group
    -- This is because sign_inv says sign (f⁻¹) = sign (f).
    rintros ⟨p,q, rfl⟩,
    apply equiv.perm.mem_alternating_group.mpr,
    rw commutator_element_def,
    simp only [sign_mul, sign_inv],
    cases int.units_eq_one_or (sign p) with ha ha;
    { rw ha, norm_num, },
    -- End of ridiculous argument
  },
  rw commutator_def (equiv.perm α),
  let z : (alternating_group α : subgroup (perm α)) ≤ ⊤ := le_top,
  apply le_trans _ (commutator_mono z z),
  rw alternating_group_is_perfect' h5,
  simp only [le_refl] ,
end

end perfect
