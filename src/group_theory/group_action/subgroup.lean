/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.basic
import data.fintype.basic
/-!
This file defines the conjugation action of a group on its subgroups
-/

open mul_action

variables {G : Type*} [group G]

instance subgroup.mul_action' : mul_action G (subgroup G) :=
{ smul := λ g H, H.map (mul_aut.conj g).to_monoid_hom,
  one_smul := λ _, by ext; simp,
  mul_smul := λ _ _ _, by ext; simp }

namespace subgroup

lemma smul_eq_map_conj (g : G) (H : subgroup G) :
  g • H = H.map (mul_aut.conj g).to_monoid_hom := rfl

lemma smul_eq_comap_conj (g : G) (H : subgroup G) :
  g • H = H.comap (mul_aut.conj g⁻¹).to_monoid_hom :=
begin
  ext,
  simp only [smul_eq_map_conj, subgroup.mem_comap, subgroup.mem_map, exists_prop, mul_equiv.coe_to_monoid_hom,
    mul_aut.conj_apply, mul_aut.conj_inv_apply, monoid_hom.map_inv],
  exact ⟨by rintros ⟨y, hy, rfl⟩; simp [mul_assoc, *],
    λ h, ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩⟩
end

@[simp] lemma mem_smul (g h : G) (H : subgroup G) :
  h ∈ (g • H) ↔ g⁻¹ * h * g ∈ H :=
by simp [smul_eq_comap_conj]

instance decidable_mem_smul (g : G) (H : subgroup G) [decidable_pred (∈ H)] :
  decidable_pred (∈ g • H) :=
λ h, decidable_of_iff _ (mem_smul g h H).symm

/-- A subgroup is isomorphic to its conjugates -/
noncomputable def equiv_smul [fintype G] (g : G) (H : subgroup G) : H ≃* (g • H : subgroup G) :=
H.equiv_map_of_injective (mul_aut.conj g).to_monoid_hom (mul_aut.conj g).injective

@[simp] lemma card_smul [fintype G] (g : G) (H : subgroup G)
  [decidable_pred (∈ H)] {h : fintype ↥(g • H : subgroup G)} :
  fintype.card (g • H : subgroup G) = fintype.card H :=
fintype.card_congr (equiv_smul _ _).to_equiv.symm

/-- The stabilizer of a subgroup under the conjugation action is the normalizer. -/
lemma stabilizer_eq_normalizer (H : subgroup G) :
  stabilizer G H = normalizer H :=
subgroup.ext $ λ x,
  begin
    rw [mem_stabilizer_iff, mem_normalizer_iff, ← smul_left_cancel_iff (x⁻¹),
      inv_smul_smul, set_like.ext_iff],
    simp
  end

/-- A subgroup is contained in its own stabilizer under the conjugation action -/
lemma le_stabilizer_self (H : subgroup G) : H ≤ stabilizer G H :=
by rw [stabilizer_eq_normalizer]; exact le_normalizer

/-- A subgroup is a fixed point of the conjugation action iff it is normal -/
lemma mem_fixed_points_iff_normal (H : subgroup G) :
  H ∈ fixed_points G (subgroup G) ↔ normal H :=
by simp only [mem_fixed_points_iff_stabilizer_eq_top,
  stabilizer_eq_normalizer, normal_iff_normalizer_eq_top]

end subgroup
