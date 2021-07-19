/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.basic
import data.fintype
/--
This file defines the conjugation action of a group on its subgroups
-/

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
  exact ⟨λ h, ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩,
    by rintros ⟨y, hy, rfl⟩; simp [mul_assoc, *]⟩
end

@[simp] lemma mem_smul (g h : G) (H : subgroup G) :
  h ∈ (g • H) ↔ g⁻¹ * h * g ∈ H :=
by simp [smul_eq_comap_conj]

instance decidable_mem_smul (g : G) (H : subgroup G) [decidable_pred (∈ H)] :
  decidable_pred (∈ g • H) :=
λ h, decidable_of_iff _ (mem_smul g h H).symm

#print subgroup.map

@[simp] lemma card_smul [fintype G] (g : G) (H : subgroup G) [decidable_pred (∈ H)] :
  fintype.card (g • H : subgroup G) = fintype.card H :=
fintype.card_congr _

end subgroup
