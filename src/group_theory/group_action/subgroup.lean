/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.subgroup.pointwise

/-!
# Conjugation action on subgroups

This file defines the conjugation action of a group on its subgroups.
-/

open mul_action
open_locale pointwise

variables {G : Type*} [group G]

/-- The conjugation action of `G` on the subgroups of `G` -/
instance subgroup.mul_action' : mul_action G (subgroup G) := mul_action.comp_hom _ mul_aut.conj

namespace subgroup
variables {G' : subgroup G} {g h : G}

lemma smul_eq_map_conj (g : G) (H : subgroup G) :
  g • H = H.map (mul_aut.conj g).to_monoid_hom := rfl

lemma smul_eq_comap_conj (g : G) (H : subgroup G) :
  g • H = H.comap ((mul_aut.conj g)⁻¹).to_monoid_hom :=
by simp only [smul_eq_map_conj, map_equiv_eq_comap_symm, mul_aut.inv_def]

@[simp] lemma mem_smul : h ∈ g • G' ↔ g⁻¹ * h * g ∈ G' :=
by simp only [smul_eq_comap_conj, mul_equiv.coe_to_monoid_hom, mul_aut.conj_inv_apply, mem_comap]

instance decidable_mem_smul (g : G) (H : subgroup G) [decidable_pred (∈ H)] :
  decidable_pred (∈ g • H) :=
λ h, decidable_of_iff' _ mem_smul

@[simp] lemma card_smul [fintype G] (g : G) (H : subgroup G)
  [decidable_pred (∈ H)] {h : fintype ↥(g • H : subgroup G)} :
  fintype.card (g • H : subgroup G) = fintype.card H :=
fintype.card_congr (equiv_smul _ _).to_equiv.symm

lemma smul_eq_self_of_mem (hg : g ∈ G') : g • G' = G' :=
subgroup.ext $ λ _, by simp [*, mul_mem_cancel_left, mul_mem_cancel_right] at *

@[simp] lemma smul_self (x : G') : x • G' = G' := smul_eq_self_of_mem x.2

lemma smul_le_iff_le_smul {H K : subgroup G} : g • H ≤ K ↔ H ≤ g⁻¹ • K :=
by rw [smul_eq_map_conj, map_le_iff_le_comap, smul_eq_comap_conj, monoid_hom.map_inv, inv_inv]

section map_comap
variables {H : Type*} [group H] (f : G →* H)

@[simp] lemma map_smul (g : G) (K : subgroup G) : map f (g • K) = f g • map f K :=
begin
  rw [smul_eq_map_conj, smul_eq_map_conj, map_map, map_map],
  congr,
  ext,
  simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, monoid_hom.map_mul, eq_self_iff_true,
    function.comp_app, monoid_hom.map_mul_inv, monoid_hom.coe_comp, mul_left_inj]
end

@[simp] lemma comap_smul (g : G) (K : subgroup H) : comap f (f g • K) = g • comap f K :=
begin
  rw [smul_eq_comap_conj, smul_eq_comap_conj, comap_comap, comap_comap],
  congr,
  ext,
  simp only [mul_equiv.coe_to_monoid_hom, monoid_hom.map_mul, function.comp_app,
    mul_aut.conj_inv_apply, monoid_hom.map_inv, monoid_hom.coe_comp]
end

end map_comap

/-- The stabilizer of a subgroup under the conjugation action is the normalizer. -/
lemma stabilizer_eq_normalizer (H : subgroup G) : stabilizer G H = normalizer H :=
begin
  ext x,
  rw [mem_stabilizer_iff, mem_normalizer_iff, ← smul_left_cancel_iff (x⁻¹),
    inv_smul_smul, set_like.ext_iff],
  simp only [inv_inv, mem_smul]
end

/-- A subgroup is contained in its own stabilizer under the conjugation action -/
lemma le_stabilizer_self (H : subgroup G) : H ≤ stabilizer G H :=
by rw [stabilizer_eq_normalizer]; exact le_normalizer

/-- A subgroup is a fixed point of the conjugation action if and only if it is normal -/
lemma mem_fixed_points_iff_normal (H : subgroup G) :
  H ∈ fixed_points G (subgroup G) ↔ normal H :=
by simp only [mem_fixed_points_iff_stabilizer_eq_top,
  stabilizer_eq_normalizer, normal_iff_normalizer_eq_top]

/-- The normalizer of the conjugate of a subgroup is the conjugate of the normalizer -/
@[simp] lemma normalizer_smul (g : G) (H : subgroup G) :
  normalizer (g • H) = g • normalizer H :=
by rw [smul_eq_map_conj, smul_eq_map_conj, map_equiv_normalizer_eq]

end subgroup
