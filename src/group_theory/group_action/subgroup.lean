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

open conj_act mul_action
open_locale pointwise

variables {G H : Type*} [group G] [group H]

namespace subgroup
variables {G' : subgroup G} {g : conj_act G} {h : G}

lemma smul_eq_map_conj (g : conj_act G) (H : subgroup G) :
  g • H = H.map (mul_aut.conj g.of_conj_act).to_monoid_hom := rfl

lemma smul_eq_comap_conj (g : conj_act G) (H : subgroup G) :
  g • H = H.comap ((mul_aut.conj g.of_conj_act)⁻¹).to_monoid_hom :=
by simp only [smul_eq_map_conj, map_equiv_eq_comap_symm, mul_aut.inv_def]

@[simp] lemma mem_smul : h ∈ g • G' ↔ g.of_conj_act⁻¹ * h * g.of_conj_act ∈ G' :=
by simp [mem_pointwise_smul_iff_inv_smul_mem, conj_act.smul_def]

lemma smul_eq_self_of_mem (hg : g.of_conj_act ∈ G') : g • G' = G' :=
subgroup.ext $ λ _, by simp [hg, mul_mem_cancel_left, mul_mem_cancel_right]

@[simp] lemma smul_self (x : G') : to_conj_act (x : G) • G' = G' := smul_eq_self_of_mem x.2

section map_comap
variables (f : G →* H)

@[simp] lemma map_smul (g : conj_act G) (K : subgroup G) :
  map f (g • K) = to_conj_act (f g.of_conj_act) • map f K :=
begin
  rw [smul_eq_map_conj, smul_eq_map_conj, map_map, map_map],
  congr,
  ext,
  simp,
end

@[simp] lemma comap_smul (g : conj_act G) (K : subgroup H) :
  comap f (to_conj_act (f g.of_conj_act) • K) = g • comap f K :=
begin
  rw [smul_eq_comap_conj, smul_eq_comap_conj, comap_comap, comap_comap],
  congr,
  ext,
  simp,
end

end map_comap

/-- The stabilizer of a subgroup under the conjugation action is the normalizer. -/
lemma stabilizer_eq_normalizer (H : subgroup G) :
  stabilizer (conj_act G) H = (normalizer H).comap conj_act.of_conj_act.to_monoid_hom :=
begin
  ext x,
  rw [mem_stabilizer_iff, ←eq_inv_smul_iff],
  simp [mem_normalizer_iff, set_like.ext_iff],
end

/-- A subgroup is contained in its own stabilizer under the conjugation action -/
lemma le_stabilizer_self (H : subgroup G) :
  H.comap conj_act.of_conj_act.to_monoid_hom ≤ stabilizer (conj_act G)  H :=
by rw [stabilizer_eq_normalizer]; exact le_normalizer

/-- A subgroup is a fixed point of the conjugation action if and only if it is normal -/
lemma mem_fixed_points_iff_normal (H : subgroup G) :
  H ∈ fixed_points (conj_act G) (subgroup G) ↔ normal H :=
by simp [mem_fixed_points_iff_stabilizer_eq_top,
  stabilizer_eq_normalizer, normal_iff_normalizer_eq_top]

end subgroup
