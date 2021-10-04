/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.normed_space.linear_isometry

/-!
# Conformal Linear Maps

A continuous linear map between `R`-normed spaces `X` and `Y` `is_conformal_map` if it is
a nonzero multiple of a linear isometry.

## Main definitions

* `is_conformal_map`: the main definition of conformal linear maps

## Main results

* The conformality of the composition of two conformal linear maps, the identity map
  and multiplications by nonzero constants as continuous linear maps
* `is_conformal_map_of_subsingleton`: all continuous linear maps on singleton spaces are conformal
* `is_conformal_map.preserves_angle`: if a continuous linear map is conformal, then it
                                      preserves all angles in the normed space

See `analysis.normed_space.conformal_linear_map.inner_product` for
* `is_conformal_map_iff`: a map between inner product spaces is conformal
  iff it preserves inner products up to a fixed scalar factor.


## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
-/

noncomputable theory

open linear_isometry continuous_linear_map

/-- A continuous linear map `f'` is said to be conformal if it's
    a nonzero multiple of a linear isometry. -/
def is_conformal_map {R : Type*} {X Y : Type*} [normed_field R]
  [semi_normed_group X] [semi_normed_group Y] [normed_space R X] [normed_space R Y]
  (f' : X →L[R] Y) :=
∃ (c : R) (hc : c ≠ 0) (li : X →ₗᵢ[R] Y), f' = c • li.to_continuous_linear_map

variables {R M N G M' : Type*} [normed_field R]
  [semi_normed_group M] [semi_normed_group N] [semi_normed_group G]
  [normed_space R M] [normed_space R N] [normed_space R G]
  [normed_group M'] [normed_space R M']

lemma is_conformal_map_id : is_conformal_map (id R M) :=
⟨1, one_ne_zero, id, by { ext, simp }⟩

lemma is_conformal_map_const_smul {c : R} (hc : c ≠ 0) : is_conformal_map (c • (id R M)) :=
⟨c, hc, id, by { ext, simp }⟩

lemma linear_isometry.is_conformal_map (f' : M →ₗᵢ[R] N) :
  is_conformal_map f'.to_continuous_linear_map :=
⟨1, one_ne_zero, f', by { ext, simp }⟩

lemma is_conformal_map_of_subsingleton [h : subsingleton M] (f' : M →L[R] N) :
  is_conformal_map f' :=
⟨1, one_ne_zero, ⟨0, λ x, by simp [subsingleton.elim x 0]⟩, subsingleton.elim _ _⟩

namespace is_conformal_map

lemma comp {f' : M →L[R] N} {g' : N →L[R] G}
  (hg' : is_conformal_map g') (hf' : is_conformal_map f') :
  is_conformal_map (g'.comp f') :=
begin
  rcases hf' with ⟨cf, hcf, lif, rfl⟩,
  rcases hg' with ⟨cg, hcg, lig, rfl⟩,
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, _⟩,
  ext x,
  simp only [comp_smul, coe_smul', linear_isometry.coe_comp, coe_to_continuous_linear_map,
    coe_comp', (∘), pi.smul_apply, smul_smul, mul_comm]
end

protected lemma injective {f' : M' →L[R] N} (h : is_conformal_map f') : function.injective f' :=
let ⟨c, hc, li, hf'⟩ := h in by simp only [hf', pi.smul_def];
  exact (smul_right_injective _ hc).comp li.injective

lemma ne_zero [nontrivial M'] {f' : M' →L[R] N} (hf' : is_conformal_map f') :
  f' ≠ 0 :=
begin
  rintro rfl,
  rcases exists_ne (0 : M') with ⟨a, ha⟩,
  exact ha (hf'.injective rfl)
end

end is_conformal_map
