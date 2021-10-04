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
  [semi_normed_group X] [semi_normed_group Y] [semi_normed_space R X] [semi_normed_space R Y]
  (f' : X →L[R] Y) :=
∃ (c : R) (hc : c ≠ 0) (li : X →ₗᵢ[R] Y), (f' : X → Y) = c • li

variables {R M N G M' : Type*} [normed_field R]
  [semi_normed_group M] [semi_normed_group N] [semi_normed_group G]
  [semi_normed_space R M] [semi_normed_space R N] [semi_normed_space R G]
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
begin
  rw subsingleton_iff at h,
  have minor : (f' : M → N) = function.const M 0 := by ext x'; rw h x' 0; exact f'.map_zero,
  have key : ∀ (x' : M), ∥(0 : M →ₗ[R] N) x'∥ = ∥x'∥ := λ x',
    by { rw [linear_map.zero_apply, h x' 0], repeat { rw norm_zero }, },
  exact ⟨(1 : R), one_ne_zero, ⟨0, key⟩,
    by { rw pi.smul_def, ext p, rw [one_smul, minor], refl, }⟩,
end

namespace is_conformal_map

lemma comp {f' : M →L[R] N} {g' : N →L[R] G}
  (hg' : is_conformal_map g') (hf' : is_conformal_map f') :
  is_conformal_map (g'.comp f') :=
begin
  rcases hf' with ⟨cf, hcf, lif, hlif⟩,
  rcases hg' with ⟨cg, hcg, lig, hlig⟩,
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, funext (λ x, _)⟩,
  simp only [coe_comp', linear_isometry.coe_comp, hlif, hlig, pi.smul_apply,
             function.comp_app, linear_isometry.map_smul, smul_smul],
end

lemma injective {f' : M' →L[R] N} (h : is_conformal_map f') : function.injective f' :=
let ⟨c, hc, li, hf'⟩ := h in by simp only [hf', pi.smul_def];
  exact (smul_right_injective _ hc).comp li.injective

lemma ne_zero [nontrivial M'] {f' : M' →L[R] N} (hf' : is_conformal_map f') :
  f' ≠ 0 :=
begin
  intros w,
  rcases exists_ne (0 : M') with ⟨a, ha⟩,
  have : f' a = f' 0,
  { simp_rw [w, continuous_linear_map.zero_apply], },
  exact ha (hf'.injective this),
end

end is_conformal_map
