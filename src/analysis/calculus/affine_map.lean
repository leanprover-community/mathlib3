/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed_space.continuous_affine_map
import analysis.calculus.times_cont_diff

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main definitions:

 * `continuous_affine_map.times_cont_diff`: a continuous affine map is smooth

-/

namespace continuous_affine_map

variables {𝕜 V W : Type*} [nondiscrete_normed_field 𝕜]
variables [normed_group V] [normed_space 𝕜 V]
variables [normed_group W] [normed_space 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
protected lemma times_cont_diff {n : with_top ℕ} (f : V →A[𝕜] W) :
  times_cont_diff 𝕜 n f :=
begin
  rw f.decomp,
  apply f.cont_linear.times_cont_diff.add,
  simp only,
  exact times_cont_diff_const,
end

/-- The evaluation map on the space of continuous affine maps is smooth. -/
lemma times_cont_diff_apply {n : with_top ℕ} :
  times_cont_diff 𝕜 n (λ p, p.1 p.2 : (V →A[𝕜] W) × V → W) :=
begin
  let f₁ : W × W → W := function.uncurry (+),
  let f₂ : W × ((V →L[𝕜] W) × V) → W × W := λ p, (p.1, p.2.1 p.2.2),
  let f₃ : (W × (V →L[𝕜] W)) × V → W × ((V →L[𝕜] W) × V) := equiv.prod_assoc W (V →L[𝕜] W) V,
  let f₄ : (V →A[𝕜] W) × V → (W × (V →L[𝕜] W)) × V :=
    prod.map (continuous_affine_map.to_const_prod_continuous_linear_map 𝕜 V W) id,
  have hf₀ : (λ (p : (V →A[𝕜] W) × V), p.1 p.2) = f₁ ∘ f₂ ∘ f₃ ∘ f₄,
  { ext ⟨f, x⟩,
    rw f.decomp,
    simp only [f₁, f₂, f₃, f₄, add_comm (f 0), function.uncurry_apply_pair, function.comp_app,
      to_const_prod_continuous_linear_map_fst, to_const_prod_continuous_linear_map_snd, id.def,
      prod.map_mk, equiv.prod_assoc_apply, pi.add_apply], },
  have hf₁ : times_cont_diff 𝕜 n f₁ := times_cont_diff_add,
  have hf₂ : times_cont_diff 𝕜 n f₂ := times_cont_diff.prod_map times_cont_diff_id
    is_bounded_bilinear_map_apply.times_cont_diff,
  have hf₃ : times_cont_diff 𝕜 n f₃ := times_cont_diff_prod_assoc,
  have hf₄ : times_cont_diff 𝕜 n f₄ := times_cont_diff.prod_map
    (to_const_prod_continuous_linear_map 𝕜 V W).times_cont_diff times_cont_diff_id,
  rw hf₀,
  exact hf₁.comp (hf₂.comp (hf₃.comp hf₄)),
end

end continuous_affine_map
