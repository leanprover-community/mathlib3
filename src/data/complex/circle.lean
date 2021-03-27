/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.instances.sphere

/-!
# The circle

This file defines `circle` to be the metric sphere (`metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group
* a charted space with model space `euclidean_space ℝ (fin 1)` (inherited from `metric.sphere`)
* a Lie group with model space `𝓡 1`

We furthermore define `exp_map_circle` to be the natural map `λ t, exp (t * I)` from `ℝ` to
`circle`, and show that this map is a group homomorphism and is smooth.

## Implementation notes

To borrow the smooth manifold structure cleanly, the circle needs to be defined using
`metric.sphere`, and therefore the underlying set is `{z : ℂ | abs (z - 0) = 1}`.  This prevents
certain algebraic facts from working definitionally -- for example, the circle is not defeq to
`{z : ℂ | abs z = 1}`, which is the kernel of `complex.abs` considered as a homomorphism from `ℂ`
to `ℝ`, nor is it defeq to `{z : ℂ | norm_sq z = 1}`, which is the kernel of the homomorphism
`complex.norm_sq` from `ℂ` to `ℝ`.

-/

noncomputable theory

open complex finite_dimensional metric
open_locale manifold

/-- Identity involving the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
def findim_real_complex_fact : fact (findim ℝ ℂ = 1 + 1) := ⟨by simp⟩

local attribute [instance] findim_real_complex_fact

/-- The unit circle in `ℂ`, here given the structure of a submonoid of `ℂ`. -/
def circle : submonoid ℂ :=
{ carrier := sphere (0:ℂ) 1,
  one_mem' := by simp,
  mul_mem' := λ a b, begin
    simp only [norm_eq_abs, mem_sphere_zero_iff_norm],
    intros ha hb,
    simp [ha, hb],
  end }

@[simp] lemma mem_circle_iff_abs (z : ℂ) : z ∈ circle ↔ abs z = 1 := mem_sphere_zero_iff_norm

lemma circle_def : ↑circle = {z : ℂ | abs z = 1} := by { ext, simp }

@[simp] lemma abs_eq_of_mem_circle (z : circle) : abs z = 1 := by { convert z.2, simp }

instance : group circle :=
{ inv := λ z, ⟨conj z, by simp⟩,
  div := λ z, λ w, z * ⟨conj w, by simp⟩,
  div_eq_mul_inv := by simp,
  mul_left_inv := λ z, subtype.ext $ by { simp [has_inv.inv, ← norm_sq_eq_conj_mul_self,
    ← mul_self_abs] },
  .. circle.to_monoid }

-- the following result could instead be deduced from the Lie group structure on the circle using
-- `topological_group_of_lie_group`, but that seems a little awkward since one has to first provide
-- and then forget the model space
instance : topological_group circle :=
{ continuous_mul := let h : continuous (λ x : circle, (x : ℂ)) := continuous_subtype_coe in
    continuous_induced_rng (continuous_mul.comp (h.prod_map h)),
  continuous_inv := continuous_induced_rng $
    complex.conj_clm.continuous.comp continuous_subtype_coe }

/-- The unit circle in `ℂ` is a charted space modelled on `euclidean_space ℝ (fin 1)`.  This
follows by definition from the corresponding result for `metric.sphere`. -/
instance: charted_space (euclidean_space ℝ (fin 1)) circle := metric.sphere.charted_space

/-- The unit circle in `ℂ` is a Lie group. -/
instance : lie_group (𝓡 1) circle :=
{ smooth_mul := begin
    let c : circle → ℂ := coe,
    have h₁ : times_cont_mdiff _ _ _ (prod.map c c) :=
      times_cont_mdiff_coe_sphere.prod_map times_cont_mdiff_coe_sphere,
    have h₂ : times_cont_mdiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ (λ (z : ℂ × ℂ), z.fst * z.snd),
    { rw times_cont_mdiff_iff,
      exact ⟨continuous_mul, λ x y, (times_cont_diff_mul.restrict_scalars ℝ).times_cont_diff_on⟩ },
    convert (h₂.comp h₁).cod_restrict_sphere _,
    convert smooth_manifold_with_corners.prod circle circle,
    { exact metric.sphere.smooth_manifold_with_corners },
    { exact metric.sphere.smooth_manifold_with_corners }
  end,
  smooth_inv := (complex.conj_clm.times_cont_diff.times_cont_mdiff.comp
    times_cont_mdiff_coe_sphere).cod_restrict_sphere _,
  .. metric.sphere.smooth_manifold_with_corners }

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def exp_map_circle (t : ℝ) : circle :=
⟨exp (t * I), by simp [exp_mul_I, abs_cos_add_sin_mul_I]⟩

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`, considered as a homomorphism of
groups. -/
def exp_map_circle_hom : ℝ →+ (additive circle) :=
{ to_fun := exp_map_circle,
  map_zero' := by { rw exp_map_circle, convert of_mul_one, simp },
  map_add' := λ x y, show exp_map_circle (x + y) = (exp_map_circle x) * (exp_map_circle y),
    from subtype.ext $ by simp [exp_map_circle, exp_add, add_mul] }

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ` is smooth. -/
lemma times_cont_mdiff_exp_map_circle : times_cont_mdiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ exp_map_circle :=
(((times_cont_diff_exp.restrict_scalars ℝ).comp
  (times_cont_diff_id.smul times_cont_diff_const)).times_cont_mdiff).cod_restrict_sphere _
