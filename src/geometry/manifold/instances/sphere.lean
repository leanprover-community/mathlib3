/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.complex.circle
import analysis.normed_space.ball_action
import analysis.inner_product_space.calculus
import analysis.inner_product_space.pi_L2
import geometry.manifold.algebra.lie_group
import geometry.manifold.instances.real

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put a smooth manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, a local homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal complement of
`v`).

For finite-dimensional `E`, we then construct a smooth manifold instance on the sphere; the charts
here are obtained by composing the local homeomorphisms `stereographic` with arbitrary isometries
from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about smooth maps:
* `cont_mdiff_coe_sphere` states that the coercion map from the sphere into `E` is smooth;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `cont_mdiff.cod_restrict_sphere` states that a map from a manifold into the sphere is
  smooth if its lift to a map to `E` is smooth; this is a useful tool for constructing smooth maps
  *to* the sphere.

As an application we prove `cont_mdiff_neg_sphere`, that the antipodal map is smooth.

Finally, we equip the `circle` (defined in `analysis.complex.circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `euclidean_space ℝ (fin 1)` (inherited from `metric.sphere`)
* a Lie group with model with corners `𝓡 1`

We furthermore show that `exp_map_circle` (defined in `analysis.complex.circle` to be the natural
map `λ t, exp (t * I)` from `ℝ` to `circle`) is smooth.


## Implementation notes

The model space for the charted space instance is `euclidean_space ℝ (fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[fact (finrank ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `euclidean_space ℝ (fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `euclidean_space ℝ (fin (2 - 1))` but not with model space
`euclidean_space ℝ (fin 1)`.
-/

variables {E : Type*} [inner_product_space ℝ E]

noncomputable theory

open metric finite_dimensional function
open_locale manifold

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

section stereographic_projection
variables (v : E)

/-! ### Construction of the stereographic projection -/

/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the affine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere to the stereographic
projection. -/
def stereo_to_fun [complete_space E] (x : E) : (ℝ ∙ v)ᗮ :=
(2 / ((1:ℝ) - innerSL v x)) • orthogonal_projection (ℝ ∙ v)ᗮ x

variables {v}

@[simp] lemma stereo_to_fun_apply [complete_space E] (x : E) :
  stereo_to_fun v x = (2 / ((1:ℝ) - innerSL v x)) • orthogonal_projection (ℝ ∙ v)ᗮ x :=
rfl

lemma cont_diff_on_stereo_to_fun [complete_space E] :
  cont_diff_on ℝ ⊤ (stereo_to_fun v) {x : E | innerSL v x ≠ (1:ℝ)} :=
begin
  refine cont_diff_on.smul _
    (orthogonal_projection ((ℝ ∙ v)ᗮ)).cont_diff.cont_diff_on,
  refine cont_diff_const.cont_diff_on.div _ _,
  { exact (cont_diff_const.sub (innerSL v : E →L[ℝ] ℝ).cont_diff).cont_diff_on },
  { intros x h h',
    exact h (sub_eq_zero.mp h').symm }
end

lemma continuous_on_stereo_to_fun [complete_space E] :
  continuous_on (stereo_to_fun v) {x : E | innerSL v x ≠ (1:ℝ)} :=
(@cont_diff_on_stereo_to_fun E _ v _).continuous_on

variables (v)

/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection.  This is a map from the orthogonal complement of a unit vector `v` in an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereo_inv_fun`, not `stereo_inv_fun_aux`. -/
def stereo_inv_fun_aux (w : E) : E := (‖w‖ ^ 2 + 4)⁻¹ • ((4:ℝ) • w + (‖w‖ ^ 2 - 4) • v)

variables {v}

@[simp] lemma stereo_inv_fun_aux_apply (w : E) :
  stereo_inv_fun_aux v w = (‖w‖ ^ 2 + 4)⁻¹ • ((4:ℝ) • w + (‖w‖ ^ 2 - 4) • v) :=
rfl

lemma stereo_inv_fun_aux_mem (hv : ‖v‖ = 1) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) :
  stereo_inv_fun_aux v w ∈ (sphere (0:E) 1) :=
begin
  have h₁ : 0 ≤ ‖w‖ ^ 2 + 4 := by nlinarith,
  suffices : ‖(4:ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4,
  { have h₂ : ‖w‖ ^ 2 + 4 ≠ 0 := by nlinarith,
    simp only [mem_sphere_zero_iff_norm, norm_smul, real.norm_eq_abs, abs_inv, this,
      abs_of_nonneg h₁, stereo_inv_fun_aux_apply],
    field_simp },
  suffices : ‖(4:ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ ^ 2 = (‖w‖ ^ 2 + 4) ^ 2,
  { have h₃ : 0 ≤ ‖stereo_inv_fun_aux v w‖ := norm_nonneg _,
    simpa [h₁, h₃, -one_pow] using this },
  rw submodule.mem_orthogonal_singleton_iff_inner_left at hw,
  simp [norm_add_sq_real, norm_smul, inner_smul_left, inner_smul_right,
    hw, mul_pow, real.norm_eq_abs, hv],
  ring
end

lemma has_fderiv_at_stereo_inv_fun_aux (v : E) :
  has_fderiv_at (stereo_inv_fun_aux v) (continuous_linear_map.id ℝ E) 0 :=
begin
  have h₀ : has_fderiv_at (λ w : E, ‖w‖ ^ 2) (0 : E →L[ℝ] ℝ) 0,
  { convert (has_strict_fderiv_at_norm_sq _).has_fderiv_at,
    simp },
  have h₁ : has_fderiv_at (λ w : E, (‖w‖ ^ 2 + 4)⁻¹) (0 : E →L[ℝ] ℝ) 0,
  { convert (has_fderiv_at_inv _).comp _ (h₀.add (has_fderiv_at_const 4 0)); simp },
  have h₂ : has_fderiv_at (λ w, (4:ℝ) • w + (‖w‖ ^ 2 - 4) • v)
    ((4:ℝ) • continuous_linear_map.id ℝ E) 0,
  { convert ((has_fderiv_at_const (4:ℝ) 0).smul (has_fderiv_at_id 0)).add
      ((h₀.sub (has_fderiv_at_const (4:ℝ) 0)).smul (has_fderiv_at_const v 0)),
    ext w,
    simp, },
  convert h₁.smul h₂,
  ext w,
  simp,
end

lemma has_fderiv_at_stereo_inv_fun_aux_comp_coe (v : E) :
  has_fderiv_at (stereo_inv_fun_aux v ∘ (coe : (ℝ ∙ v)ᗮ → E)) (ℝ ∙ v)ᗮ.subtypeL 0 :=
begin
  have : has_fderiv_at
    (stereo_inv_fun_aux v)
    (continuous_linear_map.id ℝ E)
    ((ℝ ∙ v)ᗮ.subtypeL 0) :=
    has_fderiv_at_stereo_inv_fun_aux v,
  convert this.comp (0 : (ℝ ∙ v)ᗮ) (by apply continuous_linear_map.has_fderiv_at),
end

lemma cont_diff_stereo_inv_fun_aux : cont_diff ℝ ⊤ (stereo_inv_fun_aux v) :=
begin
  have h₀ : cont_diff ℝ ⊤ (λ w : E, ‖w‖ ^ 2) := cont_diff_norm_sq,
  have h₁ : cont_diff ℝ ⊤ (λ w : E, (‖w‖ ^ 2 + 4)⁻¹),
  { refine (h₀.add cont_diff_const).inv _,
    intros x,
    nlinarith },
  have h₂ : cont_diff ℝ ⊤ (λ w, (4:ℝ) • w + (‖w‖ ^ 2 - 4) • v),
  { refine (cont_diff_const.smul cont_diff_id).add _,
    refine (h₀.sub cont_diff_const).smul cont_diff_const },
  exact h₁.smul h₂
end

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereo_inv_fun (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) : sphere (0:E) 1 :=
⟨stereo_inv_fun_aux v (w:E), stereo_inv_fun_aux_mem hv w.2⟩

@[simp] lemma stereo_inv_fun_apply (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
  (stereo_inv_fun hv w : E) = (‖w‖ ^ 2 + 4)⁻¹ • ((4:ℝ) • w + (‖w‖ ^ 2 - 4) • v) :=
rfl

lemma stereo_inv_fun_ne_north_pole (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
  stereo_inv_fun hv w ≠ (⟨v, by simp [hv]⟩ : sphere (0:E) 1) :=
begin
  refine subtype.ne_of_val_ne _,
  rw ← inner_lt_one_iff_real_of_norm_one _ hv,
  { have hw : ⟪v, w⟫_ℝ = 0 := submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2,
    have hw' : (‖(w:E)‖ ^ 2 + 4)⁻¹ * (‖(w:E)‖ ^ 2 - 4) < 1,
    { refine (inv_mul_lt_iff' _).mpr _,
      { nlinarith },
      linarith },
    simpa [real_inner_comm, inner_add_right, inner_smul_right, real_inner_self_eq_norm_mul_norm, hw,
      hv] using hw' },
  { simpa using stereo_inv_fun_aux_mem hv w.2 }
end

lemma continuous_stereo_inv_fun (hv : ‖v‖ = 1) : continuous (stereo_inv_fun hv) :=
continuous_induced_rng.2 (cont_diff_stereo_inv_fun_aux.continuous.comp continuous_subtype_coe)

variables [complete_space E]

lemma stereo_left_inv (hv : ‖v‖ = 1) {x : sphere (0:E) 1} (hx : (x:E) ≠ v) :
  stereo_inv_fun hv (stereo_to_fun v x) = x :=
begin
  ext,
  simp only [stereo_to_fun_apply, stereo_inv_fun_apply, smul_add],
  -- name two frequently-occuring quantities and write down their basic properties
  set a : ℝ := innerSL v x,
  set y := orthogonal_projection (ℝ ∙ v)ᗮ x,
  have split : ↑x = a • v + ↑y,
  { convert eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ v) x,
    exact (orthogonal_projection_unit_singleton ℝ hv x).symm },
  have hvy : ⟪v, y⟫_ℝ = 0 := submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2,
  have pythag : 1 = a ^ 2 + ‖y‖ ^ 2,
  { have hvy' : ⟪a • v, y⟫_ℝ = 0 := by simp [inner_smul_left, hvy],
    convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy' using 2,
    { simp [← split] },
    { simp [norm_smul, hv, ← sq, sq_abs] },
    { exact sq _ } },
  -- two facts which will be helpful for clearing denominators in the main calculation
  have ha : 1 - a ≠ 0,
  { have : a < 1 := (inner_lt_one_iff_real_of_norm_one hv (by simp)).mpr hx.symm,
    linarith },
  have : 2 ^ 2 * ‖y‖ ^ 2 + 4 * (1 - a) ^ 2 ≠ 0,
  { refine ne_of_gt _,
    have := norm_nonneg (y:E),
    have : 0 < (1 - a) ^ 2 := sq_pos_of_ne_zero (1 - a) ha,
    nlinarith },
  -- the core of the problem is these two algebraic identities:
  have h₁ : (2 ^ 2 / (1 - a) ^ 2 * ‖y‖ ^ 2 + 4)⁻¹ * 4 * (2 / (1 - a)) = 1,
  { field_simp,
    simp only [submodule.coe_norm] at *,
    nlinarith },
  have h₂ : (2 ^ 2 / (1 - a) ^ 2 * ‖y‖ ^ 2 + 4)⁻¹ * (2 ^ 2 / (1 - a) ^ 2 * ‖y‖ ^ 2 - 4) = a,
  { field_simp,
    transitivity (1 - a) ^ 2 * (a * (2 ^ 2 * ‖y‖ ^ 2 + 4 * (1 - a) ^ 2)),
    { congr,
      simp only [submodule.coe_norm] at *,
      nlinarith },
    ring },
  -- deduce the result
  convert congr_arg2 has_add.add (congr_arg (λ t, t • (y:E)) h₁) (congr_arg (λ t, t • v) h₂)
    using 1,
  { simp [inner_add_right, inner_smul_right, hvy, real_inner_self_eq_norm_mul_norm, hv, mul_smul,
      mul_pow, real.norm_eq_abs, sq_abs, norm_smul] },
  { simp [split, add_comm] }
end

lemma stereo_right_inv (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
  stereo_to_fun v (stereo_inv_fun hv w) = w :=
begin
  have : 2 / (1 - (‖(w:E)‖ ^ 2 + 4)⁻¹ * (‖(w:E)‖ ^ 2 - 4)) * (‖(w:E)‖ ^ 2 + 4)⁻¹ * 4 = 1,
  { have : ‖(w:E)‖ ^ 2 + 4 ≠ 0 := by nlinarith,
    have : (4:ℝ) + 4 ≠ 0 := by nlinarith,
    field_simp,
    ring },
  convert congr_arg (λ c, c • w) this,
  { have h₁ : orthogonal_projection (ℝ ∙ v)ᗮ v = 0 :=
      orthogonal_projection_orthogonal_complement_singleton_eq_zero v,
    have h₂ : orthogonal_projection (ℝ ∙ v)ᗮ w = w :=
      orthogonal_projection_mem_subspace_eq_self w,
    have h₃ : innerSL v w = (0:ℝ) := submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2,
    have h₄ : innerSL v v = (1:ℝ) := by simp [real_inner_self_eq_norm_mul_norm, hv],
    simp [h₁, h₂, h₃, h₄, continuous_linear_map.map_add, continuous_linear_map.map_smul,
      mul_smul] },
  { simp }
end

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`; this
is the version as a local homeomorphism. -/
def stereographic (hv : ‖v‖ = 1) : local_homeomorph (sphere (0:E) 1) (ℝ ∙ v)ᗮ :=
{ to_fun := (stereo_to_fun v) ∘ coe,
  inv_fun := stereo_inv_fun hv,
  source := {⟨v, by simp [hv]⟩}ᶜ,
  target := set.univ,
  map_source' := by simp,
  map_target' := λ w _, stereo_inv_fun_ne_north_pole hv w,
  left_inv' := λ _ hx, stereo_left_inv hv (λ h, hx (subtype.ext h)),
  right_inv' := λ w _, stereo_right_inv hv w,
  open_source := is_open_compl_singleton,
  open_target := is_open_univ,
  continuous_to_fun := continuous_on_stereo_to_fun.comp continuous_subtype_coe.continuous_on
    (λ w h, h ∘ subtype.ext ∘ eq.symm ∘ (inner_eq_norm_mul_iff_of_norm_one hv (by simp)).mp),
  continuous_inv_fun := (continuous_stereo_inv_fun hv).continuous_on }

lemma stereographic_apply (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) :
  stereographic hv x = (2 / ((1:ℝ) - inner v x)) • orthogonal_projection (ℝ ∙ v)ᗮ x :=
rfl

@[simp] lemma stereographic_source (hv : ‖v‖ = 1) :
  (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ :=
rfl

@[simp] lemma stereographic_target (hv : ‖v‖ = 1) : (stereographic hv).target = set.univ := rfl

@[simp] lemma stereographic_apply_neg (v : sphere (0:E) 1) :
  stereographic (norm_eq_of_mem_sphere v) (-v) = 0 :=
by simp [stereographic_apply, orthogonal_projection_orthogonal_complement_singleton_eq_zero]

@[simp] lemma stereographic_neg_apply (v : sphere (0:E) 1) :
  stereographic (norm_eq_of_mem_sphere (-v)) v = 0 :=
begin
  convert stereographic_apply_neg (-v),
  ext1,
  simp,
end

end stereographic_projection

section charted_space

/-!
### Charted space structure on the sphere

In this section we construct a charted space structure on the unit sphere in a finite-dimensional
real inner product space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.

The restriction to finite dimension is for convenience.  The most natural `charted_space`
structure for the sphere uses the stereographic projection from the antipodes of a point as the
canonical chart at this point.  However, the codomain of the stereographic projection constructed
in the previous section is `(ℝ ∙ v)ᗮ`, the orthogonal complement of the vector `v` in `E` which is
the "north pole" of the projection, so a priori these charts all have different codomains.

So it is necessary to prove that these codomains are all continuously linearly equivalent to a
fixed normed space.  This could be proved in general by a simple case of Gram-Schmidt
orthogonalization, but in the finite-dimensional case it follows more easily by dimension-counting.
-/

/-- Variant of the stereographic projection, for the sphere in an `n + 1`-dimensional inner product
space `E`.  This version has codomain the Euclidean space of dimension `n`, and is obtained by
composing the original sterographic projection (`stereographic`) with an arbitrary linear isometry
from `(ℝ ∙ v)ᗮ` to the Euclidean space. -/
def stereographic' (n : ℕ) [fact (finrank ℝ E = n + 1)] (v : sphere (0:E) 1) :
  local_homeomorph (sphere (0:E) 1) (euclidean_space ℝ (fin n)) :=
(stereographic (norm_eq_of_mem_sphere v)) ≫ₕ
(orthonormal_basis.from_orthogonal_span_singleton n
  (ne_zero_of_mem_unit_sphere v)).repr.to_homeomorph.to_local_homeomorph

@[simp] lemma stereographic'_source {n : ℕ} [fact (finrank ℝ E = n + 1)] (v : sphere (0:E) 1) :
  (stereographic' n v).source = {v}ᶜ :=
by simp [stereographic']

@[simp] lemma stereographic'_target {n : ℕ} [fact (finrank ℝ E = n + 1)] (v : sphere (0:E) 1) :
  (stereographic' n v).target = set.univ :=
by simp [stereographic']

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted space
modelled on the Euclidean space of dimension `n`. -/
instance {n : ℕ} [fact (finrank ℝ E = n + 1)] :
  charted_space (euclidean_space ℝ (fin n)) (sphere (0:E) 1) :=
{ atlas            := {f | ∃ v : (sphere (0:E) 1), f = stereographic' n v},
  chart_at         := λ v, stereographic' n (-v),
  mem_chart_source := λ v, by simpa using ne_neg_of_mem_unit_sphere ℝ v,
  chart_mem_atlas  := λ v, ⟨-v, rfl⟩ }

end charted_space

section smooth_manifold

lemma sphere_ext_iff (u v : sphere (0:E) 1) :
  u = v ↔ ⟪(u:E), v⟫_ℝ = 1 :=
by simp [subtype.ext_iff, inner_eq_norm_mul_iff_of_norm_one]

lemma stereographic'_symm_apply {n : ℕ} [fact (finrank ℝ E = n + 1)]
    (v : sphere (0:E) 1) (x : euclidean_space ℝ (fin n)) :
  ((stereographic' n v).symm x : E) =
    let U : (ℝ ∙ (v:E))ᗮ ≃ₗᵢ[ℝ] euclidean_space ℝ (fin n) :=
      (orthonormal_basis.from_orthogonal_span_singleton n
        (ne_zero_of_mem_unit_sphere v)).repr in
    ((‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm x : E) +
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • v) :=
by simp [real_inner_comm, stereographic, stereographic', ← submodule.coe_norm]

/-! ### Smooth manifold structure on the sphere -/

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a smooth manifold,
modelled on the Euclidean space of dimension `n`. -/
instance {n : ℕ} [fact (finrank ℝ E = n + 1)] :
  smooth_manifold_with_corners (𝓡 n) (sphere (0:E) 1) :=
smooth_manifold_with_corners_of_cont_diff_on (𝓡 n) (sphere (0:E) 1)
begin
  rintros _ _ ⟨v, rfl⟩ ⟨v', rfl⟩,
  let U := -- Removed type ascription, and this helped for some reason with timeout issues?
    (orthonormal_basis.from_orthogonal_span_singleton n
      (ne_zero_of_mem_unit_sphere v)).repr,
  let U' :=-- Removed type ascription, and this helped for some reason with timeout issues?
    (orthonormal_basis.from_orthogonal_span_singleton n
      (ne_zero_of_mem_unit_sphere v')).repr,
  have hUv : stereographic' n v = (stereographic (norm_eq_of_mem_sphere v)) ≫ₕ
    U.to_homeomorph.to_local_homeomorph := rfl,
  have hU'v' : stereographic' n v' = (stereographic (norm_eq_of_mem_sphere v')).trans
    U'.to_homeomorph.to_local_homeomorph := rfl,
  have H₁ := U'.cont_diff.comp_cont_diff_on cont_diff_on_stereo_to_fun,
  have H₂ := (cont_diff_stereo_inv_fun_aux.comp
      (ℝ ∙ (v:E))ᗮ.subtypeL.cont_diff).comp U.symm.cont_diff,
  convert H₁.comp' (H₂.cont_diff_on : cont_diff_on ℝ ⊤ _ set.univ) using 1,
  ext,
  simp [sphere_ext_iff, stereographic'_symm_apply, real_inner_comm]
end

/-- The inclusion map (i.e., `coe`) from the sphere in `E` to `E` is smooth.  -/
lemma cont_mdiff_coe_sphere {n : ℕ} [fact (finrank ℝ E = n + 1)] :
  cont_mdiff (𝓡 n) 𝓘(ℝ, E) ∞ (coe : (sphere (0:E) 1) → E) :=
begin
  rw cont_mdiff_iff,
  split,
  { exact continuous_subtype_coe },
  { intros v _,
    let U := -- Again, removing type ascription...
      (orthonormal_basis.from_orthogonal_span_singleton n
        (ne_zero_of_mem_unit_sphere (-v))).repr,
    exact ((cont_diff_stereo_inv_fun_aux.comp
      (ℝ ∙ ((-v):E))ᗮ.subtypeL.cont_diff).comp U.symm.cont_diff).cont_diff_on }
end

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {H : Type*} [topological_space H] {I : model_with_corners ℝ F H}
variables {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

/-- If a `cont_mdiff` function `f : M → E`, where `M` is some manifold, takes values in the
sphere, then it restricts to a `cont_mdiff` function from `M` to the sphere. -/
lemma cont_mdiff.cod_restrict_sphere {n : ℕ} [fact (finrank ℝ E = n + 1)]
  {m : ℕ∞} {f : M → E} (hf : cont_mdiff I 𝓘(ℝ, E) m f)
  (hf' : ∀ x, f x ∈ sphere (0:E) 1) :
  cont_mdiff I (𝓡 n) m (set.cod_restrict _ _ hf' : M → (sphere (0:E) 1)) :=
begin
  rw cont_mdiff_iff_target,
  refine ⟨continuous_induced_rng.2 hf.continuous, _⟩,
  intros v,
  let U := -- Again, removing type ascription... Weird that this helps!
    (orthonormal_basis.from_orthogonal_span_singleton n (ne_zero_of_mem_unit_sphere (-v))).repr,
  have h : cont_diff_on ℝ ⊤ _ set.univ :=
    U.cont_diff.cont_diff_on,
  have H₁ := (h.comp' cont_diff_on_stereo_to_fun).cont_mdiff_on,
  have H₂ : cont_mdiff_on _ _ _ _ set.univ := hf.cont_mdiff_on,
  convert (H₁.of_le le_top).comp' H₂ using 1,
  ext x,
  have hfxv : f x = -↑v ↔ ⟪f x, -↑v⟫_ℝ = 1,
  { have hfx : ‖f x‖ = 1 := by simpa using hf' x,
    rw inner_eq_norm_mul_iff_of_norm_one hfx,
    exact norm_eq_of_mem_sphere (-v) },
  dsimp [chart_at],
  simp [not_iff_not, subtype.ext_iff, hfxv, real_inner_comm]
end

/-- The antipodal map is smooth. -/
lemma cont_mdiff_neg_sphere {n : ℕ} [fact (finrank ℝ E = n + 1)] :
  cont_mdiff (𝓡 n) (𝓡 n) ∞ (λ x : sphere (0:E) 1, -x) :=
begin
  -- this doesn't elaborate well in term mode
  apply cont_mdiff.cod_restrict_sphere,
  apply cont_diff_neg.cont_mdiff.comp _,
  exact cont_mdiff_coe_sphere,
end

/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `tangent_space (𝓡 n) v` to `E`.  The range of this map is the orthogonal complement
of `v` in `E`.

Note that there is an abuse here of the defeq between `E` and the tangent space to `E` at `(v:E`).
In general this defeq is not canonical, but in this case (the tangent space of a vector space) it is
canonical. -/
lemma range_mfderiv_coe_sphere {n : ℕ} [fact (finrank ℝ E = n + 1)] (v : sphere (0:E) 1) :
  (mfderiv (𝓡 n) 𝓘(ℝ, E) (coe : sphere (0:E) 1 → E) v : tangent_space (𝓡 n) v →L[ℝ] E).range
  = (ℝ ∙ (v:E))ᗮ :=
begin
  rw ((cont_mdiff_coe_sphere v).mdifferentiable_at le_top).mfderiv,
  simp only [chart_at, stereographic', stereographic_neg_apply, fderiv_within_univ,
    linear_isometry_equiv.to_homeomorph_symm, linear_isometry_equiv.coe_to_homeomorph,
    linear_isometry_equiv.map_zero] with mfld_simps,
  let U :=
    (orthonormal_basis.from_orthogonal_span_singleton n (ne_zero_of_mem_unit_sphere (-v))).repr,
  change (fderiv ℝ ((stereo_inv_fun_aux (-v : E) ∘ coe) ∘ U.symm) 0).range = (ℝ ∙ (v:E))ᗮ,
  have : has_fderiv_at
      (stereo_inv_fun_aux (-v : E) ∘ (coe : (ℝ ∙ (↑(-v):E))ᗮ → E))
      (ℝ ∙ (↑(-v):E))ᗮ.subtypeL
      (U.symm 0),
  { convert has_fderiv_at_stereo_inv_fun_aux_comp_coe (-v:E),
    simp },
  rw (this.comp 0 U.symm.to_continuous_linear_equiv.has_fderiv_at).fderiv,
  convert (U.symm : euclidean_space ℝ (fin n) ≃ₗᵢ[ℝ] (ℝ ∙ (↑(-v):E))ᗮ).range_comp
      (ℝ ∙ (↑(-v):E))ᗮ.subtype using 1,
  simp only [submodule.range_subtype, coe_neg_sphere],
  congr' 1,
  -- we must show `submodule.span ℝ {v} = submodule.span ℝ {-v}`
  apply submodule.span_eq_span,
  { simp only [set.singleton_subset_iff, set_like.mem_coe],
    rw ← submodule.neg_mem_iff,
    exact submodule.mem_span_singleton_self (-v) },
  { simp only [set.singleton_subset_iff, set_like.mem_coe],
    rw submodule.neg_mem_iff,
    exact submodule.mem_span_singleton_self v },
end

/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `tangent_space (𝓡 n) v` to `E`.  This map is injective. -/
lemma mfderiv_coe_sphere_injective {n : ℕ} [fact (finrank ℝ E = n + 1)] (v : sphere (0:E) 1) :
  injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (coe : sphere (0:E) 1 → E) v) :=
begin
  rw ((cont_mdiff_coe_sphere v).mdifferentiable_at le_top).mfderiv,
  simp only [chart_at, stereographic', stereographic_neg_apply, fderiv_within_univ,
    linear_isometry_equiv.to_homeomorph_symm, linear_isometry_equiv.coe_to_homeomorph,
    linear_isometry_equiv.map_zero] with mfld_simps,
  let U :=
    (orthonormal_basis.from_orthogonal_span_singleton n (ne_zero_of_mem_unit_sphere (-v))).repr,
  change injective (fderiv ℝ ((stereo_inv_fun_aux (-v : E) ∘ coe) ∘ U.symm) 0),
  have : has_fderiv_at
      (stereo_inv_fun_aux (-v : E) ∘ (coe : (ℝ ∙ (↑(-v):E))ᗮ → E))
      (ℝ ∙ (↑(-v):E))ᗮ.subtypeL
      (U.symm 0),
  { convert has_fderiv_at_stereo_inv_fun_aux_comp_coe (-v:E),
    simp },
  rw (this.comp 0 U.symm.to_continuous_linear_equiv.has_fderiv_at).fderiv,
  simpa using subtype.coe_injective,
end

end smooth_manifold

section circle

open complex

local attribute [instance] finrank_real_complex_fact

/-- The unit circle in `ℂ` is a charted space modelled on `euclidean_space ℝ (fin 1)`.  This
follows by definition from the corresponding result for `metric.sphere`. -/
instance : charted_space (euclidean_space ℝ (fin 1)) circle := metric.sphere.charted_space

instance : smooth_manifold_with_corners (𝓡 1) circle :=
metric.sphere.smooth_manifold_with_corners

/-- The unit circle in `ℂ` is a Lie group. -/
instance : lie_group (𝓡 1) circle :=
{ smooth_mul := begin
    apply cont_mdiff.cod_restrict_sphere,
    let c : circle → ℂ := coe,
    have h₂ : cont_mdiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ (λ (z : ℂ × ℂ), z.fst * z.snd),
    { rw cont_mdiff_iff,
      exact ⟨continuous_mul, λ x y, cont_diff_mul.cont_diff_on⟩ },
    suffices h₁ : cont_mdiff _ _ _ (prod.map c c),
    { apply h₂.comp h₁ },
    -- this elaborates much faster with `apply`
    apply cont_mdiff.prod_map; exact cont_mdiff_coe_sphere,
  end,
  smooth_inv := begin
    apply cont_mdiff.cod_restrict_sphere,
    simp only [← coe_inv_circle, coe_inv_circle_eq_conj],
    exact complex.conj_cle.cont_diff.cont_mdiff.comp cont_mdiff_coe_sphere
  end }

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ` is smooth. -/
lemma cont_mdiff_exp_map_circle : cont_mdiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ exp_map_circle :=
((cont_diff_exp.comp (cont_diff_id.smul cont_diff_const)).cont_mdiff).cod_restrict_sphere _

end circle
