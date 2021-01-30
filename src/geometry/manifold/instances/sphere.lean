/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.charted_space
import analysis.normed_space.inner_product

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put a charted space structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, a local homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal complement of
`v`).

For finite-dimensional `E`, we then construct a charted space instance on the sphere; the charts
here are obtained by composing the local homeomorphisms `stereographic` with arbitrary isometries
from `(ℝ ∙ v)ᗮ` to Euclidean space.

## Implementation notes

The model space for the charted space instance is `euclidean_space ℝ (fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[fact (findim ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `euclidean_space ℝ (fin (findim ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `euclidean_space ℝ (fin (2 - 1))` but not with model space
`euclidean_space ℝ (fin 1)`.
-/

variables {E : Type*} [inner_product_space ℝ E]

noncomputable theory

open metric finite_dimensional

section stereographic_projection
variables (v : E)

/-! ### Construction of the stereographic projection -/

/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the affine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere to the stereographic
projection. -/
def stereo_to_fun [complete_space E] (x : E) : (ℝ ∙ v)ᗮ :=
(2 / ((1:ℝ) - inner_right v x)) • orthogonal_projection (ℝ ∙ v)ᗮ x

variables {v}

@[simp] lemma stereo_to_fun_apply [complete_space E] (x : E) :
  stereo_to_fun v x = (2 / ((1:ℝ) - inner_right v x)) • orthogonal_projection (ℝ ∙ v)ᗮ x :=
rfl

lemma times_cont_diff_on_stereo_to_fun [complete_space E] :
  times_cont_diff_on ℝ ⊤ (stereo_to_fun v) {x : E | inner_right v x ≠ (1:ℝ)} :=
begin
  refine times_cont_diff_on.smul _
    (orthogonal_projection ((ℝ ∙ v)ᗮ)).times_cont_diff.times_cont_diff_on,
  refine times_cont_diff_const.times_cont_diff_on.div _ _,
  { exact (times_cont_diff_const.sub (inner_right v).times_cont_diff).times_cont_diff_on },
  { intros x h h',
    exact h (sub_eq_zero.mp h').symm }
end

lemma continuous_on_stereo_to_fun [complete_space E] :
  continuous_on (stereo_to_fun v) {x : E | inner_right v x ≠ (1:ℝ)} :=
times_cont_diff_on_stereo_to_fun.continuous_on

variables (v)

/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection.  This is a map from the orthogonal complement of a unit vector `v` in an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereo_inv_fun`, not `stereo_inv_fun_aux`. -/
def stereo_inv_fun_aux (w : E) : E := (∥w∥ ^ 2 + 4)⁻¹ • ((4:ℝ) • w + (∥w∥ ^ 2 - 4) • v)

variables {v}

@[simp] lemma stereo_inv_fun_aux_apply (w : E) :
  stereo_inv_fun_aux v w = (∥w∥ ^ 2 + 4)⁻¹ • ((4:ℝ) • w + (∥w∥ ^ 2 - 4) • v) :=
rfl

lemma stereo_inv_fun_aux_mem (hv : ∥v∥ = 1) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) :
  stereo_inv_fun_aux v w ∈ (sphere (0:E) 1) :=
begin
  have h₁ : 0 ≤ ∥w∥ ^ 2 + 4 := by nlinarith,
  suffices : ∥(4:ℝ) • w + (∥w∥ ^ 2 - 4) • v∥ = ∥w∥ ^ 2 + 4,
  { have h₂ : ∥w∥ ^ 2 + 4 ≠ 0 := by nlinarith,
    simp only [mem_sphere_zero_iff_norm, norm_smul, real.norm_eq_abs, abs_inv, this,
      abs_of_nonneg h₁, stereo_inv_fun_aux_apply],
    field_simp },
  suffices : ∥(4:ℝ) • w + (∥w∥ ^ 2 - 4) • v∥ ^ 2 = (∥w∥ ^ 2 + 4) ^ 2,
  { have h₃ : 0 ≤ ∥stereo_inv_fun_aux v w∥ := norm_nonneg _,
    simpa [h₁, h₃, -one_pow] using this },
  simp [norm_add_pow_two_real, norm_smul, inner_smul_left, inner_smul_right,
    inner_left_of_mem_orthogonal_singleton _ hw, mul_pow, real.norm_eq_abs, hv],
  ring
end

lemma times_cont_diff_stereo_inv_fun_aux : times_cont_diff ℝ ⊤ (stereo_inv_fun_aux v) :=
begin
  have h₀ : times_cont_diff ℝ ⊤ (λ w : E, ∥w∥ ^ 2) := times_cont_diff_norm_square,
  have h₁ : times_cont_diff ℝ ⊤ (λ w : E, (∥w∥ ^ 2 + 4)⁻¹),
  { refine (h₀.add times_cont_diff_const).inv _,
    intros x,
    nlinarith },
  have h₂ : times_cont_diff ℝ ⊤ (λ w, (4:ℝ) • w + (∥w∥ ^ 2 - 4) • v),
  { refine (times_cont_diff_const.smul times_cont_diff_id).add _,
    refine (h₀.sub times_cont_diff_const).smul times_cont_diff_const },
  exact h₁.smul h₂
end

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereo_inv_fun (hv : ∥v∥ = 1) (w : (ℝ ∙ v)ᗮ) : sphere (0:E) 1 :=
⟨stereo_inv_fun_aux v (w:E), stereo_inv_fun_aux_mem hv w.2⟩

@[simp] lemma stereo_inv_fun_apply (hv : ∥v∥ = 1) (w : (ℝ ∙ v)ᗮ) :
  (stereo_inv_fun hv w : E) = (∥w∥ ^ 2 + 4)⁻¹ • ((4:ℝ) • w + (∥w∥ ^ 2 - 4) • v) :=
rfl

lemma stereo_inv_fun_ne_north_pole (hv : ∥v∥ = 1) (w : (ℝ ∙ v)ᗮ) :
  stereo_inv_fun hv w ≠ (⟨v, by simp [hv]⟩ : sphere (0:E) 1) :=
begin
  refine subtype.ne_of_val_ne _,
  rw ← inner_lt_one_iff_real_of_norm_one _ hv,
  { have hw : ⟪v, w⟫_ℝ = 0 := inner_right_of_mem_orthogonal_singleton v w.2,
    have hw' : (∥(w:E)∥ ^ 2 + 4)⁻¹ * (∥(w:E)∥ ^ 2 - 4) < 1,
    { refine (inv_mul_lt_iff' _).mpr _,
      { nlinarith },
      linarith },
    simpa [real_inner_comm, inner_add_right, inner_smul_right, real_inner_self_eq_norm_square, hw,
      hv] using hw' },
  { simpa using stereo_inv_fun_aux_mem hv w.2 }
end

lemma continuous_stereo_inv_fun (hv : ∥v∥ = 1) : continuous (stereo_inv_fun hv) :=
continuous_induced_rng (times_cont_diff_stereo_inv_fun_aux.continuous.comp continuous_subtype_coe)

variables [complete_space E]

lemma stereo_left_inv (hv : ∥v∥ = 1) {x : sphere (0:E) 1} (hx : (x:E) ≠ v) :
  stereo_inv_fun hv (stereo_to_fun v x) = x :=
begin
  ext,
  simp only [stereo_to_fun_apply, stereo_inv_fun_apply, smul_add],
  -- name two frequently-occuring quantities and write down their basic properties
  set a : ℝ := inner_right v x,
  set y := orthogonal_projection (ℝ ∙ v)ᗮ x,
  have split : ↑x = a • v + ↑y,
  { convert eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ v) x,
    exact (orthogonal_projection_unit_singleton ℝ hv x).symm },
  have hvy : ⟪v, y⟫_ℝ = 0 := inner_right_of_mem_orthogonal_singleton v y.2,
  have pythag : 1 = a ^ 2 + ∥(y:E)∥ ^ 2,
  { have hvy' : ⟪a • v, y⟫_ℝ = 0 := by simp [inner_smul_left, hvy],
    convert norm_add_square_eq_norm_square_add_norm_square_of_inner_eq_zero _ _ hvy' using 2,
    { simp [← split] },
    { simp [norm_smul, hv, real.norm_eq_abs, ← pow_two, abs_sq_eq] },
    { exact pow_two _ } },
  -- two facts which will be helpful for clearing denominators in the main calculation
  have ha : 1 - a ≠ 0,
  { have : a < 1 := (inner_lt_one_iff_real_of_norm_one hv (by simp)).mpr hx.symm,
    linarith },
  have : 2 ^ 2 * ∥(y:E)∥ ^ 2 + 4 * (1 - a) ^ 2 ≠ 0,
  { refine ne_of_gt _,
    have := norm_nonneg (y:E),
    have : 0 < (1 - a) ^ 2 := pow_two_pos_of_ne_zero (1 - a) ha,
    nlinarith },
  -- the core of the problem is these two algebraic identities:
  have h₁ : (2 ^ 2 / (1 - a) ^ 2 * ∥y∥ ^ 2 + 4)⁻¹ * 4 * (2 / (1 - a)) = 1,
  { field_simp,
    nlinarith },
  have h₂ : (2 ^ 2 / (1 - a) ^ 2 * ∥(y:E)∥ ^ 2 + 4)⁻¹ * (2 ^ 2 / (1 - a) ^ 2 * ∥(y:E)∥ ^ 2 - 4) = a,
  { field_simp,
    transitivity (1 - a) ^ 2 * (a * (2 ^ 2 * ∥(y:E)∥ ^ 2 + 4 * (1 - a) ^ 2)),
    { congr,
      nlinarith },
    ring },
  -- deduce the result
  convert congr_arg2 has_add.add (congr_arg (λ t, t • (y:E)) h₁) (congr_arg (λ t, t • v) h₂)
    using 1,
  { simp [inner_add_right, inner_smul_right, hvy, real_inner_self_eq_norm_square, hv, mul_smul,
      mul_pow, real.norm_eq_abs, abs_sq_eq, norm_smul] },
  { simp [split, add_comm] }
end

lemma stereo_right_inv (hv : ∥v∥ = 1) (w : (ℝ ∙ v)ᗮ) :
  stereo_to_fun v (stereo_inv_fun hv w) = w :=
begin
  have : 2 / (1 - (∥(w:E)∥ ^ 2 + 4)⁻¹ * (∥(w:E)∥ ^ 2 - 4)) * (∥(w:E)∥ ^ 2 + 4)⁻¹ * 4 = 1,
  { have : ∥(w:E)∥ ^ 2 + 4 ≠ 0 := by nlinarith,
    have : (4:ℝ) + 4 ≠ 0 := by nlinarith,
    field_simp,
    ring },
  convert congr_arg (λ c, c • w) this,
  { have h₁ : orthogonal_projection (ℝ ∙ v)ᗮ v = 0 :=
      orthogonal_projection_orthogonal_complement_singleton_eq_zero v,
    have h₂ : orthogonal_projection (ℝ ∙ v)ᗮ w = w :=
      orthogonal_projection_mem_subspace_eq_self w,
    have h₃ : inner_right v w = (0:ℝ) := inner_right_of_mem_orthogonal_singleton v w.2,
    have h₄ : inner_right v v = (1:ℝ) := by simp [real_inner_self_eq_norm_square, hv],
    simp [h₁, h₂, h₃, h₄, continuous_linear_map.map_add, continuous_linear_map.map_smul,
      mul_smul] },
  { simp }
end

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`; this
is the version as a local homeomorphism. -/
def stereographic (hv : ∥v∥ = 1) : local_homeomorph (sphere (0:E) 1) (ℝ ∙ v)ᗮ :=
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

@[simp] lemma stereographic_source (hv : ∥v∥ = 1) :
  (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ :=
rfl

@[simp] lemma stereographic_target (hv : ∥v∥ = 1) : (stereographic hv).target = set.univ := rfl

end stereographic_projection

section charted_space

variables [finite_dimensional ℝ E]

/-! ### Charted space structure on the sphere

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
def stereographic' {n : ℕ} (hn : findim ℝ E = n + 1) (v : sphere (0:E) 1) :
  local_homeomorph (sphere (0:E) 1) (euclidean_space ℝ (fin n)) :=
(stereographic (norm_eq_of_mem_sphere v)).trans
(linear_isometry_equiv.from_orthogonal_span_singleton hn
  (nonzero_of_mem_unit_sphere v)).to_continuous_linear_equiv.to_homeomorph.to_local_homeomorph

@[simp] lemma stereographic'_source {n : ℕ} (hn : findim ℝ E = n + 1) (v : sphere (0:E) 1) :
  (stereographic' hn v).source = {v}ᶜ :=
by simp [stereographic']

@[simp] lemma stereographic'_target {n : ℕ} (hn : findim ℝ E = n + 1) (v : sphere (0:E) 1) :
  (stereographic' hn v).target = set.univ :=
by simp [stereographic']

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted space
modelled on the Euclidean space of dimension `n`. -/
instance {n : ℕ} [_i : fact (findim ℝ E = n + 1)] :
  charted_space (euclidean_space ℝ (fin n)) (sphere (0:E) 1) :=
{ atlas            := {f | ∃ v : (sphere (0:E) 1), f = stereographic' _i.elim v},
  chart_at         := λ v, stereographic' _i.elim (-v),
  mem_chart_source := λ v, by simpa using ne_neg_of_mem_unit_sphere ℝ v,
  chart_mem_atlas  := λ v, ⟨-v, rfl⟩ }

end charted_space
