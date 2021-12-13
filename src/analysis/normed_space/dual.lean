/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.hahn_banach
import analysis.normed_space.is_R_or_C

/-!
# The topological dual of a normed space

In this file we define the topological dual `normed_space.dual` of a normed space, and the
continuous linear map `normed_space.inclusion_in_double_dual` from a normed space into its double
dual.

For base field `𝕜 = ℝ` or `𝕜 = ℂ`, this map is actually an isometric embedding; we provide a
version `normed_space.inclusion_in_double_dual_li` of the map which is of type a bundled linear
isometric embedding, `E →ₗᵢ[𝕜] (dual 𝕜 (dual 𝕜 E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `semi_normed_space` and we specialize to `normed_space` when needed.

## Main definitions

* `inclusion_in_double_dual` and `inclusion_in_double_dual_li` are the inclusion of a normed space
  in its double dual, considered as a bounded linear map and as a linear isometry, respectively.
* `polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals `x'` for which
  `∥x' z∥ ≤ 1` for every `z ∈ s`.

## Tags

dual
-/

noncomputable theory
open_locale classical
universes u v

namespace normed_space

section general
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (E : Type*) [semi_normed_group E] [semi_normed_space 𝕜 E]
variables (F : Type*) [normed_group F] [normed_space 𝕜 F]

/-- The topological dual of a seminormed space `E`. -/
@[derive [inhabited, semi_normed_group, semi_normed_space 𝕜]] def dual := E →L[𝕜] 𝕜

instance : add_monoid_hom_class (dual 𝕜 E) E 𝕜 := continuous_linear_map.add_monoid_hom_class

instance : has_coe_to_fun (dual 𝕜 E) (λ _, E → 𝕜) := continuous_linear_map.to_fun

instance : normed_group (dual 𝕜 F) := continuous_linear_map.to_normed_group

instance : normed_space 𝕜 (dual 𝕜 F) := continuous_linear_map.to_normed_space

instance [finite_dimensional 𝕜 E] : finite_dimensional 𝕜 (dual 𝕜 E) :=
continuous_linear_map.finite_dimensional

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual : E →L[𝕜] (dual 𝕜 (dual 𝕜 E)) :=
continuous_linear_map.apply 𝕜 𝕜

@[simp] lemma dual_def (x : E) (f : dual 𝕜 E) : inclusion_in_double_dual 𝕜 E x f = f x := rfl

lemma inclusion_in_double_dual_norm_eq :
  ∥inclusion_in_double_dual 𝕜 E∥ = ∥(continuous_linear_map.id 𝕜 (dual 𝕜 E))∥ :=
continuous_linear_map.op_norm_flip _

lemma inclusion_in_double_dual_norm_le : ∥inclusion_in_double_dual 𝕜 E∥ ≤ 1 :=
by { rw inclusion_in_double_dual_norm_eq, exact continuous_linear_map.norm_id_le }

lemma double_dual_bound (x : E) : ∥(inclusion_in_double_dual 𝕜 E) x∥ ≤ ∥x∥ :=
by simpa using continuous_linear_map.le_of_op_norm_le _ (inclusion_in_double_dual_norm_le 𝕜 E) x

end general

section bidual_isometry

variables (𝕜 : Type v) [is_R_or_C 𝕜]
  {E : Type u} [normed_group E] [normed_space 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
lemma norm_le_dual_bound (x : E) {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ (f : dual 𝕜 E), ∥f x∥ ≤ M * ∥f∥) :
  ∥x∥ ≤ M :=
begin
  classical,
  by_cases h : x = 0,
  { simp only [h, hMp, norm_zero] },
  { obtain ⟨f, hf⟩ : ∃ g : E →L[𝕜] 𝕜, _ := exists_dual_vector 𝕜 x h,
    calc ∥x∥ = ∥(∥x∥ : 𝕜)∥ : is_R_or_C.norm_coe_norm.symm
    ... = ∥f x∥ : by rw hf.2
    ... ≤ M * ∥f∥ : hM f
    ... = M : by rw [hf.1, mul_one] }
end

lemma eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
norm_eq_zero.mp (le_antisymm (norm_le_dual_bound 𝕜 x le_rfl (λ f, by simp [h f])) (norm_nonneg _))

lemma eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : dual 𝕜 E, g x = 0 :=
⟨λ hx, by simp [hx], λ h, eq_zero_of_forall_dual_eq_zero 𝕜 h⟩

lemma eq_iff_forall_dual_eq {x y : E} :
  x = y ↔ ∀ g : dual 𝕜 E, g x = g y :=
begin
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)],
  simp [sub_eq_zero],
end

/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
def inclusion_in_double_dual_li : E →ₗᵢ[𝕜] (dual 𝕜 (dual 𝕜 E)) :=
{ norm_map' := begin
    intros x,
    apply le_antisymm,
    { exact double_dual_bound 𝕜 E x },
    rw continuous_linear_map.norm_def,
    refine le_cInf continuous_linear_map.bounds_nonempty _,
    rintros c ⟨hc1, hc2⟩,
    exact norm_le_dual_bound 𝕜 x hc1 hc2
  end,
  .. inclusion_in_double_dual 𝕜 E }

end bidual_isometry

end normed_space

section polar_sets

open metric set normed_space

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def polar (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (s : set E) : set (dual 𝕜 E) :=
{x' : dual 𝕜 E | ∀ z ∈ s, ∥ x' z ∥ ≤ 1}

open metric set normed_space
open_locale topological_space

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

@[simp] lemma zero_mem_polar (s : set E) :
  (0 : dual 𝕜 E) ∈ polar 𝕜 s :=
λ _ _, by simp only [zero_le_one, continuous_linear_map.zero_apply, norm_zero]

lemma polar_eq_Inter (s : set E) :
  polar 𝕜 s = ⋂ z ∈ s, {x' : dual 𝕜 E | ∥ x' z ∥ ≤ 1} :=
by { ext, simp only [polar, mem_bInter_iff, mem_set_of_eq], }

@[simp] lemma polar_empty : polar 𝕜 (∅ : set E) = univ :=
by simp only [polar, forall_false_left, mem_empty_eq, forall_const, set_of_true]

variables {𝕜}

/-- If `x'` is a dual element such that the norms `∥x' z∥` are bounded for `z ∈ s`, then a
small scalar multiple of `x'` is in `polar 𝕜 s`. -/
lemma smul_mem_polar {s : set E} {x' : dual 𝕜 E} {c : 𝕜}
  (hc : ∀ z, z ∈ s → ∥ x' z ∥ ≤ ∥c∥) : c⁻¹ • x' ∈ polar 𝕜 s :=
begin
  by_cases c_zero : c = 0, { simp [c_zero] },
  have eq : ∀ z, ∥ c⁻¹ • (x' z) ∥ = ∥ c⁻¹ ∥ * ∥ x' z ∥ := λ z, norm_smul c⁻¹ _,
  have le : ∀ z, z ∈ s → ∥ c⁻¹ • (x' z) ∥ ≤ ∥ c⁻¹ ∥ * ∥ c ∥,
  { intros z hzs,
    rw eq z,
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _), },
  have cancel : ∥ c⁻¹ ∥ * ∥ c ∥ = 1,
  by simp only [c_zero, norm_eq_zero, ne.def, not_false_iff,
                inv_mul_cancel, normed_field.norm_inv],
  rwa cancel at le,
end

variables (𝕜)

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
lemma polar_closed_ball
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] {r : ℝ} (hr : 0 < r) :
  polar 𝕜 (closed_ball (0 : E) r) = closed_ball (0 : dual 𝕜 E) (1/r) :=
begin
  ext x',
  simp only [mem_closed_ball, mem_set_of_eq, dist_zero_right],
  split,
  { intros h,
    apply continuous_linear_map.op_norm_le_of_ball hr (one_div_nonneg.mpr hr.le),
    { exact λ z hz, linear_map.bound_of_ball_bound hr 1 x'.to_linear_map h z, },
    { exact ring_hom_isometric.ids, }, },
  { intros h z hz,
    simp only [mem_closed_ball, dist_zero_right] at hz,
    have key := (continuous_linear_map.le_op_norm x' z).trans
      (mul_le_mul h hz (norm_nonneg _) (one_div_nonneg.mpr hr.le)),
    rwa [one_div_mul_cancel hr.ne.symm] at key, },
end

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar 𝕜 s` are bounded by a constant. -/
lemma polar_bounded_of_nhds_zero {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  ∃ (c : ℝ), ∀ x' ∈ polar 𝕜 s, ∥x'∥ ≤ c :=
begin
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ∥a∥ := normed_field.exists_one_lt_norm 𝕜,
  obtain ⟨r, r_pos, r_ball⟩ : ∃ (r : ℝ) (hr : 0 < r), ball 0 r ⊆ s :=
    metric.mem_nhds_iff.1 s_nhd,
  refine ⟨∥a∥ / r, λ x' hx', _⟩,
  have I : 0 ≤ ∥a∥ / r := div_nonneg (norm_nonneg _) r_pos.le,
  refine continuous_linear_map.op_norm_le_of_shell r_pos I ha (λ x hx h'x, _),
  have x_mem : x ∈ ball (0 : E) r, by simpa only [mem_ball_zero_iff] using h'x,
  calc ∥x' x∥ ≤ 1 : hx' x (r_ball x_mem)
  ... = (∥a∥ / r) * (r / ∥a∥) : by field_simp [r_pos.ne', (zero_lt_one.trans ha).ne']
  ... ≤ (∥a∥ / r) * ∥x∥ : mul_le_mul_of_nonneg_left hx I
end

end polar_sets
