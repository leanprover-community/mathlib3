/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.hahn_banach
import analysis.normed_space.is_R_or_C
import analysis.locally_convex.polar

/-!
# The topological dual of a normed space

In this file we define the topological dual `normed_space.dual` of a normed space, and the
continuous linear map `normed_space.inclusion_in_double_dual` from a normed space into its double
dual.

For base field `𝕜 = ℝ` or `𝕜 = ℂ`, this map is actually an isometric embedding; we provide a
version `normed_space.inclusion_in_double_dual_li` of the map which is of type a bundled linear
isometric embedding, `E →ₗᵢ[𝕜] (dual 𝕜 (dual 𝕜 E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `semi_normed_group` and we specialize to `normed_group` when needed.

## Main definitions

* `inclusion_in_double_dual` and `inclusion_in_double_dual_li` are the inclusion of a normed space
  in its double dual, considered as a bounded linear map and as a linear isometry, respectively.
* `polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals `x'` for which
  `∥x' z∥ ≤ 1` for every `z ∈ s`.

## Tags

dual
-/

noncomputable theory
open_locale classical topological_space
universes u v

namespace normed_space

section general
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (E : Type*) [semi_normed_group E] [normed_space 𝕜 E]
variables (F : Type*) [normed_group F] [normed_space 𝕜 F]

/-- The topological dual of a seminormed space `E`. -/
@[derive [inhabited, semi_normed_group, normed_space 𝕜]] def dual := E →L[𝕜] 𝕜

instance : add_monoid_hom_class (dual 𝕜 E) E 𝕜 := continuous_linear_map.add_monoid_hom_class

instance : has_coe_to_fun (dual 𝕜 E) (λ _, E → 𝕜) := continuous_linear_map.to_fun

instance : normed_group (dual 𝕜 F) := continuous_linear_map.to_normed_group

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

/-- The dual pairing as a bilinear form. -/
def dual_pairing : (dual 𝕜 E) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 := continuous_linear_map.coe_lm 𝕜

@[simp] lemma dual_pairing_apply {v : dual 𝕜 E} {x : E} : dual_pairing 𝕜 E v x = v x := rfl

lemma dual_pairing_separating_left : (dual_pairing 𝕜 E).separating_left :=
begin
  rw [linear_map.separating_left_iff_ker_eq_bot, linear_map.ker_eq_bot],
  exact continuous_linear_map.coe_injective,
end

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
  { obtain ⟨f, hf₁, hfx⟩ : ∃ f : E →L[𝕜] 𝕜, ∥f∥ = 1 ∧ f x = ∥x∥ := exists_dual_vector 𝕜 x h,
    calc ∥x∥ = ∥(∥x∥ : 𝕜)∥ : is_R_or_C.norm_coe_norm.symm
    ... = ∥f x∥ : by rw hfx
    ... ≤ M * ∥f∥ : hM f
    ... = M : by rw [hf₁, mul_one] }
end

lemma eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
norm_le_zero_iff.mp (norm_le_dual_bound 𝕜 x le_rfl (λ f, by simp [h f]))

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

section polar_sets

open metric set normed_space

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def polar (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  {E : Type*} [semi_normed_group E] [normed_space 𝕜 E] : set E → set (dual 𝕜 E) :=
(dual_pairing 𝕜 E).flip.polar

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables {E : Type*} [semi_normed_group E] [normed_space 𝕜 E]

lemma mem_polar_iff {x' : dual 𝕜 E} (s : set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ∥x' z∥ ≤ 1 := iff.rfl

@[simp] lemma polar_univ : polar 𝕜 (univ : set E) = {(0 : dual 𝕜 E)} :=
(dual_pairing 𝕜 E).flip.polar_univ
  (linear_map.flip_separating_right.mpr (dual_pairing_separating_left 𝕜 E))

lemma is_closed_polar (s : set E) : is_closed (polar 𝕜 s) :=
begin
  dunfold normed_space.polar,
  simp only [linear_map.polar_eq_Inter, linear_map.flip_apply],
  refine is_closed_bInter (λ z hz, _),
  exact is_closed_Iic.preimage (continuous_linear_map.apply 𝕜 𝕜 z).continuous.norm
end

@[simp] lemma polar_closure (s : set E) : polar 𝕜 (closure s) = polar 𝕜 s :=
((dual_pairing 𝕜 E).flip.polar_antitone subset_closure).antisymm $
  (dual_pairing 𝕜 E).flip.polar_gc.l_le $
  closure_minimal ((dual_pairing 𝕜 E).flip.polar_gc.le_u_l s) $
  by simpa [linear_map.flip_flip]
    using (is_closed_polar _ _).preimage (inclusion_in_double_dual 𝕜 E).continuous

variables {𝕜}

/-- If `x'` is a dual element such that the norms `∥x' z∥` are bounded for `z ∈ s`, then a
small scalar multiple of `x'` is in `polar 𝕜 s`. -/
lemma smul_mem_polar {s : set E} {x' : dual 𝕜 E} {c : 𝕜}
  (hc : ∀ z, z ∈ s → ∥ x' z ∥ ≤ ∥c∥) : c⁻¹ • x' ∈ polar 𝕜 s :=
begin
  by_cases c_zero : c = 0, { simp only [c_zero, inv_zero, zero_smul],
    exact (dual_pairing 𝕜 E).flip.zero_mem_polar _ },
  have eq : ∀ z, ∥ c⁻¹ • (x' z) ∥ = ∥ c⁻¹ ∥ * ∥ x' z ∥ := λ z, norm_smul c⁻¹ _,
  have le : ∀ z, z ∈ s → ∥ c⁻¹ • (x' z) ∥ ≤ ∥ c⁻¹ ∥ * ∥ c ∥,
  { intros z hzs,
    rw eq z,
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _), },
  have cancel : ∥ c⁻¹ ∥ * ∥ c ∥ = 1,
  by simp only [c_zero, norm_eq_zero, ne.def, not_false_iff,
                inv_mul_cancel, norm_inv],
  rwa cancel at le,
end

lemma polar_ball_subset_closed_ball_div {c : 𝕜} (hc : 1 < ∥c∥) {r : ℝ} (hr : 0 < r) :
  polar 𝕜 (ball (0 : E) r) ⊆ closed_ball (0 : dual 𝕜 E) (∥c∥ / r) :=
begin
  intros x' hx',
  rw mem_polar_iff at hx',
  simp only [polar, mem_set_of_eq, mem_closed_ball_zero_iff, mem_ball_zero_iff] at *,
  have hcr : 0 < ∥c∥ / r, from div_pos (zero_lt_one.trans hc) hr,
  refine continuous_linear_map.op_norm_le_of_shell hr hcr.le hc (λ x h₁ h₂, _),
  calc ∥x' x∥ ≤ 1 : hx' _ h₂
  ... ≤ (∥c∥ / r) * ∥x∥ : (inv_pos_le_iff_one_le_mul' hcr).1 (by rwa inv_div)
end

variables (𝕜)

lemma closed_ball_inv_subset_polar_closed_ball {r : ℝ} :
  closed_ball (0 : dual 𝕜 E) r⁻¹ ⊆ polar 𝕜 (closed_ball (0 : E) r) :=
λ x' hx' x hx,
calc ∥x' x∥ ≤ ∥x'∥ * ∥x∥ : x'.le_op_norm x
... ≤ r⁻¹ * r :
  mul_le_mul (mem_closed_ball_zero_iff.1 hx') (mem_closed_ball_zero_iff.1 hx)
    (norm_nonneg _) (dist_nonneg.trans hx')
... = r / r : inv_mul_eq_div _ _
... ≤ 1 : div_self_le_one r

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
lemma polar_closed_ball
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] {r : ℝ} (hr : 0 < r) :
  polar 𝕜 (closed_ball (0 : E) r) = closed_ball (0 : dual 𝕜 E) r⁻¹ :=
begin
  refine subset.antisymm _ (closed_ball_inv_subset_polar_closed_ball _),
  intros x' h,
  simp only [mem_closed_ball_zero_iff],
  refine continuous_linear_map.op_norm_le_of_ball hr (inv_nonneg.mpr hr.le) (λ z hz, _),
  simpa only [one_div] using linear_map.bound_of_ball_bound' hr 1 x'.to_linear_map h z
end

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar 𝕜 s` are bounded by a constant. -/
lemma bounded_polar_of_mem_nhds_zero {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  bounded (polar 𝕜 s) :=
begin
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ∥a∥ := normed_field.exists_one_lt_norm 𝕜,
  obtain ⟨r, r_pos, r_ball⟩ : ∃ (r : ℝ) (hr : 0 < r), ball 0 r ⊆ s :=
    metric.mem_nhds_iff.1 s_nhd,
  exact bounded_closed_ball.mono (((dual_pairing 𝕜 E).flip.polar_antitone r_ball).trans $
    polar_ball_subset_closed_ball_div ha r_pos)
end

end polar_sets

end normed_space
