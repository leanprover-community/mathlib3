/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.hahn_banach

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

instance : has_coe_to_fun (dual 𝕜 E) (λ _, E → 𝕜) := continuous_linear_map.to_fun

instance : normed_group (dual 𝕜 F) := continuous_linear_map.to_normed_group

instance : normed_space 𝕜 (dual 𝕜 F) := continuous_linear_map.to_normed_space

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
    calc ∥x∥ = ∥norm' 𝕜 x∥ : (norm_norm' _ _ _).symm
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
    apply le_cInf continuous_linear_map.bounds_nonempty,
    rintros c ⟨hc1, hc2⟩,
    exact norm_le_dual_bound 𝕜 x hc1 hc2
  end,
  .. inclusion_in_double_dual 𝕜 E }

end bidual_isometry

end normed_space
