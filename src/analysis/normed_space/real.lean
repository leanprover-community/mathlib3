/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import analysis.normed_space.basic
import data.real.sqrt

/-!
# Real normed spaces

In this file we prove resuls about real normed vector spaces
-/

open filter metric function set
open_locale topology big_operators nnreal ennreal uniformity pointwise

variables {E : Type*} [seminormed_add_comm_group E]

lemma inv_norm_smul_mem_closed_unit_ball [normed_space ℝ E] (x : E) :
  ‖x‖⁻¹ • x ∈ closed_ball (0 : E) 1 :=
by simp only [mem_closed_ball_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
  div_self_le_one]

lemma norm_smul_of_nonneg [normed_space ℝ E] {t : ℝ} (ht : 0 ≤ t) (x : E) :
  ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ht]

theorem closure_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  closure (ball x r) = closed_ball x r :=
begin
  refine subset.antisymm closure_ball_subset_closed_ball (λ y hy, _),
  have : continuous_within_at (λ c : ℝ, c • (y - x) + x) (Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuous_within_at,
  convert this.mem_closure _ _,
  { rw [one_smul, sub_add_cancel] },
  { simp [closure_Ico zero_ne_one, zero_le_one] },
  { rintros c ⟨hc0, hc1⟩,
    rw [mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, real.norm_eq_abs,
      abs_of_nonneg hc0, mul_comm, ← mul_one r],
    rw [mem_closed_ball, dist_eq_norm] at hy,
    replace hr : 0 < r, from ((norm_nonneg _).trans hy).lt_of_ne hr.symm,
    apply mul_lt_mul'; assumption }
end

theorem frontier_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  frontier (ball x r) = sphere x r :=
begin
  rw [frontier, closure_ball x hr, is_open_ball.interior_eq],
  ext x, exact (@eq_iff_le_not_lt ℝ _ _ _).symm
end

theorem interior_closed_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  interior (closed_ball x r) = ball x r :=
begin
  cases hr.lt_or_lt with hr hr,
  { rw [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty] },
  refine subset.antisymm _ ball_subset_interior_closed_ball,
  intros y hy,
  rcases (mem_closed_ball.1 $ interior_subset hy).lt_or_eq with hr|rfl, { exact hr },
  set f : ℝ → E := λ c : ℝ, c • (y - x) + x,
  suffices : f ⁻¹' closed_ball x (dist y x) ⊆ Icc (-1) 1,
  { have hfc : continuous f := (continuous_id.smul continuous_const).add continuous_const,
    have hf1 : (1:ℝ) ∈ f ⁻¹' (interior (closed_ball x $ dist y x)), by simpa [f],
    have h1 : (1:ℝ) ∈ interior (Icc (-1:ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1),
    contrapose h1,
    simp },
  intros c hc,
  rw [mem_Icc, ← abs_le, ← real.norm_eq_abs, ← mul_le_mul_right hr],
  simpa [f, dist_eq_norm, norm_smul] using hc
end

theorem frontier_closed_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball x hr,
  closed_ball_diff_ball]

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`homeomorph_unit_ball_apply_coe` and `homeomorph_unit_ball_symm_apply` as `@[simp]`.

See also `cont_diff_homeomorph_unit_ball` and `cont_diff_on_homeomorph_unit_ball_symm` for
smoothness properties that hold when `E` is an inner-product space. -/
@[simps { attrs := [] }]
noncomputable def homeomorph_unit_ball [normed_space ℝ E] :
  E ≃ₜ ball (0 : E) 1 :=
{ to_fun := λ x, ⟨(1 + ‖x‖^2).sqrt⁻¹ • x, begin
    have : 0 < 1 + ‖x‖ ^ 2, by positivity,
    rw [mem_ball_zero_iff, norm_smul, real.norm_eq_abs, abs_inv, ← div_eq_inv_mul,
      div_lt_one (abs_pos.mpr $ real.sqrt_ne_zero'.mpr this), ← abs_norm_eq_norm x, ← sq_lt_sq,
      abs_norm_eq_norm, real.sq_sqrt this.le],
    exact lt_one_add _,
  end⟩,
  inv_fun := λ y, (1 - ‖(y : E)‖^2).sqrt⁻¹ • (y : E),
  left_inv := λ x,
  by field_simp [norm_smul, smul_smul, (zero_lt_one_add_norm_sq x).ne',
    real.sq_sqrt (zero_lt_one_add_norm_sq x).le, ← real.sqrt_div (zero_lt_one_add_norm_sq x).le],
  right_inv := λ y,
  begin
    have : 0 < 1 - ‖(y : E)‖ ^ 2 :=
      by nlinarith [norm_nonneg (y : E), (mem_ball_zero_iff.1 y.2 : ‖(y : E)‖ < 1)],
    field_simp [norm_smul, smul_smul, this.ne', real.sq_sqrt this.le, ← real.sqrt_div this.le],
  end,
  continuous_to_fun :=
  begin
    suffices : continuous (λ x, (1 + ‖x‖^2).sqrt⁻¹), from (this.smul continuous_id).subtype_mk _,
    refine continuous.inv₀ _ (λ x, real.sqrt_ne_zero'.mpr (by positivity)),
    continuity,
  end,
  continuous_inv_fun :=
  begin
    suffices : ∀ (y : ball (0 : E) 1), (1 - ‖(y : E)‖ ^ 2).sqrt ≠ 0, { continuity, },
    intros y,
    rw real.sqrt_ne_zero',
    nlinarith [norm_nonneg (y : E), (mem_ball_zero_iff.1 y.2 : ‖(y : E)‖ < 1)],
  end }

@[simp] lemma coe_homeomorph_unit_ball_apply_zero [normed_space ℝ E] :
  (homeomorph_unit_ball (0 : E) : E) = 0 :=
by simp [homeomorph_unit_ball]

section surj

variables (E) [normed_space ℝ E] [nontrivial E]

lemma exists_norm_eq {c : ℝ} (hc : 0 ≤ c) : ∃ x : E, ‖x‖ = c :=
begin
  rcases exists_ne (0 : E) with ⟨x, hx⟩,
  rw ← norm_ne_zero_iff at hx,
  use c • ‖x‖⁻¹ • x,
  simp [norm_smul, real.norm_of_nonneg hc, hx]
end

@[simp] lemma range_norm : range (norm : E → ℝ) = Ici 0 :=
subset.antisymm (range_subset_iff.2 norm_nonneg) (λ _, exists_norm_eq E)

lemma nnnorm_surjective : surjective (nnnorm : E → ℝ≥0) :=
λ c, (exists_norm_eq E c.coe_nonneg).imp $ λ x h, nnreal.eq h

@[simp] lemma range_nnnorm : range (nnnorm : E → ℝ≥0) = univ :=
(nnnorm_surjective E).range_eq

end surj

theorem interior_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  interior (closed_ball x r) = ball x r :=
begin
  rcases eq_or_ne r 0 with rfl|hr,
  { rw [closed_ball_zero, ball_zero, interior_singleton] },
  { exact interior_closed_ball x hr }
end

theorem frontier_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]
