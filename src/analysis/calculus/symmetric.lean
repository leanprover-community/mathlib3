/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.deriv
import analysis.convex.topology
import analysis.calculus.mean_value

/-!
# Symmetry of the second derivative

-/

open asymptotics set
open_locale topological_space

section
variables {E F : Type*} [normed_group E] [normed_space ℝ E]
[normed_group F] [normed_space ℝ F]
{s : set E}
(s_conv : convex s)
{f : E → F} {f' : E → (E →L[ℝ] F)} {f'' : E →L[ℝ] (E →L[ℝ] F)}
(hf : ∀ x ∈ interior s, has_fderiv_at f (f' x) x)
{x : E} (xs : x ∈ s) (hx : has_fderiv_within_at f' f'' (interior s) x)

include s_conv xs hx hf

lemma taylor_approx_two_segment (v w : E) (hv : x + v ∈ interior s) (hw : x + v + w ∈ interior s) :
  is_o (λ (h : ℝ), f (x + h • v + h • w) - f (x + h • v) - h • f' x w
    - h^2 • f'' v w - (h^2/2) • f'' w w) (λ h, h^2) (𝓝[Ioi (0 : ℝ)] 0) :=
begin
  -- it suffices to check that the expression is bounded by `ε * ((∥v∥ + ∥w∥) * ∥w∥) * h^2` for
  -- small enough `h`, for any positive `ε`.
  apply is_o.trans_is_O (is_o_iff.2 (λ ε εpos, _)) (is_O_const_mul_self ((∥v∥ + ∥w∥) * ∥w∥) _ _),
  -- consider a ball of radius `δ` around `x` in which the Taylor approximation for `f''` is
  -- good up to `δ`.
  rw [has_fderiv_within_at, has_fderiv_at_filter, is_o_iff] at hx,
  rcases metric.mem_nhds_within_iff.1 (hx εpos) with ⟨δ, δpos, sδ⟩,
  have E1 : ∀ᶠ h in 𝓝[Ioi (0:ℝ)] 0, h * (∥v∥ + ∥w∥) < δ,
  { have : filter.tendsto (λ h, h * (∥v∥ + ∥w∥)) (𝓝[Ioi (0:ℝ)] 0) (𝓝 (0 * (∥v∥ + ∥w∥))) :=
      (continuous_id.mul continuous_const).continuous_within_at,
    apply (tendsto_order.1 this).2 δ,
    simpa using δpos },
  have E2 : ∀ᶠ h in 𝓝[Ioi (0:ℝ)] 0, (h : ℝ) < 1 :=
    mem_nhds_within_Ioi_iff_exists_Ioo_subset.2 ⟨(1 : ℝ), by simp, λ x hx, hx.2⟩,
  filter_upwards [E1, E2, self_mem_nhds_within],
  -- we consider `h` small enough that all points under consideration belong to this ball,
  -- and also with `0 < h < 1`.
  assume h hδ h_lt_1 hpos,
  replace hpos : 0 < h := hpos,
  let g := λ t, f (x + h • v + (t * h) • w) - (t * h) • f' x w  - (t * h^2) • f'' v w
    - ((t * h)^2/2) • f'' w w,
  set g' := λ t, f' (x + h • v + (t * h) • w) (h • w) - h • f' x w
    - h^2 • f'' v w - (t * h^2) • f'' w w with hg',
  have xt_mem : ∀ t ∈ Icc (0 : ℝ) 1, x + h • v + (t * h) • w ∈ interior s,
  { assume t ht,
    have : x + h • v ∈ interior s :=
      s_conv.add_smul_mem_interior xs hv ⟨hpos, h_lt_1.le⟩,
    rw [← smul_smul],
    apply s_conv.interior.add_smul_mem this _ ht,
    rw add_assoc at hw,
    convert s_conv.add_smul_mem_interior xs hw ⟨hpos, h_lt_1.le⟩ using 1,
    simp only [add_assoc, smul_add] },
  have g_deriv : ∀ t ∈ Icc (0 : ℝ) 1, has_deriv_within_at g (g' t) (Icc 0 1) t,
  { assume t ht,
    apply_rules [has_deriv_within_at.sub, has_deriv_within_at.add],
    { refine (hf _ _).comp_has_deriv_within_at _ _,
      { exact xt_mem t ht },
      apply has_deriv_at.has_deriv_within_at,
      suffices : has_deriv_at (λ u, x + h • v + (u * h) • w) (0 + 0 + (1 * h) • w) t,
        by simpa only [one_mul, zero_add],
      apply_rules [has_deriv_at.add, has_deriv_at_const, has_deriv_at.smul_const,
        has_deriv_at_id'] },
    { suffices : has_deriv_within_at (λ u, (u * h) • f' x w) ((1 * h) • f' x w) (Icc 0 1) t,
        by simpa only [one_mul],
      apply_rules [has_deriv_at.has_deriv_within_at, has_deriv_at.smul_const, has_deriv_at_id'] },
    { suffices : has_deriv_within_at (λ u, (u * h ^ 2) • f'' v w) ((1 * h^2) • f'' v w) (Icc 0 1) t,
        by simpa only [one_mul],
      apply_rules [has_deriv_at.has_deriv_within_at, has_deriv_at.smul_const, has_deriv_at_id'] },
    { suffices H : has_deriv_within_at (λ u, ((u * h) ^ 2 / 2) • f'' w w)
        (((((2 : ℕ) : ℝ) * (t * h) ^ (2  - 1) * (1 * h))/2) • f'' w w) (Icc 0 1) t,
      { convert H using 2,
        simp only [one_mul, nat.cast_bit0, pow_one, nat.cast_one],
        ring },
      apply_rules [has_deriv_at.has_deriv_within_at, has_deriv_at.smul_const, has_deriv_at_id',
        has_deriv_at.pow] } },
  have g'_bound : ∀ t ∈ Ico (0 : ℝ) 1, ∥g' t∥ ≤ ε * ((∥v∥ + ∥w∥) * ∥w∥) * h^2,
  { assume t ht,
    have I : ∥h • v + (t * h) • w∥ ≤ h * (∥v∥ + ∥w∥) := calc
      ∥h • v + (t * h) • w∥ ≤ ∥h • v∥ + ∥(t * h) • w∥ : norm_add_le _ _
      ... = h * ∥v∥ + t * (h * ∥w∥) :
        by simp only [norm_smul, real.norm_eq_abs, hpos.le, abs_of_nonneg, abs_mul, ht.left,
                      mul_assoc]
      ... ≤ h * ∥v∥ + 1 * (h * ∥w∥) :
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right ht.2.le
          (mul_nonneg hpos.le (norm_nonneg _)))
      ... = h * (∥v∥ + ∥w∥) : by ring,
    calc ∥g' t∥ = ∥(f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)) (h • w)∥ :
    begin
      rw hg',
      have : h * (t * h) = t * (h * h), by ring,
      simp only [continuous_linear_map.coe_sub', continuous_linear_map.map_add, pow_two,
        continuous_linear_map.add_apply, pi.smul_apply, smul_sub, smul_add, smul_smul, ← sub_sub,
        continuous_linear_map.coe_smul', pi.sub_apply, continuous_linear_map.map_smul, this]
    end
    ... ≤ ∥f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)∥ * ∥h • w∥ :
      continuous_linear_map.le_op_norm _ _
    ... ≤ (ε * ∥h • v + (t * h) • w∥) * (∥h • w∥) :
    begin
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      suffices H : x + h • v + (t * h) • w ∈ metric.ball x δ ∩ interior s,
      { have := sδ H,
        simp only [mem_set_of_eq] at this,
        convert this;
        abel },
      refine ⟨_, xt_mem t ⟨ht.1, ht.2.le⟩⟩,
      rw [add_assoc, add_mem_ball_iff_norm],
      exact I.trans_lt hδ
    end
    ... ≤ (ε * (∥h • v∥ + ∥h • w∥)) * (∥h • w∥) :
    begin
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      apply mul_le_mul_of_nonneg_left _ (εpos.le),
      apply (norm_add_le _ _).trans,
      refine add_le_add (le_refl _) _,
      simp only [norm_smul, real.norm_eq_abs, abs_mul, abs_of_nonneg, ht.1, hpos.le, mul_assoc],
      exact mul_le_of_le_one_left (mul_nonneg hpos.le (norm_nonneg _)) ht.2.le,
    end
    ... = ε * ((∥v∥ + ∥w∥) * ∥w∥) * h^2 :
      by { simp only [norm_smul, real.norm_eq_abs, abs_mul, abs_of_nonneg, hpos.le], ring } },
  have I : ∥g 1 - g 0∥ ≤ ε * ((∥v∥ + ∥w∥) * ∥w∥) * h^2, by simpa using
    norm_image_sub_le_of_norm_deriv_le_segment' g_deriv g'_bound 1 (right_mem_Icc.2 zero_le_one),
  convert I using 1,
  { congr' 1,
    dsimp only [g],
    simp only [nat.one_ne_zero, add_zero, one_mul, zero_div, zero_mul, sub_zero, zero_smul,
      ne.def, not_false_iff, bit0_eq_zero, zero_pow'],
    abel },
  { simp only [real.norm_eq_abs, abs_mul, add_nonneg (norm_nonneg v) (norm_nonneg w),
      abs_of_nonneg, mul_assoc, pow_bit0_abs, norm_nonneg, abs_pow] }
end


end
