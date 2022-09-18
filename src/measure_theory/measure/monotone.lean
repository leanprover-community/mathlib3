/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.deriv
import measure_theory.covering.differentiation
import measure_theory.covering.vitali


/-!
# Differentiability of monotone functions

We show that a monotone function `f : ℝ → ℝ` is differentiable almost everywhere, in
`monotone.ae_differentiable_at`.

If the function `f` is continuous, this follows directly from general differentiation of measure
theorems. Let `μ` be the Stieltjes measure associated to `f`. Then, almost everywhere,
`μ [x, y] / (y - x)` (resp. `μ [y, x] / (x - y)`) converges to the Radon-Nikodym derivative of `μ`
with respect to Lebesgue when `y` tends to `x` in `(x, +∞)` (resp. `(-∞, x)`), by
`vitali_family.ae_tendsto_rn_deriv`. As `μ [x, y] = f y - f x`, this gives differentiability right
away.

When `f` is only monotone, the same argument works up to small adjustments, as the associated
Stieltjes measure satisfies `μ [x, y] = f (y^+) - f (x^-)` (the right and left limits of `f` at `y`
and `x` respectively). One argues that `f (x^-) = f x` almost everywhere (in fact away from a
countable set), and moreover `f ((y - (y-x)^2)^+) ≤ f y ≤ f (y^+)`. This is enough to deduce the
limit of `(f y - f x) / (y - x)` by a lower and upper approximation argument from the known
behavior of `μ [x, y]`.
-/

open set filter function metric measure_theory measure_theory.measure topological_space
open_locale nnreal ennreal topological_space

namespace real

/-- A Vitali family over `ℝ`, designed so that at `x` it contains the intervals containing `x`.-/
protected noncomputable def vitali_family : vitali_family (volume : measure ℝ) :=
begin
  refine vitali.vitali_family (volume : measure ℝ) (6 : ℝ≥0)
    (λ x ε εpos, ⟨ε, ⟨εpos, le_refl _⟩, _⟩),
  have : (0 : ℝ) ≤ 6, by norm_num,
  simp [ennreal.of_real_mul, this, ← mul_assoc, mul_comm _ (2 : ℝ≥0∞)],
end

lemma Icc_mem_vitali_family_at_right {x y : ℝ} (hxy : x < y) :
  Icc x y ∈ real.vitali_family.sets_at x :=
begin
  have H : ennreal.of_real (2 * (3 * metric.diam (Icc x y))) ≤ 6 * ennreal.of_real (y - x),
  { simp only [ennreal.of_real_mul, zero_le_three, real.diam_Icc hxy.le, ←mul_assoc,
      zero_le_mul_left, zero_lt_bit0, zero_lt_one, zero_le_bit0, zero_le_one,
      ennreal.of_real_bit0, ennreal.of_real_one, ennreal.of_real_bit1],
    apply ennreal.mul_le_mul _ (le_refl _),
    have : ennreal.of_real (2 * 3) ≤ ennreal.of_real 6,
      from ennreal.of_real_le_of_real (by norm_num),
    simpa [ennreal.of_real_mul] using this },
  simpa [real.vitali_family, vitali.vitali_family, hxy, hxy.le, is_closed_Icc] using H,
end

lemma tendsto_Icc_vitali_family_right (x : ℝ) :
  tendsto (λ y, Icc x y) (𝓝[>] x) (real.vitali_family.filter_at x) :=
begin
  apply vitali_family.tendsto_filter_at,
  { filter_upwards [self_mem_nhds_within] with y hy using Icc_mem_vitali_family_at_right hy },
  { assume ε εpos,
    have : x ∈ Ico x (x + ε) := ⟨le_refl _, by linarith⟩,
    filter_upwards [Icc_mem_nhds_within_Ioi this] with y hy,
    rw closed_ball_eq_Icc,
    exact Icc_subset_Icc (by linarith) hy.2 }
end

lemma Icc_mem_vitali_family_at_left {x y : ℝ} (hxy : x < y) :
  Icc x y ∈ real.vitali_family.sets_at y :=
begin
  have H : ennreal.of_real (2 * (3 * metric.diam (Icc x y))) ≤ 6 * ennreal.of_real (y - x),
  { simp only [ennreal.of_real_mul, zero_le_three, real.diam_Icc hxy.le, ←mul_assoc,
      zero_le_mul_left, zero_lt_bit0, zero_lt_one, zero_le_bit0, zero_le_one,
      ennreal.of_real_bit0, ennreal.of_real_one, ennreal.of_real_bit1],
    apply ennreal.mul_le_mul _ (le_refl _),
    have : ennreal.of_real (2 * 3) ≤ ennreal.of_real 6,
      from ennreal.of_real_le_of_real (by norm_num),
    simpa [ennreal.of_real_mul] using this },
  simpa [real.vitali_family, vitali.vitali_family, hxy, hxy.le, is_closed_Icc] using H,
end

lemma tendsto_Icc_vitali_family_left (x : ℝ) :
  tendsto (λ y, Icc y x) (𝓝[<] x) (real.vitali_family.filter_at x) :=
begin
  apply vitali_family.tendsto_filter_at,
  { filter_upwards [self_mem_nhds_within] with y hy using Icc_mem_vitali_family_at_left hy },
  { assume ε εpos,
    have : x ∈ Ioc (x - ε) x := ⟨by linarith, le_refl _⟩,
    filter_upwards [Icc_mem_nhds_within_Iio this] with y hy,
    rw closed_ball_eq_Icc,
    exact Icc_subset_Icc hy.1 (by linarith) }
end

end real

/-- If `(f y - f x) / (y - x)` converges to a limit as `y` tends to `x`, then the same goes if
`y` is shifted a limit bit, i.e., `f (y + (y-x)^2) - f x) / (y - x)` converges to the same limit.
This lemma contains a slightly more general version of this statement (where one considers
convergence along some subfilter, typically `𝓝[<] x` or `𝓝[>] x`) tailored to the application
to almost everywhere differentiability of monotone functions. -/
lemma tendsto_apply_add_mul_sq_div_sub {f : ℝ → ℝ} {x a c d : ℝ} {l : filter ℝ} (hl : l ≤ 𝓝[≠] x)
  (hf : tendsto (λ y, (f y - d) / (y - x)) l (𝓝 a))
  (h' : tendsto (λ y, y + c * (y-x)^2) l l) :
  tendsto (λ y, (f (y + c * (y-x)^2) - d) / (y - x)) l (𝓝 a) :=
begin
  have L : tendsto (λ y, (y + c * (y - x)^2 - x) / (y - x)) l (𝓝 1),
  { have : tendsto (λ y, (1 + c * (y - x))) l (𝓝 (1 + c * (x - x))),
    { apply tendsto.mono_left _ (hl.trans nhds_within_le_nhds),
      exact ((tendsto_id.sub_const x).const_mul c).const_add 1 },
    simp only [_root_.sub_self, add_zero, mul_zero] at this,
    apply tendsto.congr' (eventually.filter_mono hl _) this,
    filter_upwards [self_mem_nhds_within] with y hy,
    field_simp [sub_ne_zero.2 hy],
    ring },
  have Z := (hf.comp h').mul L,
  rw mul_one at Z,
  apply tendsto.congr' _ Z,
  have : ∀ᶠ y in l, y + c * (y-x)^2 ≠ x := by apply tendsto.mono_right h' hl self_mem_nhds_within,
  filter_upwards [this] with y hy,
  field_simp [sub_ne_zero.2 hy],
end

lemma nhds_within_le_of_subset {α : Type*} [topological_space α] {s t : set α} (h : s ⊆ t) (x : α) :
  𝓝[s] x ≤ 𝓝[t] x :=
nhds_within_le_iff.2 (mem_of_superset self_mem_nhds_within h)

lemma nhds_within_Iio_le_nhds_within_ne {α : Type*} [preorder α] [topological_space α] (x : α) :
  𝓝[<] x ≤ 𝓝[≠] x :=
nhds_within_le_of_subset (λ y hy, ne_of_lt hy) x

lemma nhds_within_Ioi_le_nhds_within_ne {α : Type*} [preorder α] [topological_space α] (x : α) :
  𝓝[>] x ≤ 𝓝[≠] x :=
nhds_within_le_of_subset (λ y hy, ne_of_gt hy) x

lemma stieltjes_function.has_deriv_at (f : stieltjes_function) :
  ∀ᵐ x, has_deriv_at f (rn_deriv f.measure volume x).to_real x :=
begin
  /- Denote by `μ` the Stieltjes measure associated to `f`.
  The general theorem `vitali_family.ae_tendsto_rn_deriv` ensures that `μ [x, y] / (y - x)` tends
  to the Radon-Nikodym derivative as `y` tends to `x` from the right. As `μ [x, y] = f y - f (x^-)`
  and `f (x^-) = f x` almost everywhere, this gives differentiability on the right.
  On the left, `μ [y, x] / (x - y)` again tends to the Radon-Nikodym derivative.
  As `μ [y, x] = f x - f (y^-)`, this is not exactly the right result, so one uses a sandwiching
  argument to deduce the convergence for `(f x - f y) / (x - y)`. -/
  filter_upwards [vitali_family.ae_tendsto_rn_deriv real.vitali_family f.measure,
    rn_deriv_lt_top f.measure volume, f.countable_left_lim_ne.ae_not_mem volume] with x hx h'x h''x,
  -- Limit on the right, following from differentiation of measures
  have L1 : tendsto (λ y, (f y - f x) / (y - x))
    (𝓝[>] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (real.tendsto_Icc_vitali_family_right x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : x < y),
    simp only [comp_app, stieltjes_function.measure_Icc, real.volume_Icc, not_not.1 h''x],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real],
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le },
  -- Limit on the left, following from differentiation of measures. Its form is not exactly the one
  -- we need, due to the appearance of a left limit.
  have L2 : tendsto (λ y, (f.left_lim y - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (real.tendsto_Icc_vitali_family_left x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : y < x),
    simp only [comp_app, stieltjes_function.measure_Icc, real.volume_Icc],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real, ← neg_neg (y - x),
        div_neg, neg_div', neg_sub, neg_sub],
    exact div_nonneg (sub_nonneg.2 (f.left_lim_le hxy.le)) (sub_pos.2 hxy).le },
  -- Shifting a little bit the limit on the left, by `(y - x)^2`.
  have L3 : tendsto (λ y, (f.left_lim (y + 1 * (y - x)^2) - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto_apply_add_mul_sq_div_sub (nhds_within_Iio_le_nhds_within_ne x) L2,
    apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
    { apply tendsto.mono_left _ nhds_within_le_nhds,
      have : tendsto (λ (y : ℝ), y + 1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + 1 * (x - x)^2)) :=
        tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul 1),
      simpa using this },
    { have : Ioo (x - 1) x ∈ 𝓝[<] x,
      { apply Ioo_mem_nhds_within_Iio, exact ⟨by linarith, le_refl _⟩ },
      filter_upwards [this],
      rintros y ⟨hy : x - 1 < y, h'y : y < x⟩,
      rw mem_Iio,
      nlinarith } },
  -- Deduce the correct limit on the left, by sandwiching.
  have L4 : tendsto (λ y, (f y - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto_of_tendsto_of_tendsto_of_le_of_le' L3 L2,
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : y < x),
      refine div_le_div_of_nonpos_of_le (by linarith) ((sub_le_sub_iff_right _).2 _),
      apply f.le_left_lim,
      have : 0 < (x - y)^2 := sq_pos_of_pos (sub_pos.2 hy),
      linarith },
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : y < x),
      refine div_le_div_of_nonpos_of_le (by linarith) _,
      simpa only [sub_le_sub_iff_right] using f.left_lim_le (le_refl y) } },
  -- prove the result by splitting into left and right limits.
  rw [has_deriv_at_iff_tendsto_slope, slope_fun_def_field, ← nhds_left'_sup_nhds_right',
    tendsto_sup],
  exact ⟨L4, L1⟩
end


lemma monotone.ae_has_deriv_at {f : ℝ → ℝ} (hf : monotone f) :
  ∀ᵐ x, has_deriv_at f (rn_deriv hf.stieltjes_function.measure volume x).to_real x :=
begin
  filter_upwards [hf.stieltjes_function.has_deriv_at,
    hf.countable_not_continuous_at.ae_not_mem volume] with x hx h'x,
  have A : hf.stieltjes_function x = f x,
  { rw [not_not, ← hf.left_lim_eq_right_lim_iff_continuous_at] at h'x,
    apply le_antisymm _ (hf.le_right_lim (le_refl _)),
    rw ← h'x,
    exact hf.left_lim_le (le_refl _) },
  rw [has_deriv_at_iff_tendsto_slope, (nhds_left'_sup_nhds_right' x).symm, tendsto_sup,
    slope_fun_def_field, A] at hx,
  have L1 : tendsto (λ y, (f y - f x) / (y - x)) (𝓝[>] x)
     (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).to_real),
  { have : tendsto (λ y, (hf.stieltjes_function (y + (-1) * (y-x)^2) - f x) / (y - x)) (𝓝[>] x)
      (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).to_real),
    { apply tendsto_apply_add_mul_sq_div_sub (nhds_within_Ioi_le_nhds_within_ne x) hx.2,
      apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
      { apply tendsto.mono_left _ nhds_within_le_nhds,
        have : tendsto (λ (y : ℝ), y + (-1) * (y - x) ^ 2) (𝓝 x) (𝓝 (x + (-1) * (x - x)^2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1)),
        simpa using this },
      { have : Ioo x (x+1) ∈ 𝓝[>] x,
        { apply Ioo_mem_nhds_within_Ioi, exact ⟨le_refl _, by linarith⟩ },
        filter_upwards [this],
        rintros y ⟨hy : x < y, h'y : y < x + 1⟩,
        rw mem_Ioi,
        nlinarith } },
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' this hx.2,
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : x < y),
      have : 0 < (y - x)^2, from sq_pos_of_pos (sub_pos.2 hy),
      apply div_le_div_of_le_of_nonneg _ (sub_pos.2 hy).le,
      exact (sub_le_sub_iff_right _).2 (hf.right_lim_le (by linarith)) },
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : x < y),
      apply div_le_div_of_le_of_nonneg _ (sub_pos.2 hy).le,
      exact (sub_le_sub_iff_right _).2 (hf.le_right_lim (le_refl y)) } },
  have L2 : tendsto (λ y, (f y - f x) / (y - x)) (𝓝[<] x)
     (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).to_real),
  { have : tendsto (λ y, (hf.stieltjes_function (y + (-1) * (y-x)^2) - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).to_real),
    { apply tendsto_apply_add_mul_sq_div_sub (nhds_within_Iio_le_nhds_within_ne x) hx.1,
      apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
      { apply tendsto.mono_left _ nhds_within_le_nhds,
        have : tendsto (λ (y : ℝ), y + (-1) * (y - x) ^ 2) (𝓝 x) (𝓝 (x + (-1) * (x - x)^2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1)),
        simpa using this },
      { have : Ioo (x - 1) x ∈ 𝓝[<] x,
        { apply Ioo_mem_nhds_within_Iio, exact ⟨by linarith, le_refl _⟩ },
        filter_upwards [this],
        rintros y ⟨hy : x - 1 < y, h'y : y < x⟩,
        rw mem_Iio,
        nlinarith } },
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hx.1 this,
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : y < x),
      apply div_le_div_of_nonpos_of_le (sub_neg.2 hy).le,
      exact (sub_le_sub_iff_right _).2 (hf.le_right_lim (le_refl _)) },
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : y < x),
      have : 0 < (y - x)^2, from sq_pos_of_neg (sub_neg.2 hy),
      apply div_le_div_of_nonpos_of_le (sub_neg.2 hy).le,
      exact (sub_le_sub_iff_right _).2 (hf.right_lim_le (by linarith)) } },
  rw [has_deriv_at_iff_tendsto_slope, slope_fun_def_field, (nhds_left'_sup_nhds_right' x).symm,
    tendsto_sup],
  exact ⟨L2, L1⟩
end

/-- A monotone real function is differentiable Lebesgue-almost everywhere. -/
theorem monotone.ae_differentiable_at {f : ℝ → ℝ} (hf : monotone f) :
  ∀ᵐ x, differentiable_at ℝ f x :=
by filter_upwards [hf.ae_has_deriv_at] with x hx using hx.differentiable_at
