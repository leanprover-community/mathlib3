/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.abs_max

/-!
-/

open set function filter asymptotics complex metric
open_locale topological_space filter real

local notation `expR` := real.exp

namespace phragmen_lindelof

variables {ι E : Type*} [normed_group E] [normed_space ℂ E]

lemma horizontal_strip_pi_div_two {C : ℝ} {f : ℂ → E}
  (hd : diff_cont_on_cl ℂ f (im ⁻¹' Ioo (-(π / 2)) (π / 2)))
  (hB : ∃ (c ∈ Ico 0 (1 : ℝ)) A, ∀ z : ℂ, |z.im| < π / 2 → ∥f z∥ ≤ expR (A * expR (c * |z.re|)))
  (hle : ∀ z : ℂ, |z.im| = (π / 2) → ∥f z∥ ≤ C) {z : ℂ} (hz : |z.im| ≤ π / 2) :
  ∥f z∥ ≤ C :=
begin
  -- WLOG, `0 < C`.
  have hπ2 : 0 < π / 2, from div_pos real.pi_pos two_pos,
  have hπ : -(π / 2) < π / 2, from neg_lt_self hπ2,
  suffices : ∀ C' : ℝ, 0 < C' → (∀ w : ℂ, |w.im| = (π / 2) → ∥f w∥ ≤ C') → ∥f z∥ ≤ C',
  { refine le_of_forall_le_of_dense (λ C' hC', this C' _ $ λ w hw, (hle w hw).trans hC'.le),
    refine ((norm_nonneg (f (↑(π / 2) * I))).trans (hle _ _)).trans_lt hC',
    rwa [of_real_mul_im, I_im, mul_one, abs_of_pos] },
  clear_dependent C, intros C hC₀ hle,
  -- Choose some `c A : ℝ` satisfying `hB`, then choose `b ∈ (c, 1)`.
  rcases hB with ⟨c, ⟨hc₀, hc₁⟩, A, Hle⟩,
  rcases exists_between hc₁ with ⟨b, hcb, hb₁⟩,
  have hb₀ : 0 < b, from hc₀.trans_lt hcb,
  have hbπ : 0 < b * (π / 2), from mul_pos hb₀ hπ2,
  have hbπ' : b * (π / 2) < π / 2, from (mul_lt_iff_lt_one_left hπ2).2 hb₁,
  /- Put `g ε w = exp (-ε * (exp (b * w) + exp (-b * w)))`. We're only interested in `ε > 0`
  and `w` from our strip. -/
  set g : ℝ → ℂ → ℂ := λ ε w, exp (-ε * (exp (b * w) + exp (-b * w))),
  /- Since `g ε z → 1` as `ε → 0`, it suffices to prove that `∥g ε z • f z∥ ≤ C`
  for all positive `ε`. -/
  suffices : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∥g ε z • f z∥ ≤ C,
  { refine le_of_tendsto (tendsto.mono_left _ nhds_within_le_nhds) this,
    refine ((continuous_of_real.neg.mul continuous_const).cexp.smul
      continuous_const).norm.tendsto' _ _ _,
    simp },
  filter_upwards [self_mem_nhds_within] with ε ε₀, change 0 < ε at ε₀,
  -- An upper estimate on `∥g ε w∥` that will be used in two branches of the proof.
  obtain ⟨δ, δ₀, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ {w : ℂ}, |w.im| ≤ π / 2 →
    abs (g ε w) ≤ expR (-δ * expR (b * |w.re|)),
  { have hcos₀ : 0 < real.cos (b * (π / 2)),
      from real.cos_pos_of_mem_Ioo (abs_lt.1 $ (abs_of_pos hbπ).symm ▸ hbπ'),
    refine ⟨ε * real.cos (b * (π / 2)), mul_pos ε₀ hcos₀, _⟩,
    intros w hw,
    calc abs (g ε w)
        = expR (-ε * (expR (b * w.re) + expR (-b * w.re)) * real.cos (b * w.im)) :
      by simp only [abs_exp, ← of_real_neg, of_real_mul_re, add_re, exp_re, of_real_mul_im,
        neg_mul b w.im, real.cos_neg, mul_assoc, add_mul]
    ... ≤ expR (-(ε * real.cos (b * (π / 2))) * expR (b * |w.re|)) : _,
    simp only [real.exp_le_exp, neg_mul, neg_le_neg_iff, mul_assoc, mul_le_mul_left ε₀],
    rw mul_comm,
    have hexp : expR (b * |w.re|) ≤ expR (b * w.re) + expR (-(b * w.re)),
    { cases le_total w.re 0 with hw hw,
      { rw [abs_of_nonpos hw, mul_neg],
        exact le_add_of_nonneg_left (real.exp_pos _).le },
      { rw [_root_.abs_of_nonneg hw],
        exact le_add_of_nonneg_right (real.exp_pos _).le } },
    have hcos : real.cos (b * (π / 2)) ≤ real.cos (b * w.im),
    { rw [← real.cos_abs (b * w.im)],
      refine real.cos_le_cos_of_nonneg_of_le_pi (_root_.abs_nonneg _) _ _,
      { exact hbπ'.le.trans (half_le_self real.pi_pos.le) },
      { rw [_root_.abs_mul, abs_of_pos hb₀],
        exact mul_le_mul_of_nonneg_left hw hb₀.le } },
    exact mul_le_mul hexp hcos hcos₀.le ((real.exp_pos _).le.trans hexp) },
  -- `abs (g ε w) ≤ 1` whenever `ε` is nonnegative and `|w.im| = π / 2`
  have hg₁ : ∀ (w : ℂ), |w.im| = π / 2 → abs (g ε w) ≤ 1,
  { intros w hw,
    refine (hδ hw.le).trans (real.exp_le_one_iff.2 _),
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 δ₀.le) (real.exp_pos _).le },
  obtain ⟨R, hzR, hR⟩ : ∃ R : ℝ, |z.re| < R ∧ ∀ w : ℂ, |w.re| = R → |w.im| < π / 2 →
    ∥g ε w • f w∥ ≤ C,
  { refine ((eventually_gt_at_top _).and _).exists,
    suffices : tendsto (λ R, expR (-δ * expR (b * R) + A * expR (c * R))) at_top (𝓝 0),
    { refine (this.eventually (ge_mem_nhds hC₀)).mono (λ R hR w hre him, _),
      calc ∥g ε w • f w∥ ≤ expR (-δ * expR (b * R) + A * expR (c * R)) : _
      ... ≤ C : hR,
      rw [norm_smul, real.exp_add, ← hre],
      exact mul_le_mul (hδ him.le) (Hle _ him) (norm_nonneg _) (real.exp_pos _).le },
    refine real.tendsto_exp_at_bot.comp _,
    clear_dependent C z g f,
    obtain ⟨c, hc, rfl⟩ : ∃ c' : ℝ, 0 < c' ∧ b - c' = c,
      from ⟨b - c, sub_pos.2 hcb, sub_sub_cancel _ _⟩,
    simp only [sub_mul, real.exp_sub, div_eq_inv_mul, real.exp_add, ← mul_assoc, ← add_mul],
    suffices : tendsto (λ R, -δ + A * (expR (c * R))⁻¹) at_top (𝓝 (-δ + A * 0)),
    { rw [mul_zero, add_zero] at this,
      exact tendsto.neg_mul_at_top (neg_lt_zero.2 δ₀) this
        (real.tendsto_exp_at_top.comp $ tendsto_const_nhds.mul_at_top hb₀ tendsto_id) },
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul _),
    exact tendsto_inv_at_top_zero.comp (real.tendsto_exp_at_top.comp $
      tendsto_const_nhds.mul_at_top hc tendsto_id) },
  have hR₀ : 0 < R, from (_root_.abs_nonneg _).trans_lt hzR,
  have hgd : differentiable ℂ (g ε),
    from (((differentiable_id.const_mul _).cexp.add
      (differentiable_id.const_mul _).cexp).const_mul _).cexp,
  replace hd : diff_cont_on_cl ℂ (λ w, g ε w • f w) ((Ioo (-R) R) ×ℂ Ioo (-(π / 2)) (π / 2)),
    from (hgd.diff_cont_on_cl.smul hd).mono (λ w hw, hw.2),
  convert norm_le_of_forall_mem_frontier_norm_le
    ((bounded_Ioo _ _).re_prod_im (bounded_Ioo _ _)) hd (λ w hw, _) _,
  { have hwc := frontier_subset_closure hw,
    rw [frontier_re_prod_im, closure_Ioo (neg_lt_self hR₀).ne, frontier_Ioo hπ,
      closure_Ioo hπ.ne, frontier_Ioo (neg_lt_self hR₀)] at hw,
    cases eq_or_ne (|w.im|) (π / 2) with him him,
    { rw [closure_re_prod_im, closure_Ioo (neg_lt_self hR₀).ne] at hwc,
      rw [norm_smul, ← one_mul C],
      exact mul_le_mul (hg₁ _ him) (hle _ him) (norm_nonneg _) zero_le_one },
    { replace hw : w ∈ {-R, R} ×ℂ Icc (-(π / 2)) (π / 2),
      { rw [ne.def, abs_eq hπ2.le] at him,
        exact hw.resolve_left (λ h, him (or.symm h.right)) },
      exact hR _ ((abs_eq hR₀.le).2 (or.symm hw.1)) ((abs_le.2 hw.2).lt_of_ne him) } },
  { rw [closure_re_prod_im, closure_Ioo hπ.ne, closure_Ioo (neg_lt_self hR₀).ne],
    exact ⟨abs_le.1 hzR.le, abs_le.1 hz⟩ }
end

lemma horizontal_strip {a b C : ℝ} {f : ℂ → E}
  (hd : diff_cont_on_cl ℂ f (im ⁻¹' Ioo a b))
  (hB : ∃ (c ∈ Ico 0 (π / (b - a))) A, ∀ z : ℂ, z.im ∈ Ioo a b →
    ∥f z∥ ≤ expR (A * expR (c * |z.re|)))
  (hle : ∀ z : ℂ, (z.im = a ∨ z.im = b) → ∥f z∥ ≤ C) {z : ℂ} (hz : z.im ∈ Icc a b) :
  ∥f z∥ ≤ C :=
begin
  -- If `z.im = a` or `z.im = b`, then apply `hle`, otherwise `z.im ∈ Ioo a b`
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hz with (hz|hz|hz'),
  { exact hle z (or.inl hz) }, { exact hle z (or.inr hz) }, clear hz, rename hz' hz,
  obtain ⟨a, b, ha, rfl, rfl⟩ :
    ∃ a' b' : ℝ, 0 < a' ∧ a' * -(π / 2) + b' = a ∧ a' * (π / 2) + b' = b,
  { refine ⟨(b - a) / π, (a + b) / 2, div_pos (sub_pos.2 (hz.1.trans hz.2)) real.pi_pos, _, _⟩;
      { field_simp [real.pi_pos.ne'], ring } },
  have hlt_iff : ∀ {w : ℂ}, |w.im| < π / 2 ↔
    (a * w + I * b : ℂ).im ∈ Ioo (a * -(π / 2) + b) (a * (π / 2) + b),
  { intro w,
    rw [add_im, mul_comm I, of_real_mul_im, of_real_mul_im, I_im, mul_one, add_mem_Ioo_iff_left,
      add_sub_cancel, add_sub_cancel, mem_Ioo, mul_lt_mul_left ha, mul_lt_mul_left ha, abs_lt] },
  have heq_iff : ∀ {w : ℂ}, |w.im| = π / 2 ↔
    (a * w + I * b : ℂ).im ∈ ({a * -(π / 2) + b, a * (π / 2) + b} : set ℝ),
  { intro w,
    rw [add_im, mul_comm I, of_real_mul_im, of_real_mul_im, I_im, mul_one, mem_insert_iff,
      mem_singleton_iff, add_left_inj, add_left_inj, mul_right_inj' ha.ne', mul_right_inj' ha.ne',
      abs_eq (div_pos real.pi_pos two_pos).le, or_comm] },
  have hle_iff : ∀ {w : ℂ}, |w.im| ≤ π / 2 ↔
    (a * w + I * b : ℂ).im ∈ Icc (a * -(π / 2) + b) (a * (π / 2) + b),
  { intro w,
    rw [add_im, mul_comm I, of_real_mul_im, of_real_mul_im, I_im, mul_one, add_mem_Icc_iff_left,
      add_sub_cancel, add_sub_cancel, mem_Icc, mul_le_mul_left ha, mul_le_mul_left ha, abs_le] },
  obtain ⟨z, rfl⟩ : ∃ z' : ℂ, ↑a * z' + I * b = z,
  { use (z - I * b) / a,
    rw [mul_div_cancel' _ (of_real_ne_zero.2 ha.ne'), sub_add_cancel] },
  replace hz : |z.im| ≤ π / 2, from hle_iff.2 (Ioo_subset_Icc_self hz),
  set g : ℂ → E := λ w, f (a * w + I * b),
  change ∥g z∥ ≤ C,
  refine horizontal_strip_pi_div_two
    (hd.comp ((differentiable_id.const_mul _).add_const _).diff_cont_on_cl
      (λ z hz, hlt_iff.1 $ abs_lt.2 hz)) _ (λ w hw, hle _ (heq_iff.1 hw)) hz,
  rcases hB with ⟨c, hc, A, Hle⟩,
  rw [add_sub_add_right_eq_sub, mul_neg, sub_neg_eq_add, ← mul_add, add_halves,
    div_mul_left real.pi_pos.ne'] at hc,
  refine ⟨a * c, ⟨mul_nonneg ha.le hc.1, _⟩, A, λ w hw, _⟩,
  { rw [mem_Ico, lt_div_iff' ha] at hc, exact hc.2 },
  { convert Hle _ (hlt_iff.1 hw) using 4,
    rw [add_re, mul_comm I, of_real_mul_re, of_real_mul_re, I_re, mul_zero, add_zero,
      _root_.abs_mul, abs_of_pos ha, ← mul_assoc, mul_comm a] }
end

lemma eq_zero_on_horizontal_strip {a b : ℝ} {f : ℂ → E}
  (hd : diff_cont_on_cl ℂ f (im ⁻¹' Ioo a b))
  (hB : ∃ (c ∈ Ico 0 (π / (b - a))) A, ∀ z : ℂ, z.im ∈ Ioo a b →
    ∥f z∥ ≤ expR (A * expR (c * |z.re|)))
  (h₀ : ∀ z : ℂ, (z.im = a ∨ z.im = b) → f z = 0) {z : ℂ} (hz : z.im ∈ Icc a b) :
  f z = 0 :=
norm_le_zero_iff.1 $ horizontal_strip hd hB (λ z hz, norm_le_zero_iff.2 $ h₀ z hz) hz

lemma quadrant_I {C : ℝ} {f : ℂ → E} (hd : diff_cont_on_cl ℂ f (Ioi 0 ×ℂ Ioi 0))
  (hB : ∃ (c ∈ Ico (0 : ℝ) 2) A, ∀ z : ℂ, 0 < z.re → 0 < z.im → ∥f z∥ ≤ expR (A * (abs z) ^ c))
  (hre : ∀ x : ℝ, 0 ≤ x → ∥f x∥ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ∥f (x * I)∥ ≤ C) {z : ℂ}
  (hz : 0 ≤ z.re ∧ 0 ≤ z.im) :
  ∥f z∥ ≤ C :=
begin
  rcases eq_or_ne z 0 with rfl|hzne, { exact hre 0 le_rfl },
  obtain ⟨z, hz, rfl⟩ : ∃ ζ : ℂ, ζ.im ∈ Icc 0 (π / 2) ∧ exp ζ = z,
  { refine ⟨log z, _, exp_log hzne⟩,
    rw log_im,
    exact ⟨arg_nonneg_iff.2 hz.2, (arg_mem_Icc_neg_pi_div_two_pi_div_two.2 hz.1).2⟩ },
  clear hz hzne,
  change ∥(f ∘ exp) z∥ ≤ C,
  have : maps_to exp (im ⁻¹' Ioo 0 (π / 2)) (Ioi 0 ×ℂ Ioi 0),
  { intros z hz,
    rw [mem_re_prod_im, exp_re, exp_im, mem_Ioi, mem_Ioi],
    refine ⟨mul_pos (real.exp_pos _)
      (real.cos_pos_of_mem_Ioo ⟨(neg_lt_zero.2 $ div_pos real.pi_pos two_pos).trans hz.1, hz.2⟩),
      mul_pos (real.exp_pos _)
        (real.sin_pos_of_mem_Ioo ⟨hz.1, hz.2.trans (half_lt_self real.pi_pos)⟩)⟩ },
  refine horizontal_strip (hd.comp differentiable_exp.diff_cont_on_cl this) _ (λ w hw, _) hz,
  { rw [sub_zero, div_div_cancel' real.pi_pos.ne'],
    rcases hB with ⟨c, hc, A, Hle⟩,
    refine ⟨c, hc, max A 0, λ w hw, (Hle _ (this hw).1 (this hw).2).trans _⟩,
    rw [abs_exp, ← real.exp_mul, real.exp_le_exp, mul_comm _ c],
    exact mul_le_mul (le_max_left _ _)
      (real.exp_le_exp.2 $ mul_le_mul_of_nonneg_left (le_abs_self _) hc.1)
      (real.exp_pos _).le (le_max_right _ _) },
  { cases w with x y, rcases hw with (rfl : y = 0)|(rfl : y = π / 2),
    { rw [← of_real_def, comp_app, ← of_real_exp],
      exact hre _ (real.exp_pos _).le },
    { rw [mk_eq_add_mul_I, comp_app, exp_add_mul_I, ← of_real_cos, ← of_real_sin,
        real.cos_pi_div_two, real.sin_pi_div_two, of_real_zero, of_real_one, one_mul, zero_add,
        ← of_real_exp],
      exact him _ (real.exp_pos _).le } }
end

lemma quadrant_II {C : ℝ} {f : ℂ → E} (hd : diff_cont_on_cl ℂ f (Iio 0 ×ℂ Ioi 0))
  (hB : ∃ (c ∈ Ico (0 : ℝ) 2) A, ∀ z : ℂ, z.re < 0 → 0 < z.im → ∥f z∥ ≤ expR (A * (abs z) ^ c))
  (hre : ∀ x : ℝ, x ≤ 0 → ∥f x∥ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ∥f (x * I)∥ ≤ C) {z : ℂ}
  (hz : z.re ≤ 0 ∧ 0 ≤ z.im) :
  ∥f z∥ ≤ C :=
begin
  obtain ⟨z, rfl⟩ : ∃ z', z' * I = z, from ⟨z / I, div_mul_cancel _ I_ne_zero⟩,
  rw [mul_I_re, mul_I_im, neg_nonpos] at hz,
  change ∥(f ∘ (* I)) z∥ ≤ C,
  have H : maps_to (* I) (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Ioi 0),
  { intros w hw,
    simpa only [mem_re_prod_im, mul_I_re, mul_I_im, neg_lt_zero, mem_Iio] using hw.symm },
  refine quadrant_I (hd.comp (differentiable_id.mul_const _).diff_cont_on_cl H)
    _ him (λ x hx, _) hz.symm,
  { rcases hB with ⟨c, hc, A, Hle⟩,
    refine ⟨c, hc, A, λ w h₁ h₂, _⟩,
    simpa only [complex.abs_mul, abs_I, mul_one] using Hle _ (H ⟨h₁, h₂⟩).1 (H ⟨h₁, h₂⟩).2 },
  { rw [comp_app, mul_assoc, I_mul_I, mul_neg_one, ← of_real_neg],
    exact hre _ (neg_nonpos.2 hx) }
end

lemma quadrant_III {C : ℝ} {f : ℂ → E} (hd : diff_cont_on_cl ℂ f (Iio 0 ×ℂ Iio 0))
  (hB : ∃ (c ∈ Ico (0 : ℝ) 2) A, ∀ z : ℂ, z.re < 0 → z.im < 0 → ∥f z∥ ≤ expR (A * (abs z) ^ c))
  (hre : ∀ x : ℝ, x ≤ 0 → ∥f x∥ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ∥f (x * I)∥ ≤ C) {z : ℂ}
  (hz : z.re ≤ 0 ∧ z.im ≤ 0) :
  ∥f z∥ ≤ C :=
begin
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z, from ⟨-z, neg_neg z⟩,
  rw [neg_re, neg_im, neg_nonpos, neg_nonpos] at hz,
  change ∥(f ∘ has_neg.neg) z∥ ≤ C,
  have H : maps_to has_neg.neg (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Iio 0),
  { intros w hw,
    simpa only [mem_re_prod_im, neg_re, neg_im, neg_lt_zero, mem_Iio] using hw },
  refine quadrant_I (hd.comp differentiable_neg.diff_cont_on_cl H) _ (λ x hx, _) (λ x hx, _) hz,
  { rcases hB with ⟨c, hc, A, Hle⟩,
    refine ⟨c, hc, A, λ w h₁ h₂, _⟩,
    simpa only [comp_app, complex.abs_neg] using Hle _ (H ⟨h₁, h₂⟩).1 (H ⟨h₁, h₂⟩).2 },
  { rw [comp_app, ← of_real_neg],
    exact hre (-x) (neg_nonpos.2 hx) },
  { rw [comp_app, ← neg_mul, ← of_real_neg],
    exact him (-x) (neg_nonpos.2 hx) }
end

lemma quadrant_IV {C : ℝ} {f : ℂ → E} (hd : diff_cont_on_cl ℂ f (Ioi 0 ×ℂ Iio 0))
  (hB : ∃ (c ∈ Ico (0 : ℝ) 2) A, ∀ z : ℂ, 0 < z.re → z.im < 0 → ∥f z∥ ≤ expR (A * (abs z) ^ c))
  (hre : ∀ x : ℝ, 0 ≤ x → ∥f x∥ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ∥f (x * I)∥ ≤ C) {z : ℂ}
  (hz : 0 ≤ z.re ∧ z.im ≤ 0) :
  ∥f z∥ ≤ C :=
begin
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z, from ⟨-z, neg_neg z⟩,
  rw [neg_re, neg_im, neg_nonpos, neg_nonneg] at hz,
  change ∥(f ∘ has_neg.neg) z∥ ≤ C,
  have H : maps_to has_neg.neg (Iio 0 ×ℂ Ioi 0) (Ioi 0 ×ℂ Iio 0),
  { intros w hw,
    simpa only [mem_re_prod_im, neg_re, neg_im, neg_lt_zero, neg_pos, mem_Ioi, mem_Iio] using hw },
  refine quadrant_II (hd.comp differentiable_neg.diff_cont_on_cl H) _ (λ x hx, _) (λ x hx, _) hz,
  { rcases hB with ⟨c, hc, A, Hle⟩,
    refine ⟨c, hc, A, λ w h₁ h₂, _⟩,
    simpa only [comp_app, complex.abs_neg] using Hle _ (H ⟨h₁, h₂⟩).1 (H ⟨h₁, h₂⟩).2 },
  { rw [comp_app, ← of_real_neg],
    exact hre (-x) (neg_nonneg.2 hx) },
  { rw [comp_app, ← neg_mul, ← of_real_neg],
    exact him (-x) (neg_nonpos.2 hx) }
end

end phragmen_lindelof
