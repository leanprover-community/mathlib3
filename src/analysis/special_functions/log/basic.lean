/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.special_functions.exp

/-!
# Real logarithm

In this file we define `real.log` to be the logarithm of a real number. As usual, we extend it from
its domain `(0, +∞)` to a globally defined function. We choose to do it so that `log 0 = 0` and
`log (-x) = log x`.

We prove some basic properties of this function and show that it is continuous.

## Tags

logarithm, continuity
-/

open set filter function
open_locale topological_space
noncomputable theory

namespace real

variables {x y : ℝ}

/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot] noncomputable def log (x : ℝ) : ℝ :=
if hx : x = 0 then 0 else exp_order_iso.symm ⟨|x|, abs_pos.2 hx⟩

lemma log_of_ne_zero (hx : x ≠ 0) : log x = exp_order_iso.symm ⟨|x|, abs_pos.2 hx⟩ := dif_neg hx

lemma log_of_pos (hx : 0 < x) : log x = exp_order_iso.symm ⟨x, hx⟩ :=
by { rw [log_of_ne_zero hx.ne'], congr, exact abs_of_pos hx }

lemma exp_log_eq_abs (hx : x ≠ 0) : exp (log x) = |x| :=
by rw [log_of_ne_zero hx, ← coe_exp_order_iso_apply, order_iso.apply_symm_apply, subtype.coe_mk]

lemma exp_log (hx : 0 < x) : exp (log x) = x :=
by { rw exp_log_eq_abs hx.ne', exact abs_of_pos hx }

lemma exp_log_of_neg (hx : x < 0) : exp (log x) = -x :=
by { rw exp_log_eq_abs (ne_of_lt hx), exact abs_of_neg hx }

@[simp] lemma log_exp (x : ℝ) : log (exp x) = x :=
exp_injective $ exp_log (exp_pos x)

lemma surj_on_log : surj_on log (Ioi 0) univ :=
λ x _, ⟨exp x, exp_pos x, log_exp x⟩

lemma log_surjective : surjective log :=
λ x, ⟨exp x, log_exp x⟩

@[simp] lemma range_log : range log = univ :=
log_surjective.range_eq

@[simp] lemma log_zero : log 0 = 0 := dif_pos rfl

@[simp] lemma log_one : log 1 = 0 :=
exp_injective $ by rw [exp_log zero_lt_one, exp_zero]

@[simp] lemma log_abs (x : ℝ) : log (|x|) = log x :=
begin
  by_cases h : x = 0,
  { simp [h] },
  { rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs] }
end

@[simp] lemma log_neg_eq_log (x : ℝ) : log (-x) = log x :=
by rw [← log_abs x, ← log_abs (-x), abs_neg]

lemma surj_on_log' : surj_on log (Iio 0) univ :=
λ x _, ⟨-exp x, neg_lt_zero.2 $ exp_pos x, by rw [log_neg_eq_log, log_exp]⟩

lemma log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
exp_injective $
by rw [exp_log_eq_abs (mul_ne_zero hx hy), exp_add, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_mul]

lemma log_div (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y :=
exp_injective $
by rw [exp_log_eq_abs (div_ne_zero hx hy), exp_sub, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_div]

@[simp] lemma log_inv (x : ℝ) : log (x⁻¹) = -log x :=
begin
  by_cases hx : x = 0, { simp [hx] },
  rw [← exp_eq_exp, exp_log_eq_abs (inv_ne_zero hx), exp_neg, exp_log_eq_abs hx, abs_inv]
end

lemma log_le_log (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y :=
by rw [← exp_le_exp, exp_log h, exp_log h₁]

lemma log_lt_log (hx : 0 < x) : x < y → log x < log y :=
by { intro h, rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)] }

lemma log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y :=
by { rw [← exp_lt_exp, exp_log hx, exp_log hy] }

lemma log_le_iff_le_exp (hx : 0 < x) : log x ≤ y ↔ x ≤ exp y := by rw [←exp_le_exp, exp_log hx]

lemma log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x < exp y := by rw [←exp_lt_exp, exp_log hx]

lemma le_log_iff_exp_le (hy : 0 < y) : x ≤ log y ↔ exp x ≤ y := by rw [←exp_le_exp, exp_log hy]

lemma lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp x < y := by rw [←exp_lt_exp, exp_log hy]

lemma log_pos_iff (hx : 0 < x) : 0 < log x ↔ 1 < x :=
by { rw ← log_one, exact log_lt_log_iff zero_lt_one hx }

lemma log_pos (hx : 1 < x) : 0 < log x :=
(log_pos_iff (lt_trans zero_lt_one hx)).2 hx

lemma log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 :=
by { rw ← log_one, exact log_lt_log_iff h zero_lt_one }

lemma log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 := (log_neg_iff h0).2 h1

lemma log_nonneg_iff (hx : 0 < x) : 0 ≤ log x ↔ 1 ≤ x :=
by rw [← not_lt, log_neg_iff hx, not_lt]

lemma log_nonneg (hx : 1 ≤ x) : 0 ≤ log x :=
(log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx

lemma log_nonpos_iff (hx : 0 < x) : log x ≤ 0 ↔ x ≤ 1 :=
by rw [← not_lt, log_pos_iff hx, not_lt]

lemma log_nonpos_iff' (hx : 0 ≤ x) : log x ≤ 0 ↔ x ≤ 1 :=
begin
  rcases hx.eq_or_lt with (rfl|hx),
  { simp [le_refl, zero_le_one] },
  exact log_nonpos_iff hx
end

lemma log_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0 :=
(log_nonpos_iff' hx).2 h'x

lemma strict_mono_on_log : strict_mono_on log (set.Ioi 0) :=
λ x hx y hy hxy, log_lt_log hx hxy

lemma strict_anti_on_log : strict_anti_on log (set.Iio 0) :=
begin
  rintros x (hx : x < 0) y (hy : y < 0) hxy,
  rw [← log_abs y, ← log_abs x],
  refine log_lt_log (abs_pos.2 hy.ne) _,
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
end

lemma log_inj_on_pos : set.inj_on log (set.Ioi 0) :=
strict_mono_on_log.inj_on

lemma eq_one_of_pos_of_log_eq_zero {x : ℝ} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1 :=
log_inj_on_pos (set.mem_Ioi.2 h₁) (set.mem_Ioi.2 zero_lt_one) (h₂.trans real.log_one.symm)

lemma log_ne_zero_of_pos_of_ne_one {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0 :=
mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx

@[simp] lemma log_eq_zero {x : ℝ} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1 :=
begin
  split,
  { intros h,
    rcases lt_trichotomy x 0 with x_lt_zero | rfl | x_gt_zero,
    { refine or.inr (or.inr (eq_neg_iff_eq_neg.mp _)),
      rw [←log_neg_eq_log x] at h,
      exact (eq_one_of_pos_of_log_eq_zero (neg_pos.mpr x_lt_zero) h).symm, },
    { exact or.inl rfl },
    { exact or.inr (or.inl (eq_one_of_pos_of_log_eq_zero x_gt_zero h)), }, },
  { rintro (rfl|rfl|rfl); simp only [log_one, log_zero, log_neg_eq_log], }
end

@[simp] lemma log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x :=
begin
  induction n with n ih,
  { simp },
  rcases eq_or_ne x 0 with rfl | hx,
  { simp },
  rw [pow_succ', log_mul (pow_ne_zero _ hx) hx, ih, nat.cast_succ, add_mul, one_mul],
end

@[simp] lemma log_zpow (x : ℝ) (n : ℤ) : log (x ^ n) = n * log x :=
begin
  induction n,
  { rw [int.of_nat_eq_coe, zpow_coe_nat, log_pow, int.cast_coe_nat] },
  rw [zpow_neg_succ_of_nat, log_inv, log_pow, int.cast_neg_succ_of_nat, nat.cast_add_one,
    neg_mul_eq_neg_mul],
end

lemma log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 :=
begin
  rw le_sub_iff_add_le,
  convert add_one_le_exp (log x),
  rw exp_log hx,
end

/-- Bound for `|log x * x|` in the interval `(0, 1]`. -/
lemma abs_log_mul_self_lt (x: ℝ) (h1 : 0 < x) (h2 : x ≤ 1) : |log x * x| < 1 :=
begin
  have : 0 < 1/x := by simpa only [one_div, inv_pos] using h1,
  replace := log_le_sub_one_of_pos this,
  replace : log (1 / x) < 1/x := by linarith,
  rw [log_div one_ne_zero h1.ne', log_one, zero_sub, lt_div_iff h1] at this,
  have aux : 0 ≤ -log x * x,
  { refine mul_nonneg _ h1.le, rw ←log_inv, apply log_nonneg,
    rw [←(le_inv h1 zero_lt_one), inv_one], exact h2, },
  rw [←(abs_of_nonneg aux), neg_mul, abs_neg] at this, exact this,
end

/-- The real logarithm function tends to `+∞` at `+∞`. -/
lemma tendsto_log_at_top : tendsto log at_top at_top :=
tendsto_comp_exp_at_top.1 $ by simpa only [log_exp] using tendsto_id

lemma tendsto_log_nhds_within_zero : tendsto log (𝓝[≠] 0) at_bot :=
begin
  rw [← (show _ = log, from funext log_abs)],
  refine tendsto.comp _ tendsto_abs_nhds_within_zero,
  simpa [← tendsto_comp_exp_at_bot] using tendsto_id
end

lemma continuous_on_log : continuous_on log {0}ᶜ :=
begin
  rw [continuous_on_iff_continuous_restrict, restrict],
  conv in (log _) { rw [log_of_ne_zero (show (x : ℝ) ≠ 0, from x.2)] },
  exact exp_order_iso.symm.continuous.comp (continuous_subtype_mk _ continuous_subtype_coe.norm)
end

@[continuity] lemma continuous_log : continuous (λ x : {x : ℝ // x ≠ 0}, log x) :=
continuous_on_iff_continuous_restrict.1 $ continuous_on_log.mono $ λ x hx, hx

@[continuity] lemma continuous_log' : continuous (λ x : {x : ℝ // 0 < x}, log x) :=
continuous_on_iff_continuous_restrict.1 $ continuous_on_log.mono $ λ x hx, ne_of_gt hx

lemma continuous_at_log (hx : x ≠ 0) : continuous_at log x :=
(continuous_on_log x hx).continuous_at $ is_open.mem_nhds is_open_compl_singleton hx

@[simp] lemma continuous_at_log_iff : continuous_at log x ↔ x ≠ 0 :=
begin
  refine ⟨_, continuous_at_log⟩,
  rintros h rfl,
  exact not_tendsto_nhds_of_tendsto_at_bot tendsto_log_nhds_within_zero _
    (h.tendsto.mono_left inf_le_left)
end

open_locale big_operators

lemma log_prod {α : Type*} (s : finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0):
  log (∏ i in s, f i) = ∑ i in s, log (f i) :=
begin
  classical,
  induction s using finset.induction_on with a s ha ih,
  { simp },
  simp only [finset.mem_insert, forall_eq_or_imp] at hf,
  simp [ha, ih hf.2, log_mul hf.1 (finset.prod_ne_zero_iff.2 hf.2)],
end

lemma tendsto_pow_log_div_mul_add_at_top (a b : ℝ) (n : ℕ) (ha : a ≠ 0) :
  tendsto (λ x, log x ^ n / (a * x + b)) at_top (𝓝 0) :=
((tendsto_div_pow_mul_exp_add_at_top a b n ha.symm).comp tendsto_log_at_top).congr'
  (by filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx using by simp [exp_log hx])

lemma is_o_pow_log_id_at_top {n : ℕ} : asymptotics.is_o (λ x, log x ^ n) id at_top :=
begin
  rw asymptotics.is_o_iff_tendsto',
  { simpa using tendsto_pow_log_div_mul_add_at_top 1 0 n one_ne_zero },
  filter_upwards [eventually_ne_at_top (0 : ℝ)] with x h₁ h₂ using (h₁ h₂).elim,
end

lemma is_o_log_id_at_top : asymptotics.is_o log id at_top :=
is_o_pow_log_id_at_top.congr_left (λ x, pow_one _)

end real

section continuity

open real
variables {α : Type*}

lemma filter.tendsto.log {f : α → ℝ} {l : filter α} {x : ℝ} (h : tendsto f l (𝓝 x)) (hx : x ≠ 0) :
  tendsto (λ x, log (f x)) l (𝓝 (log x)) :=
(continuous_at_log hx).tendsto.comp h

variables [topological_space α] {f : α → ℝ} {s : set α} {a : α}

lemma continuous.log (hf : continuous f) (h₀ : ∀ x, f x ≠ 0) : continuous (λ x, log (f x)) :=
continuous_on_log.comp_continuous hf h₀

lemma continuous_at.log (hf : continuous_at f a) (h₀ : f a ≠ 0) :
  continuous_at (λ x, log (f x)) a :=
hf.log h₀

lemma continuous_within_at.log (hf : continuous_within_at f s a) (h₀ : f a ≠ 0) :
  continuous_within_at (λ x, log (f x)) s a :=
hf.log h₀

lemma continuous_on.log (hf : continuous_on f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
  continuous_on (λ x, log (f x)) s :=
λ x hx, (hf x hx).log (h₀ x hx)

end continuity
