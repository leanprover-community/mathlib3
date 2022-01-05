/-
Copyright (c) 2018 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.special_functions.log
import analysis.special_functions.pow

/-!
# Real logarithm base `b`

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

variables {b x y : ℝ}

/-- The real logarithm in a given base. As with the natural logarithm, we define `logb b x` to
be `logb b |x|` for `x < 0`, and to `0` for `x = 0`.-/
@[pp_nodot] noncomputable def logb (b x : ℝ) : ℝ := log x / log b

lemma log_div_log : log x / log b = logb b x := rfl

-- lemma log_of_ne_zero (hx : x ≠ 0) : log x = exp_order_iso.symm ⟨|x|, abs_pos.2 hx⟩ := dif_neg hx

-- lemma log_of_pos (hx : 0 < x) : log x = exp_order_iso.symm ⟨x, hx⟩ :=
-- by { rw [log_of_ne_zero hx.ne'], congr, exact abs_of_pos hx }

@[simp] lemma logb_rpow (b_pos : 0 < b) (b_ne_one : b ≠ 1) :
  logb b (b ^ x) = x :=
begin
  rw [logb, div_eq_iff, log_rpow b_pos],
  have b_ne_zero : b ≠ 0, linarith,
  have b_ne_minus_one : b ≠ -1, linarith,
  simp [b_ne_one, b_ne_zero, b_ne_minus_one],
end

lemma rpow_logb_eq_abs (b_pos : 0 < b) (b_ne_one : b ≠ 1) (hx : x ≠ 0) : b ^ (logb b x) = |x| :=
begin
  apply log_inj_on_pos,
  simp only [set.mem_Ioi],
  apply rpow_pos_of_pos b_pos,
  simp only [abs_pos, set.mem_Ioi, ne.def, hx],
  exact not_false,
  rw log_rpow b_pos,
  rw logb,
  rw log_abs,
  have b_ne_zero : b ≠ 0, linarith,
  have b_ne_minus_one : b ≠ -1, linarith,
  have log_b_ne_zero : log b ≠ 0, simp [b_ne_one, b_ne_zero, b_ne_minus_one],
  field_simp [ne_of_lt b_pos],
end

lemma rpow_logb (b_pos : 0 < b) (b_ne_one : b ≠ 1) (hx : 0 < x) : b ^ (logb b x) = x :=
by { rw rpow_logb_eq_abs b_pos b_ne_one (hx.ne'), exact abs_of_pos hx, }

lemma rpow_logb_of_neg (b_pos : 0 < b) (b_ne_one : b ≠ 1) (hx : x < 0) : b ^ (logb b x) = -x :=
by { rw rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx), exact abs_of_neg hx }

-- @[simp] lemma log_exp (x : ℝ) : log (exp x) = x :=
-- exp_injective $ exp_log (exp_pos x)

lemma surj_on_logb (b_pos : 0 < b) (b_ne_one : b ≠ 1) : surj_on (logb b) (Ioi 0) univ :=
λ x _, ⟨rpow b x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩

lemma logb_surjective (b_pos : 0 < b) (b_ne_one : b ≠ 1) : surjective (logb b) :=
λ x, ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp] lemma range_logb (b_pos : 0 < b) (b_ne_one : b ≠ 1) : range (logb b) = univ :=
(logb_surjective b_pos b_ne_one).range_eq

@[simp] lemma logb_zero : logb b 0 = 0 := by simp [logb]

@[simp] lemma logb_one : logb b 1 = 0 := by simp [logb]

@[simp] lemma logb_abs (x : ℝ) : logb b (|x|) = logb b x := by rw [logb, logb, log_abs]

@[simp] lemma logb_neg_eq_logb (x : ℝ) : logb b (-x) = logb b x :=
by rw [← logb_abs x, ← logb_abs (-x), abs_neg]

lemma surj_on_logb' (b_pos : 0 < b) (b_ne_one : b ≠ 1) : surj_on (logb b) (Iio 0) univ :=
begin
  intros x x_in_univ,
  use -b ^ x,
  split,
  { simp only [right.neg_neg_iff, set.mem_Iio], apply rpow_pos_of_pos b_pos, },
  { rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one], },
end

lemma logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y :=
by simp_rw [logb, log_mul hx hy, add_div]

lemma logb_div (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x / y) = logb b x - logb b y :=
by simp_rw [logb, log_div hx hy, sub_div]

@[simp] lemma logb_inv (x : ℝ) : logb b (x⁻¹) = -logb b x := by simp [logb, neg_div]

lemma logb_le_logb (one_le_b : 1 < b) (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y :=
by {rw [logb, logb, div_le_div_right (log_pos one_le_b), log_le_log h h₁], }

lemma logb_lt_logb (one_le_b : 1 < b) (hx : 0 < x) (hxy : x < y) : logb b x < logb b y :=
by {rw [logb, logb, div_lt_div_right (log_pos one_le_b)], exact log_lt_log hx hxy, }

lemma logb_lt_logb_iff (one_le_b : 1 < b) (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y :=
by {rw [logb, logb, div_lt_div_right (log_pos one_le_b)], exact log_lt_log_iff hx hy, }

-- TODO finish converting below this line
-- log -> logb b
-- exp -> b ^

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

lemma log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 :=
begin
  rw le_sub_iff_add_le,
  convert add_one_le_exp (log x),
  rw exp_log hx,
end

lemma log_div_self_antitone_on : antitone_on (λ x : ℝ, log x / x) {x | exp 1 ≤ x} :=
begin
  simp only [antitone_on, mem_set_of_eq],
  intros x hex y hey hxy,
  have x_pos : 0 < x := (exp_pos 1).trans_le hex,
  have y_pos : 0 < y := (exp_pos 1).trans_le hey,
  have hlogx : 1 ≤ log x := by rwa le_log_iff_exp_le x_pos,
  have hyx : 0 ≤ y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff x_pos, zero_add, one_mul],
  rw [div_le_iff y_pos, ←sub_le_sub_iff_right (log x)],
  calc
    log y - log x = log (y / x)           : by rw [log_div (y_pos.ne') (x_pos.ne')]
    ...           ≤ (y / x) - 1           : log_le_sub_one_of_pos (div_pos y_pos x_pos)
    ...           ≤ log x * (y / x - 1)   : le_mul_of_one_le_left hyx hlogx
    ...           = log x / x * y - log x : by ring,
end

/-- The real logarithm in a given base. -/
noncomputable def logb (b x : ℝ) : ℝ := log x / log b

@[simp] lemma log_div_log {b x : ℝ} : log x / log b = logb b x := rfl

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
