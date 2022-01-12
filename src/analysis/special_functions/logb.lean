/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.special_functions.log
import analysis.special_functions.pow

/-!
# Real logarithm base `b`

In this file we define `real.logb` to be the logarithm of a real number in a given base `b`. We
define this as the division of the natural logarithms of the argument and the base, so that we have
a globally defined function with `logb b 0 = 0`, `logb b (-x) = logb b x` `logb 0 x = 0` and
`logb (-b) x = logb b x`.

We prove some basic properties of this function and it's relation to `rpow`.

## Tags

logarithm, continuity
-/

open set filter function
open_locale topological_space
noncomputable theory

namespace real

variables {b x y : ℝ}

/-- The real logarithm in a given base. As with the natural logarithm, we define `logb b x` to
be `logb b |x|` for `x < 0`, and `0` for `x = 0`.-/
@[pp_nodot] noncomputable def logb (b x : ℝ) : ℝ := log x / log b

lemma log_div_log : log x / log b = logb b x := rfl

@[simp] lemma logb_zero : logb b 0 = 0 := by simp [logb]

@[simp] lemma logb_one : logb b 1 = 0 := by simp [logb]

@[simp] lemma logb_abs (x : ℝ) : logb b (|x|) = logb b x := by rw [logb, logb, log_abs]

@[simp] lemma logb_neg_eq_logb (x : ℝ) : logb b (-x) = logb b x :=
by rw [← logb_abs x, ← logb_abs (-x), abs_neg]

lemma logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y :=
by simp_rw [logb, log_mul hx hy, add_div]

lemma logb_div (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x / y) = logb b x - logb b y :=
by simp_rw [logb, log_div hx hy, sub_div]

@[simp] lemma logb_inv (x : ℝ) : logb b (x⁻¹) = -logb b x := by simp [logb, neg_div]

section b_pos_and_ne_one

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
  simp only [abs_pos, mem_Ioi, ne.def, hx, not_false_iff],
  rw log_rpow b_pos,
  rw logb,
  rw log_abs,
  have b_ne_zero : b ≠ 0, linarith,
  have b_ne_minus_one : b ≠ -1, linarith,
  have log_b_ne_zero : log b ≠ 0, simp [b_ne_one, b_ne_zero, b_ne_minus_one],
  field_simp [ne_of_lt b_pos],
end

@[simp] lemma rpow_logb (b_pos : 0 < b) (b_ne_one : b ≠ 1) (hx : 0 < x) : b ^ (logb b x) = x :=
by { rw rpow_logb_eq_abs b_pos b_ne_one (hx.ne'), exact abs_of_pos hx, }

lemma rpow_logb_of_neg (b_pos : 0 < b) (b_ne_one : b ≠ 1) (hx : x < 0) : b ^ (logb b x) = -x :=
by { rw rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx), exact abs_of_neg hx }

lemma surj_on_logb (b_pos : 0 < b) (b_ne_one : b ≠ 1) : surj_on (logb b) (Ioi 0) univ :=
λ x _, ⟨rpow b x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩

lemma logb_surjective (b_pos : 0 < b) (b_ne_one : b ≠ 1) : surjective (logb b) :=
λ x, ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp] lemma range_logb (b_pos : 0 < b) (b_ne_one : b ≠ 1) : range (logb b) = univ :=
(logb_surjective b_pos b_ne_one).range_eq

lemma surj_on_logb' (b_pos : 0 < b) (b_ne_one : b ≠ 1) : surj_on (logb b) (Iio 0) univ :=
begin
  intros x x_in_univ,
  use -b ^ x,
  split,
  { simp only [right.neg_neg_iff, set.mem_Iio], apply rpow_pos_of_pos b_pos, },
  { rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one], },
end

end b_pos_and_ne_one

section one_lt_b

variable {one_lt_b : 1 < b}

@[simp] lemma logb_le_logb {one_lt_b} (h : 0 < x) (h₁ : 0 < y) :
  logb b x ≤ logb b y ↔ x ≤ y :=
by { rw [logb, logb, div_le_div_right (log_pos one_lt_b), log_le_log h h₁], }

lemma logb_lt_logb (one_lt_b : 1 < b) (hx : 0 < x) (hxy : x < y) : logb b x < logb b y :=
by { rw [logb, logb, div_lt_div_right (log_pos one_lt_b)], exact log_lt_log hx hxy, }

@[simp] lemma logb_lt_logb_iff (one_lt_b : 1 < b) (hx : 0 < x) (hy : 0 < y) :
  logb b x < logb b y ↔ x < y :=
by { rw [logb, logb, div_lt_div_right (log_pos one_lt_b)], exact log_lt_log_iff hx hy, }

lemma logb_le_iff_le_rpow (one_lt_b : 1 < b) (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y :=
by { rw [←rpow_le_rpow_left_iff one_lt_b, rpow_logb], linarith, linarith, exact hx, }

lemma logb_lt_iff_lt_rpow (one_lt_b : 1 < b) (hx : 0 < x) : logb b x < y ↔ x < b ^ y :=
by { rw [←rpow_lt_rpow_left_iff one_lt_b, rpow_logb], linarith, linarith, exact hx, }

lemma le_logb_iff_rpow_le (one_lt_b : 1 < b) (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y :=
by { rw [←rpow_le_rpow_left_iff one_lt_b, rpow_logb], linarith, linarith, exact hy, }

lemma lt_logb_iff_rpow_lt (one_lt_b : 1 < b) (hy : 0 < y) : x < logb b y ↔ b ^ x < y :=
by { rw [←rpow_lt_rpow_left_iff one_lt_b, rpow_logb], linarith, linarith, exact hy, }

lemma logb_pos_iff (one_lt_b : 1 < b) (hx : 0 < x) : 0 < logb b x ↔ 1 < x :=
by { rw ← @logb_one b, rw logb_lt_logb_iff one_lt_b zero_lt_one hx, }

lemma logb_pos (one_lt_b : 1 < b) (hx : 1 < x) : 0 < logb b x :=
by { rw logb_pos_iff one_lt_b (lt_trans zero_lt_one hx), exact hx, }

lemma logb_neg_iff (one_lt_b : 1 < b) (h : 0 < x) : logb b x < 0 ↔ x < 1 :=
by { rw ← logb_one, exact logb_lt_logb_iff one_lt_b h zero_lt_one, }

lemma logb_neg (one_lt_b : 1 < b) (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
(logb_neg_iff one_lt_b h0).2 h1

lemma logb_nonneg_iff (one_lt_b : 1 < b) (hx : 0 < x) : 0 ≤ logb b x ↔ 1 ≤ x :=
by rw [← not_lt, logb_neg_iff one_lt_b hx, not_lt]

lemma logb_nonneg (one_lt_b : 1 < b) (hx : 1 ≤ x) : 0 ≤ logb b x :=
(logb_nonneg_iff one_lt_b (zero_lt_one.trans_le hx)).2 hx

lemma logb_nonpos_iff (one_lt_b : 1 < b) (hx : 0 < x) : logb b x ≤ 0 ↔ x ≤ 1 :=
by rw [← not_lt, logb_pos_iff one_lt_b hx, not_lt]

lemma logb_nonpos_iff' (one_lt_b : 1 < b) (hx : 0 ≤ x) : logb b x ≤ 0 ↔ x ≤ 1 :=
begin
  rcases hx.eq_or_lt with (rfl|hx),
  { simp [le_refl, zero_le_one] },
  exact logb_nonpos_iff one_lt_b hx,
end

lemma logb_nonpos (one_lt_b : 1 < b) (hx : 0 ≤ x) (h'x : x ≤ 1) : logb b x ≤ 0 :=
(logb_nonpos_iff' one_lt_b hx).2 h'x

lemma strict_mono_on_logb (one_lt_b : 1 < b) : strict_mono_on (logb b) (set.Ioi 0) :=
λ x hx y hy hxy, logb_lt_logb one_lt_b hx hxy

lemma strict_anti_on_logb (one_lt_b : 1 < b) : strict_anti_on (logb b) (set.Iio 0) :=
begin
  rintros x (hx : x < 0) y (hy : y < 0) hxy,
  rw [← logb_abs y, ← logb_abs x],
  refine logb_lt_logb one_lt_b (abs_pos.2 hy.ne) _,
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff],
end

lemma logb_inj_on_pos (one_lt_b : 1 < b) : set.inj_on (logb b) (set.Ioi 0) :=
(strict_mono_on_logb one_lt_b).inj_on

lemma eq_one_of_pos_of_logb_eq_zero (one_lt_b : 1 < b) (h₁ : 0 < x) (h₂ : logb b x = 0) :
x = 1 :=
logb_inj_on_pos one_lt_b (set.mem_Ioi.2 h₁) (set.mem_Ioi.2 zero_lt_one)
  (h₂.trans real.logb_one.symm)

lemma logb_ne_zero_of_pos_of_ne_one (one_lt_b : 1 < b) (hx_pos : 0 < x) (hx : x ≠ 1) :
  logb b x ≠ 0 :=
mt (eq_one_of_pos_of_logb_eq_zero one_lt_b hx_pos) hx

end one_lt_b

@[simp] lemma logb_eq_zero :
  logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1 :=
begin
  simp_rw [logb, div_eq_zero_iff, log_eq_zero],
  tauto,
end

lemma tendsto_logb_at_top (one_lt_b : 1 < b) : tendsto (logb b) at_top at_top :=
begin
  rw tendsto_at_top_at_top,
  intro e,
  use 1 ⊔ b ^ e,
  intro a,
  simp only [and_imp, sup_le_iff],
  intro ha,
  rw le_logb_iff_rpow_le one_lt_b,
  tauto,
  exact lt_of_lt_of_le zero_lt_one ha,
end

/- TODO add other limits and continuous API lemmas analogous to those in log.lean -/

open_locale big_operators

lemma logb_prod {α : Type*} (s : finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0):
  logb b (∏ i in s, f i) = ∑ i in s, logb b (f i) :=
begin
  classical,
  induction s using finset.induction_on with a s ha ih,
  { simp },
  simp only [finset.mem_insert, forall_eq_or_imp] at hf,
  simp [ha, ih hf.2, logb_mul hf.1 (finset.prod_ne_zero_iff.2 hf.2)],
end

end real
