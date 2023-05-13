/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import analysis.special_functions.pow_nnreal

/-!
# Limits and asymptotics of power functions at `+∞`

This file contains results about the limiting behaviour of power functions at `+∞`. For convenience
some results on asymptotics as `x → 0` (those which are not just continuity statements) are also
located here.
-/

noncomputable theory

open_locale classical real topology nnreal ennreal filter big_operators complex_conjugate
open filter finset set

/-!
## Limits at `+∞`
-/

section limits

open real filter

/-- The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`. -/
lemma tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) : tendsto (λ x : ℝ, x ^ y) at_top at_top :=
begin
  rw tendsto_at_top_at_top,
  intro b,
  use (max b 0) ^ (1/y),
  intros x hx,
  exact le_of_max_le_left
    (by { convert rpow_le_rpow (rpow_nonneg_of_nonneg (le_max_right b 0) (1/y)) hx (le_of_lt hy),
      rw [← rpow_mul (le_max_right b 0), (eq_div_iff (ne_of_gt hy)).mp rfl, rpow_one] }),
end

/-- The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`. -/
lemma tendsto_rpow_neg_at_top {y : ℝ} (hy : 0 < y) : tendsto (λ x : ℝ, x ^ (-y)) at_top (𝓝 0) :=
tendsto.congr' (eventually_eq_of_mem (Ioi_mem_at_top 0) (λ x hx, (rpow_neg (le_of_lt hx) y).symm))
  (tendsto_rpow_at_top hy).inv_tendsto_at_top

/-- The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers `a`, `b`, and
`c` such that `b` is nonzero. -/
lemma tendsto_rpow_div_mul_add (a b c : ℝ) (hb : 0 ≠ b) :
  tendsto (λ x, x ^ (a / (b*x+c))) at_top (𝓝 1) :=
begin
  refine tendsto.congr' _ ((tendsto_exp_nhds_0_nhds_1.comp
    (by simpa only [mul_zero, pow_one] using ((@tendsto_const_nhds _ _ _ a _).mul
      (tendsto_div_pow_mul_exp_add_at_top b c 1 hb)))).comp tendsto_log_at_top),
  apply eventually_eq_of_mem (Ioi_mem_at_top (0:ℝ)),
  intros x hx,
  simp only [set.mem_Ioi, function.comp_app] at hx ⊢,
  rw [exp_log hx, ← exp_log (rpow_pos_of_pos hx (a / (b * x + c))), log_rpow hx (a / (b * x + c))],
  field_simp,
end

/-- The function `x ^ (1 / x)` tends to `1` at `+∞`. -/
lemma tendsto_rpow_div : tendsto (λ x, x ^ ((1:ℝ) / x)) at_top (𝓝 1) :=
by { convert tendsto_rpow_div_mul_add (1:ℝ) _ (0:ℝ) zero_ne_one, funext, congr' 2, ring }

/-- The function `x ^ (-1 / x)` tends to `1` at `+∞`. -/
lemma tendsto_rpow_neg_div : tendsto (λ x, x ^ (-(1:ℝ) / x)) at_top (𝓝 1) :=
by { convert tendsto_rpow_div_mul_add (-(1:ℝ)) _ (0:ℝ) zero_ne_one, funext, congr' 2, ring }

/-- The function `exp(x) / x ^ s` tends to `+∞` at `+∞`, for any real number `s`. -/
lemma tendsto_exp_div_rpow_at_top (s : ℝ) : tendsto (λ x : ℝ, exp x / x ^ s) at_top at_top :=
begin
  cases archimedean_iff_nat_lt.1 (real.archimedean) s with n hn,
  refine tendsto_at_top_mono' _ _ (tendsto_exp_div_pow_at_top n),
  filter_upwards [eventually_gt_at_top (0 : ℝ), eventually_ge_at_top (1 : ℝ)] with x hx₀ hx₁,
  rw [div_le_div_left (exp_pos _) (pow_pos hx₀ _) (rpow_pos_of_pos hx₀ _), ←rpow_nat_cast],
  exact rpow_le_rpow_of_exponent_le hx₁ hn.le,
end

/-- The function `exp (b * x) / x ^ s` tends to `+∞` at `+∞`, for any real `s` and `b > 0`. -/
lemma tendsto_exp_mul_div_rpow_at_top (s : ℝ) (b : ℝ) (hb : 0 < b) :
  tendsto (λ x : ℝ, exp (b * x) / x ^ s) at_top at_top :=
begin
  refine ((tendsto_rpow_at_top hb).comp (tendsto_exp_div_rpow_at_top (s / b))).congr' _,
  filter_upwards [eventually_ge_at_top (0 : ℝ)] with x hx₀,
  simp [div_rpow, (exp_pos x).le, rpow_nonneg_of_nonneg, ←rpow_mul, ←exp_mul, mul_comm x, hb.ne', *]
end

/-- The function `x ^ s * exp (-b * x)` tends to `0` at `+∞`, for any real `s` and `b > 0`. -/
lemma tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 (s : ℝ) (b : ℝ) (hb : 0 < b):
  tendsto (λ x : ℝ, x ^ s * exp (-b * x)) at_top (𝓝 0) :=
begin
  refine (tendsto_exp_mul_div_rpow_at_top s b hb).inv_tendsto_at_top.congr' _,
  filter_upwards with x using by simp [exp_neg, inv_div, div_eq_mul_inv _ (exp _)]
end

theorem nnreal.tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) :
  tendsto (λ (x : ℝ≥0), x ^ y) at_top at_top :=
begin
  rw filter.tendsto_at_top_at_top,
  intros b,
  obtain ⟨c, hc⟩ := tendsto_at_top_at_top.mp (tendsto_rpow_at_top hy) b,
  use c.to_nnreal,
  intros a ha,
  exact_mod_cast hc a (real.to_nnreal_le_iff_le_coe.mp ha),
end

theorem ennreal.tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) :
  tendsto (λ (x : ℝ≥0∞), x ^ y) (𝓝 ⊤) (𝓝 ⊤) :=
begin
  rw ennreal.tendsto_nhds_top_iff_nnreal,
  intros x,
  obtain ⟨c, _, hc⟩ :=
    (at_top_basis_Ioi.tendsto_iff at_top_basis_Ioi).mp (nnreal.tendsto_rpow_at_top hy) x trivial,
  have hc' : set.Ioi (↑c) ∈ 𝓝 (⊤ : ℝ≥0∞) := Ioi_mem_nhds ennreal.coe_lt_top,
  refine eventually_of_mem hc' _,
  intros a ha,
  by_cases ha' : a = ⊤,
  { simp [ha', hy] },
  lift a to ℝ≥0 using ha',
  change ↑c < ↑a at ha,
  rw ennreal.coe_rpow_of_nonneg _ hy.le,
  exact_mod_cast hc a (by exact_mod_cast ha),
end

end limits

/-!
## Asymptotic results: `is_O`, `is_o` and `is_Theta`
-/
namespace complex
section

variables {α : Type*} {l : filter α} {f g : α → ℂ}

open asymptotics

lemma is_Theta_exp_arg_mul_im (hl : is_bounded_under (≤) l (λ x, |(g x).im|)) :
  (λ x, real.exp (arg (f x) * im (g x))) =Θ[l] (λ x, (1 : ℝ)) :=
begin
  rcases hl with ⟨b, hb⟩,
  refine real.is_Theta_exp_comp_one.2 ⟨π * b, _⟩,
  rw eventually_map at hb ⊢,
  refine hb.mono (λ x hx, _),
  erw [abs_mul],
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) real.pi_pos.le
end

lemma is_O_cpow_rpow (hl : is_bounded_under (≤) l (λ x, |(g x).im|)) :
  (λ x, f x ^ g x) =O[l] (λ x, abs (f x) ^ (g x).re) :=
calc (λ x, f x ^ g x) =O[l] (λ x, abs (f x) ^ (g x).re / real.exp (arg (f x) * im (g x))) :
  is_O_of_le _ $ λ x, (abs_cpow_le _ _).trans (le_abs_self _)
... =Θ[l] (λ x, abs (f x) ^ (g x).re / (1 : ℝ)) :
  (is_Theta_refl _ _).div (is_Theta_exp_arg_mul_im hl)
... =ᶠ[l] (λ x, abs (f x) ^ (g x).re) : by simp only [of_real_one, div_one]

lemma is_Theta_cpow_rpow (hl_im : is_bounded_under (≤) l (λ x, |(g x).im|))
  (hl : ∀ᶠ x in l, f x = 0 → re (g x) = 0 → g x = 0):
  (λ x, f x ^ g x) =Θ[l] (λ x, abs (f x) ^ (g x).re) :=
calc (λ x, f x ^ g x) =Θ[l] (λ x, abs (f x) ^ (g x).re / real.exp (arg (f x) * im (g x))) :
  is_Theta_of_norm_eventually_eq' $ hl.mono $ λ x, abs_cpow_of_imp
... =Θ[l] (λ x, abs (f x) ^ (g x).re / (1 : ℝ)) :
  (is_Theta_refl _ _).div (is_Theta_exp_arg_mul_im hl_im)
... =ᶠ[l] (λ x, abs (f x) ^ (g x).re) : by simp only [of_real_one, div_one]

lemma is_Theta_cpow_const_rpow {b : ℂ} (hl : b.re = 0 → b ≠ 0 → ∀ᶠ x in l, f x ≠ 0) :
  (λ x, f x ^ b) =Θ[l] (λ x, abs (f x) ^ b.re) :=
is_Theta_cpow_rpow is_bounded_under_const $ by simpa only [eventually_imp_distrib_right, ne.def,
  ← not_frequently, not_imp_not, imp.swap] using hl

end

end complex

open real

namespace asymptotics

variables {α : Type*} {r c : ℝ} {l : filter α} {f g : α → ℝ}

lemma is_O_with.rpow (h : is_O_with c l f g) (hc : 0 ≤ c) (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) :
  is_O_with (c ^ r) l (λ x, f x ^ r) (λ x, g x ^ r) :=
begin
  apply is_O_with.of_bound,
  filter_upwards [hg, h.bound] with x hgx hx,
  calc |f x ^ r| ≤ |f x| ^ r         : abs_rpow_le_abs_rpow _ _
             ... ≤ (c * |g x|) ^ r   : rpow_le_rpow (abs_nonneg _) hx hr
             ... = c ^ r * |g x ^ r| : by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]
end

lemma is_O.rpow (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) (h : f =O[l] g) :
  (λ x, f x ^ r) =O[l] (λ x, g x ^ r) :=
let ⟨c, hc, h'⟩ := h.exists_nonneg in (h'.rpow hc hr hg).is_O

lemma is_o.rpow (hr : 0 < r) (hg : 0 ≤ᶠ[l] g) (h : f =o[l] g) :
  (λ x, f x ^ r) =o[l] (λ x, g x ^ r) :=
is_o.of_is_O_with $ λ c hc, ((h.forall_is_O_with (rpow_pos_of_pos hc r⁻¹)).rpow
  (rpow_nonneg_of_nonneg hc.le _) hr.le hg).congr_const
    (by rw [←rpow_mul hc.le, inv_mul_cancel hr.ne', rpow_one])

end asymptotics

open asymptotics

/-- `x ^ s = o(exp(b * x))` as `x → ∞` for any real `s` and positive `b`. -/
lemma is_o_rpow_exp_pos_mul_at_top (s : ℝ) {b : ℝ} (hb : 0 < b) :
  (λ x : ℝ, x ^ s) =o[at_top] (λ x, exp (b * x)) :=
iff.mpr (is_o_iff_tendsto $ λ x h, absurd h (exp_pos _).ne') $
  by simpa only [div_eq_mul_inv, exp_neg, neg_mul]
    using tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 s b hb

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any integer `k` and positive `b`. -/
lemma is_o_zpow_exp_pos_mul_at_top (k : ℤ) {b : ℝ} (hb : 0 < b) :
  (λ x : ℝ, x ^ k) =o[at_top] (λ x, exp (b * x)) :=
by simpa only [rpow_int_cast] using is_o_rpow_exp_pos_mul_at_top k hb

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any natural `k` and positive `b`. -/
lemma is_o_pow_exp_pos_mul_at_top (k : ℕ) {b : ℝ} (hb : 0 < b) :
  (λ x : ℝ, x ^ k) =o[at_top] (λ x, exp (b * x)) :=
by simpa using is_o_zpow_exp_pos_mul_at_top k hb

/-- `x ^ s = o(exp x)` as `x → ∞` for any real `s`. -/
lemma is_o_rpow_exp_at_top (s : ℝ) : (λ x : ℝ, x ^ s) =o[at_top] exp :=
by simpa only [one_mul] using is_o_rpow_exp_pos_mul_at_top s one_pos

/-- `exp (-a * x) = o(x ^ s)` as `x → ∞`, for any positive `a` and real `s`. -/
lemma is_o_exp_neg_mul_rpow_at_top {a : ℝ} (ha : 0 < a) (b : ℝ) :
  is_o at_top (λ x : ℝ, exp (-a * x)) (λ x : ℝ, x ^ b) :=
begin
  apply is_o_of_tendsto',
  { refine (eventually_gt_at_top 0).mp (eventually_of_forall $ λ t ht h, _),
    rw rpow_eq_zero_iff_of_nonneg ht.le at h,
    exact (ht.ne' h.1).elim },
  { refine (tendsto_exp_mul_div_rpow_at_top (-b) a ha).inv_tendsto_at_top.congr' _,
    refine (eventually_ge_at_top 0).mp (eventually_of_forall $ λ t ht, _),
    dsimp only,
    rw [pi.inv_apply, inv_div, ←inv_div_inv, neg_mul, real.exp_neg, rpow_neg ht, inv_inv] }
end

lemma is_o_log_rpow_at_top {r : ℝ} (hr : 0 < r) : log =o[at_top] (λ x, x ^ r) :=
calc log =O[at_top] (λ x, r * log x)   : is_O_self_const_mul _ hr.ne' _ _
     ... =ᶠ[at_top] (λ x, log (x ^ r)) :
  (eventually_gt_at_top 0).mono $ λ x hx, (log_rpow hx _).symm
     ... =o[at_top] (λ x, x ^ r)       : is_o_log_id_at_top.comp_tendsto (tendsto_rpow_at_top hr)

lemma is_o_log_rpow_rpow_at_top {s : ℝ} (r : ℝ) (hs : 0 < s) :
  (λ x, log x ^ r) =o[at_top] (λ x, x ^ s) :=
let r' := max r 1 in
have hr : 0 < r', from lt_max_iff.2 $ or.inr one_pos,
have H : 0 < s / r', from div_pos hs hr,
calc (λ x, log x ^ r) =O[at_top] (λ x, log x ^ r') :
  is_O.of_bound 1 $ (tendsto_log_at_top.eventually_ge_at_top 1).mono $ λ x hx,
    have hx₀ : 0 ≤ log x, from zero_le_one.trans hx,
    by simp [norm_eq_abs, abs_rpow_of_nonneg, abs_rpow_of_nonneg hx₀,
      rpow_le_rpow_of_exponent_le (hx.trans (le_abs_self _))]
                  ... =o[at_top] (λ x, (x ^ (s / r')) ^ r') :
  (is_o_log_rpow_at_top H).rpow hr $ (tendsto_rpow_at_top H).eventually $ eventually_ge_at_top 0
                  ... =ᶠ[at_top] (λ x, x ^ s) :
  (eventually_ge_at_top 0).mono $ λ x hx, by simp only [← rpow_mul hx, div_mul_cancel _ hr.ne']

lemma is_o_abs_log_rpow_rpow_nhds_zero {s : ℝ} (r : ℝ) (hs : s < 0) :
  (λ x, |log x| ^ r) =o[𝓝[>] 0] (λ x, x ^ s) :=
((is_o_log_rpow_rpow_at_top r (neg_pos.2 hs)).comp_tendsto tendsto_inv_zero_at_top).congr'
  (mem_of_superset (Icc_mem_nhds_within_Ioi $ set.left_mem_Ico.2 one_pos) $
    λ x hx, by simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
  (eventually_mem_nhds_within.mono $ λ x hx,
    by rw [function.comp_app, inv_rpow hx.out.le, rpow_neg hx.out.le, inv_inv])

lemma is_o_log_rpow_nhds_zero {r : ℝ} (hr : r < 0) : log =o[𝓝[>] 0] (λ x, x ^ r) :=
(is_o_abs_log_rpow_rpow_nhds_zero 1 hr).neg_left.congr'
  (mem_of_superset (Icc_mem_nhds_within_Ioi $ set.left_mem_Ico.2 one_pos) $
    λ x hx, by simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
  eventually_eq.rfl

lemma tendsto_log_div_rpow_nhds_zero {r : ℝ} (hr : r < 0) :
  tendsto (λ x, log x / x ^ r) (𝓝[>] 0) (𝓝 0) :=
(is_o_log_rpow_nhds_zero hr).tendsto_div_nhds_zero

lemma tendsto_log_mul_rpow_nhds_zero {r : ℝ} (hr : 0 < r) :
  tendsto (λ x, log x * x ^ r) (𝓝[>] 0) (𝓝 0) :=
(tendsto_log_div_rpow_nhds_zero $ neg_lt_zero.2 hr).congr' $
  eventually_mem_nhds_within.mono $ λ x hx, by rw [rpow_neg hx.out.le, div_inv_eq_mul]
