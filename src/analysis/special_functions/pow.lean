/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import analysis.special_functions.pow_continuity

/-!
# Power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

This file is intended for lemmas and tactics involving power functions on several of the rings
`ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/

noncomputable theory

open_locale classical real topology nnreal ennreal filter big_operators complex_conjugate
open filter finset set

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

namespace complex

/-- See also `continuous_at_cpow` and `complex.continuous_at_cpow_of_re_pos`. -/
lemma continuous_at_cpow_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
  continuous_at (λ x : ℂ × ℂ, x.1 ^ x.2) (0, z) :=
begin
  have hz₀ : z ≠ 0, from ne_of_apply_ne re hz.ne',
  rw [continuous_at, zero_cpow hz₀, tendsto_zero_iff_norm_tendsto_zero],
  refine squeeze_zero (λ _, norm_nonneg _) (λ _, abs_cpow_le _ _) _,
  simp only [div_eq_mul_inv, ← real.exp_neg],
  refine tendsto.zero_mul_is_bounded_under_le _ _,
  { convert (continuous_fst.norm.tendsto _).rpow ((continuous_re.comp continuous_snd).tendsto _) _;
      simp [hz, real.zero_rpow hz.ne'] },
  { simp only [(∘), real.norm_eq_abs, abs_of_pos (real.exp_pos _)],
    rcases exists_gt (|im z|) with ⟨C, hC⟩,
    refine ⟨real.exp (π * C), eventually_map.2 _⟩,
    refine (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually
      (gt_mem_nhds hC)).mono (λ z hz, real.exp_le_exp.2 $ (neg_le_abs_self _).trans _),
    rw _root_.abs_mul,
    exact mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le
      (_root_.abs_nonneg _) real.pi_pos.le }
end

/-- See also `continuous_at_cpow` for a version that assumes `p.1 ≠ 0` but makes no
assumptions about `p.2`. -/
lemma continuous_at_cpow_of_re_pos {p : ℂ × ℂ} (h₁ : 0 ≤ p.1.re ∨ p.1.im ≠ 0) (h₂ : 0 < p.2.re) :
  continuous_at (λ x : ℂ × ℂ, x.1 ^ x.2) p :=
begin
  cases p with z w,
  rw [← not_lt_zero_iff, lt_iff_le_and_ne, not_and_distrib, ne.def, not_not, not_le_zero_iff] at h₁,
  rcases h₁ with h₁|(rfl : z = 0),
  exacts [continuous_at_cpow h₁, continuous_at_cpow_zero_of_re_pos h₂]
end

/-- See also `continuous_at_cpow_const` for a version that assumes `z ≠ 0` but makes no
assumptions about `w`. -/
lemma continuous_at_cpow_const_of_re_pos {z w : ℂ} (hz : 0 ≤ re z ∨ im z ≠ 0) (hw : 0 < re w) :
  continuous_at (λ x, x ^ w) z :=
tendsto.comp (@continuous_at_cpow_of_re_pos (z, w) hz hw)
  (continuous_at_id.prod continuous_at_const)

/-- Continuity of `(x, y) ↦ x ^ y` as a function on `ℝ × ℂ`. -/
lemma continuous_at_of_real_cpow (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
  continuous_at (λ p, ↑p.1 ^ p.2 : ℝ × ℂ → ℂ) (x, y) :=
begin
  rcases lt_trichotomy 0 x with hx | rfl | hx,
  { -- x > 0 : easy case
    have : continuous_at (λ p, ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y),
      from continuous_of_real.continuous_at.prod_map continuous_at_id,
    refine (continuous_at_cpow (or.inl _)).comp this,
    rwa of_real_re },
  { -- x = 0 : reduce to continuous_at_cpow_zero_of_re_pos
    have A : continuous_at (λ p, p.1 ^ p.2 : ℂ × ℂ → ℂ) ⟨↑(0:ℝ), y⟩,
    { rw of_real_zero,
      apply continuous_at_cpow_zero_of_re_pos,
      tauto },
    have B : continuous_at (λ p, ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) ⟨0, y⟩,
      from continuous_of_real.continuous_at.prod_map continuous_at_id,
    exact @continuous_at.comp (ℝ × ℂ) (ℂ × ℂ) ℂ _ _ _ _ (λ p, ⟨↑p.1, p.2⟩) ⟨0, y⟩ A B },
  { -- x < 0 : difficult case
    suffices : continuous_at (λ p, (-↑p.1) ^ p.2 * exp (π * I * p.2) : ℝ × ℂ → ℂ) (x, y),
    { refine this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) _),
      exact λ p hp, (of_real_cpow_of_nonpos (le_of_lt hp.1) p.2).symm },
    have A : continuous_at (λ p, ⟨-↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y),
      from continuous_at.prod_map (continuous_of_real.continuous_at.neg) continuous_at_id,
    apply continuous_at.mul,
    { refine (continuous_at_cpow (or.inl _)).comp A,
      rwa [neg_re, of_real_re, neg_pos] },
    { exact (continuous_exp.comp (continuous_const.mul continuous_snd)).continuous_at } },
end

lemma continuous_at_of_real_cpow_const (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
  continuous_at (λ a, a ^ y : ℝ → ℂ) x :=
@continuous_at.comp _ _ _ _ _ _ _ _ x (continuous_at_of_real_cpow x y h)
  (continuous_id.prod_mk continuous_const).continuous_at

lemma continuous_of_real_cpow_const {y : ℂ} (hs : 0 < y.re) : continuous (λ x, x ^ y : ℝ → ℂ) :=
continuous_iff_continuous_at.mpr (λ x, continuous_at_of_real_cpow_const x y (or.inl hs))

end complex

namespace real
variables {n : ℕ}

lemma exists_rat_pow_btwn_rat_aux (hn : n ≠ 0) (x y : ℝ) (h : x < y) (hy : 0 < y) :
  ∃ q : ℚ, 0 < q ∧ x < q^n ∧ ↑q^n < y :=
begin
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn.bot_lt,
  obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn (rpow_lt_rpow (le_max_left 0 x) (max_lt hy h) $
    inv_pos.mpr hn'),
  have := rpow_nonneg_of_nonneg (le_max_left 0 x) n⁻¹,
  have hq := this.trans_lt hxq,
  replace hxq := rpow_lt_rpow this hxq hn',
  replace hqy := rpow_lt_rpow hq.le hqy hn',
  rw [rpow_nat_cast, rpow_nat_cast, rpow_nat_inv_pow_nat _ hn] at hxq hqy,
  exact ⟨q, by exact_mod_cast hq, (le_max_right _ _).trans_lt hxq, hqy⟩,
  { exact le_max_left _ _ },
  { exact hy.le }
end

lemma exists_rat_pow_btwn_rat (hn : n ≠ 0) {x y : ℚ} (h : x < y) (hy : 0 < y) :
  ∃ q : ℚ, 0 < q ∧ x < q^n ∧ q^n < y :=
by apply_mod_cast exists_rat_pow_btwn_rat_aux hn x y; assumption

/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
lemma exists_rat_pow_btwn {α : Type*} [linear_ordered_field α] [archimedean α] (hn : n ≠ 0)
  {x y : α} (h : x < y) (hy : 0 < y) : ∃ q : ℚ, 0 < q ∧ x < q^n ∧ (q^n : α) < y :=
begin
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy),
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂,
  have : (0 : α) < q₂ := (le_max_right _ _).trans_lt hx₂,
  norm_cast at hq₁₂ this,
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_rat_pow_btwn_rat hn hq₁₂ this,
  refine ⟨q, hq, (le_max_left _ _).trans_lt $ hx₁.trans _, hy₂.trans' _⟩; assumption_mod_cast,
end

end real

/-!
## Tactics for power computations
-/

namespace norm_num
open tactic

theorem rpow_pos (a b : ℝ) (b' : ℕ) (c : ℝ) (hb : (b':ℝ) = b) (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, ← hb, real.rpow_nat_cast]
theorem rpow_neg (a b : ℝ) (b' : ℕ) (c c' : ℝ)
  (a0 : 0 ≤ a) (hb : (b':ℝ) = b) (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, ← hb, real.rpow_neg a0, real.rpow_nat_cast]

/-- Evaluate `real.rpow a b` where `a` is a rational numeral and `b` is an integer.
(This cannot go via the generalized version `prove_rpow'` because `rpow_pos` has a side condition;
we do not attempt to evaluate `a ^ b` where `a` and `b` are both negative because it comes
out to some garbage.) -/
meta def prove_rpow (a b : expr) : tactic (expr × expr) := do
  na ← a.to_rat,
  ic ← mk_instance_cache `(ℝ),
  match match_sign b with
  | sum.inl b := do
    (ic, a0) ← guard (na ≥ 0) >> prove_nonneg ic a,
    nc ← mk_instance_cache `(ℕ),
    (ic, nc, b', hb) ← prove_nat_uncast ic nc b,
    (ic, c, h) ← prove_pow a na ic b',
    cr ← c.to_rat,
    (ic, c', hc) ← prove_inv ic c cr,
    pure (c', (expr.const ``rpow_neg []).mk_app [a, b, b', c, c', a0, hb, h, hc])
  | sum.inr ff := pure (`(1:ℝ), expr.const ``real.rpow_zero [] a)
  | sum.inr tt := do
    nc ← mk_instance_cache `(ℕ),
    (ic, nc, b', hb) ← prove_nat_uncast ic nc b,
    (ic, c, h) ← prove_pow a na ic b',
    pure (c, (expr.const ``rpow_pos []).mk_app [a, b, b', c, hb, h])
  end

/-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
meta def prove_rpow' (pos neg zero : name) (α β one a b : expr) : tactic (expr × expr) := do
  na ← a.to_rat,
  icα ← mk_instance_cache α,
  icβ ← mk_instance_cache β,
  match match_sign b with
  | sum.inl b := do
    nc ← mk_instance_cache `(ℕ),
    (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b,
    (icα, c, h) ← prove_pow a na icα b',
    cr ← c.to_rat,
    (icα, c', hc) ← prove_inv icα c cr,
    pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
  | sum.inr ff := pure (one, expr.const zero [] a)
  | sum.inr tt := do
    nc ← mk_instance_cache `(ℕ),
    (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b,
    (icα, c, h) ← prove_pow a na icα b',
    pure (c, (expr.const pos []).mk_app [a, b, b', c, hb, h])
  end

open_locale nnreal ennreal

theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, hb, complex.cpow_nat_cast]
theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ)
  (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, hb, complex.cpow_neg, complex.cpow_nat_cast]

theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0)
  (hb : b = b') (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, hb, nnreal.rpow_nat_cast]
theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0)
  (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, hb, nnreal.rpow_neg, nnreal.rpow_nat_cast]

theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞)
  (hb : b = b') (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, hb, ennreal.rpow_nat_cast]
theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞)
  (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, hb, ennreal.rpow_neg, ennreal.rpow_nat_cast]

/-- Evaluate `complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
meta def prove_cpow : expr → expr → tactic (expr × expr) :=
prove_rpow' ``cpow_pos ``cpow_neg ``complex.cpow_zero `(ℂ) `(ℂ) `(1:ℂ)

/-- Evaluate `nnreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
meta def prove_nnrpow : expr → expr → tactic (expr × expr) :=
prove_rpow' ``nnrpow_pos ``nnrpow_neg ``nnreal.rpow_zero `(ℝ≥0) `(ℝ) `(1:ℝ≥0)

/-- Evaluate `ennreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
meta def prove_ennrpow : expr → expr → tactic (expr × expr) :=
prove_rpow' ``ennrpow_pos ``ennrpow_neg ``ennreal.rpow_zero `(ℝ≥0∞) `(ℝ) `(1:ℝ≥0∞)

/-- Evaluates expressions of the form `rpow a b`, `cpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num] meta def eval_rpow_cpow : expr → tactic (expr × expr)
| `(@has_pow.pow _ _ real.has_pow %%a %%b) := b.to_int >> prove_rpow a b
| `(real.rpow %%a %%b) := b.to_int >> prove_rpow a b
| `(@has_pow.pow _ _ complex.has_pow %%a %%b) := b.to_int >> prove_cpow a b
| `(complex.cpow %%a %%b) := b.to_int >> prove_cpow a b
| `(@has_pow.pow _ _ nnreal.real.has_pow %%a %%b) := b.to_int >> prove_nnrpow a b
| `(nnreal.rpow %%a %%b) := b.to_int >> prove_nnrpow a b
| `(@has_pow.pow _ _ ennreal.real.has_pow %%a %%b) := b.to_int >> prove_ennrpow a b
| `(ennreal.rpow %%a %%b) := b.to_int >> prove_ennrpow a b
| _ := tactic.failed

end norm_num

namespace tactic
namespace positivity

/-- Auxiliary definition for the `positivity` tactic to handle real powers of reals. -/
meta def prove_rpow (a b : expr) : tactic strictness :=
do
  strictness_a ← core a,
  match strictness_a with
  | nonnegative p := nonnegative <$> mk_app ``real.rpow_nonneg_of_nonneg [p, b]
  | positive p := positive <$> mk_app ``real.rpow_pos_of_pos [p, b]
  | _ := failed
  end

private lemma nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b := nnreal.rpow_pos ha

/-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals. -/
meta def prove_nnrpow (a b : expr) : tactic strictness :=
do
  strictness_a ← core a,
  match strictness_a with
  | positive p := positive <$> mk_app ``nnrpow_pos [p, b]
  | _ := failed -- We already know `0 ≤ x` for all `x : ℝ≥0`
  end

private lemma ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
ennreal.rpow_pos_of_nonneg ha hb.le

/-- Auxiliary definition for the `positivity` tactic to handle real powers of extended nonnegative
reals. -/
meta def prove_ennrpow (a b : expr) : tactic strictness :=
do
  strictness_a ← core a,
  strictness_b ← core b,
  match strictness_a, strictness_b with
  | positive pa, positive pb := positive <$> mk_app ``ennrpow_pos [pa, pb]
  | positive pa, nonnegative pb := positive <$> mk_app ``ennreal.rpow_pos_of_nonneg [pa, pb]
  | _, _ := failed -- We already know `0 ≤ x` for all `x : ℝ≥0∞`
  end

end positivity

open positivity

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when the
base is nonnegative and positive when the base is positive. -/
@[positivity]
meta def positivity_rpow : expr → tactic strictness
| `(@has_pow.pow _ _ real.has_pow %%a %%b) := prove_rpow a b
| `(real.rpow %%a %%b) := prove_rpow a b
| `(@has_pow.pow _ _ nnreal.real.has_pow %%a %%b) := prove_nnrpow a b
| `(nnreal.rpow %%a %%b) := prove_nnrpow a b
| `(@has_pow.pow _ _ ennreal.real.has_pow %%a %%b) := prove_ennrpow a b
| `(ennreal.rpow %%a %%b) := prove_ennrpow a b
| _ := failed

end tactic
