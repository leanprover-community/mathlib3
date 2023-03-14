/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.special_functions.pow
import analysis.asymptotics.asymptotic_equivalent
import analysis.asymptotics.specific_asymptotics

/-!
# Growth estimates on `x ^ y` for complex `x`, `y`

Let `l` be a filter on `ℂ` such that `complex.re` tends to infinity along `l` and `complex.im z`
grows at a subexponential rate compared to `complex.re z`. Then

- `complex.is_o_log_abs_re_of_subexponential_im_re`: `real.log ∘ complex.abs` is `o`-small of
  `complex.re` along `l`;

- `complex.is_o_cpow_mul_exp`: $z^{a_1}e^{b_1 * z} = o\left(z^{a_1}e^{b_1 * z}\right)$ along `l`
  for any complex `a₁`, `a₂` and real `b₁ < b₂`.

We use these assumptions on `l` for two reasons. First, these are the assumptions that naturally
appear in the proof. Second, in some applications (e.g., in Ilyashenko's proof of the individual
finiteness theorem for limit cycles of polynomial ODEs with hyperbolic singularities only) natural
stronger assumptions (e.g., `im z` is bounded from below and from above) are not available.

-/

open asymptotics filter function
open_locale topology

namespace complex

/-- We say that `l : filter ℂ` is an *exponential comparison filter* if the real part tends to
infinity along `l` and the imaginary part grows subexponentially compared to the real part. These
properties guarantee that `(λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z))` for any
complex `a₁`, `a₂` and real `b₁ < b₂`.

In particular, the second property is automatically satisfied if the imaginary part is bounded along
`l`. -/
structure is_exp_cmp_filter (l : filter ℂ) : Prop :=
(tendsto_re : tendsto re l at_top)
(is_O_im_pow_re : ∀ n : ℕ, (λ z : ℂ, z.im ^ n) =O[l] (λ z, real.exp z.re))

namespace is_exp_cmp_filter

variables {l : filter ℂ}

/-!
### Alternative constructors
-/

lemma of_is_O_im_re_rpow (hre : tendsto re l at_top) (r : ℝ) (hr : im =O[l] (λ z, z.re ^ r)) :
  is_exp_cmp_filter l :=
⟨hre, λ n, is_o.is_O $
  calc (λ z : ℂ, z.im ^ n) =O[l] (λ z, (z.re ^ r) ^ n) : hr.pow n
  ... =ᶠ[l] (λ z, z.re ^ (r * n)) : (hre.eventually_ge_at_top 0).mono $
    λ z hz, by simp only [real.rpow_mul hz r n, real.rpow_nat_cast]
  ... =o[l] (λ z, real.exp z.re) : (is_o_rpow_exp_at_top _).comp_tendsto hre⟩

lemma of_is_O_im_re_pow (hre : tendsto re l at_top) (n : ℕ) (hr : im =O[l] (λ z, z.re ^ n)) :
  is_exp_cmp_filter l :=
of_is_O_im_re_rpow hre n $ by simpa only [real.rpow_nat_cast]

lemma of_bounded_under_abs_im (hre : tendsto re l at_top)
  (him : is_bounded_under (≤) l (λ z, |z.im|)) :
  is_exp_cmp_filter l :=
of_is_O_im_re_pow hre 0 $
  by simpa only [pow_zero] using @is_bounded_under.is_O_const ℂ ℝ ℝ _ _ _ l him 1 one_ne_zero

lemma of_bounded_under_im (hre : tendsto re l at_top) (him_le : is_bounded_under (≤) l im)
  (him_ge : is_bounded_under (≥) l im) :
  is_exp_cmp_filter l :=
of_bounded_under_abs_im hre $ is_bounded_under_le_abs.2 ⟨him_le, him_ge⟩

/-!
### Preliminary lemmas
-/

lemma eventually_ne (hl : is_exp_cmp_filter l) : ∀ᶠ w : ℂ in l, w ≠ 0 :=
hl.tendsto_re.eventually_ne_at_top' _

lemma tendsto_abs_re (hl : is_exp_cmp_filter l) : tendsto (λ z : ℂ, |z.re|) l at_top :=
tendsto_abs_at_top_at_top.comp hl.tendsto_re

lemma tendsto_abs (hl : is_exp_cmp_filter l) : tendsto abs l at_top :=
tendsto_at_top_mono abs_re_le_abs hl.tendsto_abs_re

lemma is_o_log_re_re (hl : is_exp_cmp_filter l) : (λ z, real.log z.re) =o[l] re :=
real.is_o_log_id_at_top.comp_tendsto hl.tendsto_re

lemma is_o_im_pow_exp_re (hl : is_exp_cmp_filter l) (n : ℕ) :
  (λ z : ℂ, z.im ^ n) =o[l] (λ z, real.exp z.re) :=
flip is_o.of_pow two_ne_zero $
  calc (λ z : ℂ, (z.im ^ n) ^ 2) = (λ z, z.im ^ (2 * n)) : by simp only [pow_mul']
  ... =O[l] (λ z, real.exp z.re) : hl.is_O_im_pow_re _
  ... =     (λ z, (real.exp z.re) ^ 1) : by simp only [pow_one]
  ... =o[l] (λ z, (real.exp z.re) ^ 2) : (is_o_pow_pow_at_top_of_lt one_lt_two).comp_tendsto $
    real.tendsto_exp_at_top.comp hl.tendsto_re

lemma abs_im_pow_eventually_le_exp_re (hl : is_exp_cmp_filter l) (n : ℕ) :
  (λ z : ℂ, |z.im| ^ n) ≤ᶠ[l] (λ z, real.exp z.re) :=
by simpa using (hl.is_o_im_pow_exp_re n).bound zero_lt_one

/-- If `l : filter ℂ` is an "exponential comparison filter", then $\log |z| =o(ℜ z)$ along `l`.
This is the main lemma in the proof of `complex.is_exp_cmp_filter.is_o_cpow_exp` below.
-/
lemma is_o_log_abs_re (hl : is_exp_cmp_filter l) : (λ z, real.log (abs z)) =o[l] re :=
calc (λ z, real.log (abs z)) =O[l] (λ z, real.log (real.sqrt 2) + real.log (max z.re (|z.im|))) :
  is_O.of_bound 1 $ (hl.tendsto_re.eventually_ge_at_top 1).mono $ λ z hz,
    begin
      have h2 : 0 < real.sqrt 2, by simp,
      have hz' : 1 ≤ abs z, from hz.trans (re_le_abs z),
      have hz₀ : 0 < abs z, from one_pos.trans_le hz',
      have hm₀ : 0 < max z.re (|z.im|), from lt_max_iff.2 (or.inl $ one_pos.trans_le hz),
      rw [one_mul, real.norm_eq_abs, _root_.abs_of_nonneg (real.log_nonneg hz')],
      refine le_trans _ (le_abs_self _),
      rw [← real.log_mul, real.log_le_log, ← _root_.abs_of_nonneg (le_trans zero_le_one hz)],
      exacts [abs_le_sqrt_two_mul_max z, one_pos.trans_le hz', (mul_pos h2 hm₀), h2.ne', hm₀.ne']
    end
... =o[l] re : is_o.add (is_o_const_left.2 $ or.inr $ hl.tendsto_abs_re) $ is_o_iff_nat_mul_le.2 $
  λ n, begin
    filter_upwards [is_o_iff_nat_mul_le.1 hl.is_o_log_re_re n, hl.abs_im_pow_eventually_le_exp_re n,
      hl.tendsto_re.eventually_gt_at_top 1] with z hre him h₁,
    cases le_total (|z.im|) z.re with hle hle,
    { rwa [max_eq_left hle] },
    { have H : 1 < |z.im|, from h₁.trans_le hle,
      rwa [max_eq_right hle, real.norm_eq_abs, real.norm_eq_abs, abs_of_pos (real.log_pos H),
        ← real.log_pow, real.log_le_iff_le_exp (pow_pos (one_pos.trans H) _),
        abs_of_pos (one_pos.trans h₁)] }
  end

/-!
### Main results
-/

/-- If `l : filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
positive real `b`, we have `(λ z, z ^ a) =o[l] (λ z, exp (b * z))`. -/
lemma is_o_cpow_exp (hl : is_exp_cmp_filter l) (a : ℂ) {b : ℝ} (hb : 0 < b) :
  (λ z, z ^ a) =o[l] (λ z, exp (b * z)) :=
calc (λ z, z ^ a) =Θ[l] λ z, abs z ^ re a : is_Theta_cpow_const_rpow $ λ _ _, hl.eventually_ne
... =ᶠ[l] λ z, real.exp (re a * real.log (abs z)) : hl.eventually_ne.mono $
  λ z hz, by simp only [real.rpow_def_of_pos, abs.pos hz, mul_comm]
... =o[l] λ z, exp (b * z) : is_o.of_norm_right $
  begin
    simp only [norm_eq_abs, abs_exp, of_real_mul_re, real.is_o_exp_comp_exp_comp],
    refine (is_equivalent.refl.sub_is_o _).symm.tendsto_at_top (hl.tendsto_re.const_mul_at_top hb),
    exact (hl.is_o_log_abs_re.const_mul_left _).const_mul_right hb.ne'
  end

/-- If `l : filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
real `b₁ < b₂`, we have `(λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z))`. -/
lemma is_o_cpow_mul_exp {b₁ b₂ : ℝ} (hl : is_exp_cmp_filter l) (hb : b₁ < b₂) (a₁ a₂ : ℂ) :
  (λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z)) :=
calc (λ z, z ^ a₁ * exp (b₁ * z)) =ᶠ[l] (λ z, z ^ a₂ * exp (b₁ * z) * z ^ (a₁ - a₂)) :
  hl.eventually_ne.mono $ λ z hz,
    by { simp only, rw [mul_right_comm, ← cpow_add _ _ hz, add_sub_cancel'_right] }
... =o[l] λ z, z ^ a₂ * exp (b₁ * z) * exp (↑(b₂ - b₁) * z) :
  (is_O_refl (λ z, z ^ a₂ * exp (b₁ * z)) l).mul_is_o $ hl.is_o_cpow_exp _ (sub_pos.2 hb)
... =ᶠ[l] λ z, z ^ a₂ * exp (b₂ * z) :
  by simp only [of_real_sub, sub_mul, mul_assoc, ← exp_add, add_sub_cancel'_right]

/-- If `l : filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
negative real `b`, we have `(λ z, exp (b * z)) =o[l] (λ z, z ^ a)`. -/
lemma is_o_exp_cpow (hl : is_exp_cmp_filter l) (a : ℂ) {b : ℝ} (hb : b < 0) :
  (λ z, exp (b * z)) =o[l] (λ z, z ^ a) :=
by simpa using hl.is_o_cpow_mul_exp hb 0 a

/-- If `l : filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
natural `b₁ < b₂`, we have `(λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z))`. -/
lemma is_o_pow_mul_exp {b₁ b₂ : ℝ} (hl : is_exp_cmp_filter l) (hb : b₁ < b₂) (m n : ℕ) :
  (λ z, z ^ m * exp (b₁ * z)) =o[l] (λ z, z ^ n * exp (b₂ * z)) :=
by simpa only [cpow_nat_cast] using hl.is_o_cpow_mul_exp hb m n

/-- If `l : filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
integer `b₁ < b₂`, we have `(λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z))`. -/
lemma is_o_zpow_mul_exp {b₁ b₂ : ℝ} (hl : is_exp_cmp_filter l) (hb : b₁ < b₂) (m n : ℤ) :
  (λ z, z ^ m * exp (b₁ * z)) =o[l] (λ z, z ^ n * exp (b₂ * z)) :=
by simpa only [cpow_int_cast] using hl.is_o_cpow_mul_exp hb m n

end is_exp_cmp_filter

end complex
