/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.special_functions.pow

/-!
# Growth estimates on `x ^ y` for complex `x`, `y`

Let `l` be a filter on `ℂ` such that `complex.re` tends to infinity along `l` and `complex.im z`
grows at a subexponential rate compared to `complex.re z`. Then

- `complex.is_o_log_abs_re_of_subexponential_im_re`: `real.log ∘ complex.abs` is `o`-small of
  `complex.re` along `l`;

- `complex.tendsto_cpow_const_mul_exp_const_mul_nhds_zero`: `z ^ a * exp (b * z)` tends to zero for
  any real negative `b`;

- `complex.is_o_cpow_const_mul_exp`: `z ^ a₁ * exp (b₁ * z)` is `o`-small of `z ^ a₂ * exp (b₂ * z)`
  for any complex `a₁`, `a₂` and real `b₁ < b₂`.
-/

open asymptotics filter function
open_locale topological_space

namespace complex

/-- We say that `l : filter ℂ` is an *exponent comparison filter* if the real part tends to infinity
along `l` and the imaginary part grows subexponentially compared to the real part. These properties
guarantee that `(λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z))` for any complex
`a₁`, `a₂` and real `b₁ < b₂`.

In particular, the second property is automatically satisfied if the imaginary part is bounded along
`l`. -/
structure is_exp_cmp_filter (l : filter ℂ) : Prop :=
(tendsto_re : tendsto re l at_top)
(is_O_im_pow_re : ∀ n : ℕ, (λ z : ℂ, z.im ^ n) =O[l] (λ z, real.exp z.re))

namespace is_exp_cmp_filter

variables {l : filter ℂ}

lemma tendsto_abs_re (hl : is_exp_cmp_filter l) : tendsto (λ z : ℂ, |z.re|) l at_top :=
tendsto_abs_at_top_at_top.comp hl.tendsto_re

lemma tendsto_abs (hl : is_exp_cmp_filter l) : tendsto abs l at_top :=
tendsto_at_top_mono abs_re_le_abs hl.tendsto_abs_re

lemma is_o_log_re_re (hl : is_exp_cmp_filter l) : (λ z, real.log z.re) =o[l] re :=
real.is_o_log_id_at_top.comp_tendsto hl.tendsto_re

#check is_O.rpow
lemma is_o_im_pow_re (hl : is_exp_cmp_filter l) (n : ℕ) :
  (λ z : ℂ, z.im ^ n) =o[l] (λ z, real.exp z.re) :=
calc (λ z : ℂ, z.im ^ n) =O[l] (λ z, real.exp (2⁻¹ * z.re)) :
  by simpa using (hl.2 (2 * n)).rpow _ _
... =o[l] (λ z, real.exp z.re) :
  _

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

lemma is_o_log_abs_re (hl : is_exp_cmp_filter l) : (λ z, real.log (abs z)) =o[l] re :=
begin
  have h2 : 0 < real.sqrt 2, by simp,
  calc (λ z, real.log (abs z)) =O[l] (λ z, real.log (real.sqrt 2) + real.log (max z.re (|z.im|))) :
    is_O.of_bound 1 $ (hl.tendsto_re.eventually_ge_at_top 1).mono $ λ z hz,
      begin
        have hz' : 1 ≤ abs z, from hz.trans (re_le_abs z),
        have hz₀ : 0 < abs z, from one_pos.trans_le hz',
        have hm₀ : 0 < max z.re (|z.im|), from lt_max_iff.2 (or.inl $ one_pos.trans_le hz),
        rw [one_mul, real.norm_eq_abs, _root_.abs_of_nonneg (real.log_nonneg hz')],
        refine le_trans _ (le_abs_self _),
        rw [← real.log_mul, real.log_le_log,
          ← _root_.abs_of_nonneg (le_trans zero_le_one hz)],
        exacts [abs_le_sqrt_two_mul_max z, one_pos.trans_le hz', (mul_pos h2 hm₀), h2.ne', hm₀.ne']
      end
  ... =o[l] re : is_o.add (is_o_const_left.2 $ or.inr $ hl.tendsto_abs_re) _,
  refine is_o_iff.2 (λ ε ε₀, _),
  rcases exists_nat_ge ε⁻¹ with ⟨n, hn⟩,
  have hn₀ : 0 < n, from nat.cast_pos.1 ((inv_pos.2 ε₀).trans_le hn),
  filter_upwards [hl.is_o_log_re_re.bound ε₀, hl.im_pow_le_re n,
    hl.tendsto_re.eventually_gt_at_top 1] with z hre him h₁,
  cases le_total (|z.im|) z.re with hle hle,
  { rwa [max_eq_left hle] },
  have H : 1 < |z.im|, from h₁.trans_le hle,
  rw [max_eq_right hle, real.norm_eq_abs, real.norm_eq_abs, abs_of_pos (real.log_pos H),
    real.log_le_iff_le_exp (one_pos.trans H)],
  refine le_of_pow_le_pow _ (real.exp_pos _).le hn₀ _,
  simp only [← real.exp_nat_mul, ← mul_assoc],
  refine him.trans (real.exp_le_exp.2 $ (le_abs_self _).trans _),
  refine le_mul_of_one_le_left (_root_.abs_nonneg _) _,
  rwa [← div_le_iff ε₀, one_div]
end

lemma tendsto_cpow_const_mul_exp_const_mul_nhds_zero (hl : is_exp_cmp_filter l) (a : ℂ) {b : ℝ}
  (hb : b < 0) : tendsto (λ z, z ^ a * exp (b * z)) l (𝓝 0) :=
begin
  suffices : tendsto (λ z, real.exp (a.re * real.log (abs z) + b * re z)) l (𝓝 0),
  { have h₀ : ∀ᶠ z : ℂ in l, z ≠ 0, from hl.1.eventually_ne_at_top' 0,
    rw [tendsto_zero_iff_norm_tendsto_zero],
    simp only [norm_mul],
    rw [((is_Theta_cpow_const_rpow (λ _ _, h₀)).norm_left.mul is_Theta_rfl).tendsto_zero_iff],
    refine this.congr' (h₀.mono $ λ x hx, _),
    rw [norm_eq_abs, abs_exp, of_real_mul_re, real.rpow_def_of_pos (abs_pos.2 hx), real.exp_add,
      mul_comm a.re] },
  rw [← tendsto_comap_iff, real.comap_exp_nhds_zero],
  refine is_equivalent.tendsto_at_bot _ (tendsto_const_nhds.neg_mul_at_top hb hl.1),
  exact (((is_O_const_const _ hb.ne _).mul_is_o hl.is_o_log_abs_re).add_is_equivalent
    is_equivalent.refl).symm
end

lemma is_o_cpow_const_mul_exp {b₁ b₂ : ℝ} (hl : is_exp_cmp_filter l) (hb : b₁ < b₂) (a₁ a₂ : ℂ) :
  (λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z)) :=
begin
  have h₀ : ∀ᶠ z : ℂ in l, z ≠ 0, from (hl.1.eventually_ne_at_top' (0 : ℂ)),
  refine (is_o_iff_tendsto' (h₀.mono _)).mpr _,
  { intros x hne h,
    exfalso,
    simpa [hne, exp_ne_zero] using h },
  refine (hl.tendsto_cpow_const_mul_exp_const_mul_nhds_zero (a₁ - a₂) (sub_neg.2 hb)).congr' _,
  filter_upwards [h₀] with z hz,
  rw [mul_div_mul_comm, ← exp_sub, ← sub_mul, ← of_real_sub, cpow_sub _ _ hz]
end

end is_exp_cmp_filter

end complex

