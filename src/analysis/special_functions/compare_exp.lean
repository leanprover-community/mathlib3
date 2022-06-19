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

open asymptotics filter
open_locale topological_space

namespace complex

lemma is_o_log_abs_re_of_subexponential_im_re {l : filter ℂ}
  (hl₁ : tendsto re l at_top) (hl₂ : ∀ n : ℕ, ∀ᶠ z : ℂ in l, z.im ^ n ≤ real.exp z.re) :
  (λ z, real.log (abs z)) =o[l] re :=
begin
  have h2 : 0 < real.sqrt 2, by simp,
  calc (λ z, real.log (abs z)) =O[l] (λ z, real.log (real.sqrt 2) + real.log (max z.re (|z.im|))) :
    is_O.of_bound 1 $ (hl₁.eventually_ge_at_top 1).mono $ λ z hz,
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
  ... =o[l] re : is_o.add (is_o_const_left.2 $ or.inr $ tendsto_abs_at_top_at_top.comp hl₁) _,
  refine is_o_iff.2 (λ ε ε₀, _),
  obtain ⟨n, hnε, hn₀, hn⟩ : ∃ n : ℕ, ε⁻¹ < n ∧ 0 < n ∧ even n,
  { rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩,
    refine ⟨2 * n, hn.trans_le $ nat.mono_cast _, _, even_two_mul _⟩,
    exacts [le_mul_of_one_le_left' one_le_two,
      mul_pos two_pos $ nat.cast_pos.1 $ (inv_pos.2 ε₀).trans hn] },
  filter_upwards [(real.is_o_log_id_at_top.comp_tendsto hl₁).bound ε₀, hl₂ n,
    hl₁.eventually_gt_at_top 1] with z hre him h₁,
  cases le_total (|z.im|) z.re with hle hle,
  { rwa [max_eq_left hle] },
  have H : 1 < |z.im|, from h₁.trans_le hle,
  rw [max_eq_right hle, real.norm_eq_abs, real.norm_eq_abs, abs_of_pos (real.log_pos H),
    real.log_le_iff_le_exp (one_pos.trans H)],
  rw [← (@strict_mono_on_pow ℝ _ _ hn₀).le_iff_le (_root_.abs_nonneg z.im) (real.exp_pos _).le],
  simp only [hn.pow_abs, ← real.exp_nat_mul, ← mul_assoc],
  refine him.trans (real.exp_le_exp.2 $ (le_abs_self _).trans _),
  refine le_mul_of_one_le_left (_root_.abs_nonneg _) _,
  rw [← div_le_iff ε₀, one_div],
  exact hnε.le
end

lemma tendsto_cpow_const_mul_exp_const_mul_nhds_zero (a : ℂ) {b : ℝ} {l : filter ℂ}
  (hl₁ : tendsto re l at_top) (hl₂ : ∀ n : ℕ, ∀ᶠ z : ℂ in l, z.im ^ n ≤ real.exp z.re)
  (hb : b < 0) :
  tendsto (λ z, z ^ a * exp (b * z)) l (𝓝 0) :=
begin
  suffices : tendsto (λ z, real.exp (a.re * real.log (abs z) + b * re z)) l (𝓝 0),
  { have h₀ : ∀ᶠ z : ℂ in l, z ≠ 0, from hl₁.eventually_ne_at_top' 0,
    rw [tendsto_zero_iff_norm_tendsto_zero],
    simp only [norm_mul],
    rw [((is_Theta_cpow_const_rpow (λ _ _, h₀)).norm_left.mul is_Theta_rfl).tendsto_zero_iff],
    refine this.congr' (h₀.mono $ λ x hx, _),
    rw [norm_eq_abs, abs_exp, of_real_mul_re, real.rpow_def_of_pos (abs_pos.2 hx), real.exp_add,
      mul_comm a.re] },
  rw [← tendsto_comap_iff, real.comap_exp_nhds_zero],
  refine is_equivalent.tendsto_at_bot _ (tendsto_const_nhds.neg_mul_at_top hb hl₁),
  have : (λ z, real.log (abs z)) =o[l] re,
    from is_o_log_abs_re_of_subexponential_im_re hl₁ hl₂,
  exact (((is_O_const_const _ hb.ne _).mul_is_o this).add_is_equivalent is_equivalent.refl).symm
end

lemma is_o_cpow_const_mul_exp {a₁ a₂ : ℂ} {b₁ b₂ : ℝ} {l : filter ℂ}
  (hl₁ : tendsto re l at_top) (hl₂ : ∀ n : ℕ, ∀ᶠ z : ℂ in l, z.im ^ n ≤ real.exp z.re)
  (hb : b₁ < b₂) :
  (λ z, z ^ a₁ * exp (b₁ * z)) =o[l] (λ z, z ^ a₂ * exp (b₂ * z)) :=
begin
  have h₀ : ∀ᶠ z : ℂ in l, z ≠ 0, from (hl₁.eventually_ne_at_top' (0 : ℂ)),
  refine (is_o_iff_tendsto' (h₀.mono _)).mpr _,
  { intros x hne h,
    exfalso,
    simpa [hne, exp_ne_zero] using h },
  refine (tendsto_cpow_const_mul_exp_const_mul_nhds_zero (a₁ - a₂) hl₁ hl₂ (sub_neg.2 hb)).congr' _,
  filter_upwards [h₀] with z hz,
  rw [mul_div_mul_comm, ← exp_sub, ← sub_mul, ← of_real_sub, cpow_sub _ _ hz]
end

end complex

