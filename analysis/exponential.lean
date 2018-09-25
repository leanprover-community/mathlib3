/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import analysis.real analysis.complex tactic.linarith data.complex.exponential

open finset filter

namespace complex

lemma tendsto_exp_zero_one : tendsto (λ x : ℂ, exp x) (nhds (0 : ℂ)) (nhds (1 : ℂ)) :=
tendsto_nhds_of_metric.2 $ λ ε ε0,
  ⟨min (ε / 2) 1, lt_min (div_pos ε0 (by norm_num)) (by norm_num),
    λ x h, have h : abs x < min (ε / 2) 1, by simpa [dist_eq] using h,
      calc abs (exp x - 1) ≤ 2 * abs x : abs_exp_sub_one_le
        (le_trans (le_of_lt h) (min_le_right _ _))
      ... = abs x + abs x : two_mul (abs x)
      ... < ε / 2 + ε / 2 : add_lt_add
        (lt_of_lt_of_le h (min_le_left _ _)) (lt_of_lt_of_le h (min_le_left _ _))
      ... = ε : by rw add_halves⟩

lemma continuous_exp : continuous exp :=
continuous_iff_tendsto.2 (λ x,
  have H1 : tendsto (λ h, exp (x + h)) (nhds 0) (nhds (exp x)),
    by simpa [exp_add] using tendsto_mul tendsto_const_nhds tendsto_exp_zero_one,
  have H2 : tendsto (λ y, y - x) (nhds x) (nhds (x - x)) :=
     tendsto_sub tendsto_id (@tendsto_const_nhds _ _ _ x _),
  suffices tendsto ((λ h, exp (x + h)) ∘
    (λ y, id y - (λ z, x) y)) (nhds x) (nhds (exp x)),
    by simp only [function.comp, add_sub_cancel'_right, id.def] at this;
      exact this,
  tendsto.comp (by rw [sub_self] at H2; exact H2) H1)

lemma continuous_sin : continuous sin :=
_root_.continuous_mul
  (_root_.continuous_mul
    (_root_.continuous_sub
      (continuous.comp (_root_.continuous_mul continuous_neg' continuous_const) continuous_exp)
      (continuous.comp (_root_.continuous_mul continuous_id continuous_const) continuous_exp))
    continuous_const)
  continuous_const

lemma continuous_cos : continuous cos :=
_root_.continuous_mul
  (_root_.continuous_add
    (continuous.comp (_root_.continuous_mul continuous_id continuous_const) continuous_exp)
    (continuous.comp (_root_.continuous_mul continuous_neg' continuous_const) continuous_exp))
  continuous_const

lemma continuous_sinh : continuous sinh :=
_root_.continuous_mul
  (_root_.continuous_sub
    continuous_exp
    (continuous.comp continuous_neg' continuous_exp))
  continuous_const

lemma continuous_cosh : continuous cosh :=
_root_.continuous_mul
  (_root_.continuous_add
    continuous_exp
    (continuous.comp continuous_neg' continuous_exp))
  continuous_const

end complex

namespace real

lemma continuous_exp : continuous exp :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_exp)
  complex.continuous_re

lemma continuous_sin : continuous sin :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_sin)
  complex.continuous_re

lemma continuous_cos : continuous cos :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_cos)
  complex.continuous_re

lemma continuous_sinh : continuous sinh :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_sinh)
  complex.continuous_re

lemma continuous_cosh : continuous cosh :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_cosh)
  complex.continuous_re

private lemma exists_exp_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : ∃ y, real.exp y = x :=
let ⟨y, hy⟩ := @intermediate_value real.exp 0 (x - 1) x
  (λ _ _ _, continuous_iff_tendsto.1 continuous_exp _) (by simpa)
  (by simpa using complex.add_one_le_exp_aux (sub_nonneg.2 hx)) (sub_nonneg.2 hx) in
⟨y, hy.2.2⟩

lemma exists_exp_eq_of_pos {x : ℝ} (hx : 0 < x) : ∃ y, real.exp y = x :=
(le_total x 1).elim
(λ hx1, let ⟨y, hy⟩ := exists_exp_eq_of_one_le (one_le_inv hx hx1) in
  ⟨-y, by rw [exp_neg, hy, inv_inv']⟩)
exists_exp_eq_of_one_le

noncomputable def ln (x : ℝ) : ℝ :=
if hx : 0 < x then classical.some (exists_exp_eq_of_pos hx) else 0

lemma exp_ln {x : ℝ} (hx : 0 < x) : exp (ln x) = x :=
by rw [ln, dif_pos hx]; exact classical.some_spec (exists_exp_eq_of_pos hx)

@[simp] lemma ln_exp (x : ℝ) : ln (exp x) = x :=
complex.exp_injective $ by rw exp_ln (complex.exp_pos x)

lemma exists_cos_eq_zero : ∃ x, 1 ≤ x ∧ x ≤ 2 ∧ cos x = 0 :=
real.intermediate_value'
  (λ x _ _, continuous_iff_tendsto.1 continuous_cos _)
  (le_of_lt complex.cos_one_pos)
  (le_of_lt complex.cos_two_neg) (by norm_num)

noncomputable def pi : ℝ := 2 * classical.some exists_cos_eq_zero

local notation `π` := pi

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).2.2

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← mul_div_cancel_left pi (@two_ne_zero ℝ _), two_mul, add_div,
    sin_add, cos_pi_div_two]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← mul_div_cancel_left pi (@two_ne_zero ℝ _), mul_div_assoc,
    cos_two_mul, cos_pi_div_two];
  simp [bit0, pow_add]

lemma sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
by rw [sin_add, sin_pi, cos_pi]; simp

lemma cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
by rw [cos_add, cos_pi, sin_pi]; simp

end real