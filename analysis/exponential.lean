/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import analysis.real analysis.complex tactic.linarith data.complex.exponential

open finset filter

namespace complex

lemma tendsto_exp_zero_one : tendsto exp (nhds 0) (nhds 1) :=
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

lemma continuous_tan : continuous (λ x : {x // cos x ≠ 0}, tan x) :=
_root_.continuous_mul
  (continuous.comp continuous_subtype_val continuous_sin)
  (continuous_inv subtype.property
    (continuous.comp continuous_subtype_val continuous_cos))

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

lemma continuous_tan : continuous (λ x : {x // cos x ≠ 0}, tan x) :=
by simp only [tan_eq_sin_div_cos]; exact
_root_.continuous_mul
  (continuous.comp continuous_subtype_val continuous_sin)
  (continuous_inv subtype.property
    (continuous.comp continuous_subtype_val continuous_cos))

lemma continuous_sinh : continuous sinh :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_sinh)
  complex.continuous_re

lemma continuous_cosh : continuous cosh :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_cosh)
  complex.continuous_re

private lemma exists_exp_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : ∃ y, exp y = x :=
let ⟨y, hy⟩ := @intermediate_value real.exp 0 (x - 1) x
  (λ _ _ _, continuous_iff_tendsto.1 continuous_exp _) (by simpa)
  (by simpa using add_one_le_exp_of_nonneg (sub_nonneg.2 hx)) (sub_nonneg.2 hx) in
⟨y, hy.2.2⟩

lemma exists_exp_eq_of_pos {x : ℝ} (hx : 0 < x) : ∃ y, exp y = x :=
(le_total x 1).elim
(λ hx1, let ⟨y, hy⟩ := exists_exp_eq_of_one_le (one_le_inv hx hx1) in
  ⟨-y, by rw [exp_neg, hy, inv_inv']⟩)
exists_exp_eq_of_one_le

noncomputable def ln (x : ℝ) : ℝ :=
if hx : 0 < x then classical.some (exists_exp_eq_of_pos hx) else 0

lemma exp_ln {x : ℝ} (hx : 0 < x) : exp (ln x) = x :=
by rw [ln, dif_pos hx]; exact classical.some_spec (exists_exp_eq_of_pos hx)

@[simp] lemma ln_exp (x : ℝ) : ln (exp x) = x :=
exp_injective $ exp_ln (exp_pos x)

@[simp] lemma ln_one : ln 1 = 0 :=
exp_injective $ by rw [exp_ln zero_lt_one, exp_zero]

lemma exists_cos_eq_zero : ∃ x, 1 ≤ x ∧ x ≤ 2 ∧ cos x = 0 :=
real.intermediate_value'
  (λ x _ _, continuous_iff_tendsto.1 continuous_cos _)
  (le_of_lt cos_one_pos)
  (le_of_lt cos_two_neg) (by norm_num)

noncomputable def pi : ℝ := 2 * classical.some exists_cos_eq_zero

local notation `π` := pi

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).2.2

lemma one_le_pi_div_two : (1 : ℝ) ≤ π / 2 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1

lemma pi_div_two_le_two : π / 2 ≤ 2 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).2.1

lemma two_le_pi : (2 : ℝ) ≤ π :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (by rw div_self (@two_ne_zero' ℝ _ _ _); exact one_le_pi_div_two)

lemma pi_le_four : π ≤ 4 :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (calc π / 2 ≤ 2 : pi_div_two_le_two
    ... = 4 / 2 : by norm_num)

lemma pi_pos : 0 < π :=
lt_of_lt_of_le (by norm_num) two_le_pi

lemma pi_div_two_pos : 0 < π / 2 :=
half_pos pi_pos

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← mul_div_cancel_left pi (@two_ne_zero ℝ _), two_mul, add_div,
    sin_add, cos_pi_div_two]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← mul_div_cancel_left pi (@two_ne_zero ℝ _), mul_div_assoc,
    cos_two_mul, cos_pi_div_two];
  simp [bit0, pow_add]

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
by simp [sin_add]

lemma sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
by simp [sin_add_pi, sin_add, sin_two_pi, cos_two_pi]

lemma cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
by simp [cos_add, cos_two_pi, sin_two_pi]

lemma sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
by simp [sin_add]

lemma cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
by simp [cos_add]

lemma cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
by simp [cos_add]

lemma sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
else
  have (2 : ℝ) + 2 = 4, from rfl,
  have π - x ≤ 2, from sub_le_iff_le_add.2
    (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _)),
  sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this

lemma sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
(lt_or_eq_of_le h0x).elim
  (λ h0x, (lt_or_eq_of_le hxp).elim
    (le_of_lt ∘ sin_pos_of_pos_of_lt_pi h0x)
    (λ hpx, by simp [hpx]))
  (λ h0x, by simp [h0x.symm])

lemma sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
neg_pos.1 $ sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
have sin (π / 2) = 1 ∨ sin (π / 2) = -1 :=
by simpa [pow_two, mul_self_eq_one_iff] using sin_pow_two_add_cos_pow_two (π / 2),
this.resolve_right
  (λ h, (show ¬(0 : ℝ) < -1, by norm_num) $
    h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos))

lemma sin_add_pi_div_two (x : ℝ) : sin (x + π / 2) = cos x :=
by simp [sin_add]

lemma sin_sub_pi_div_two (x : ℝ) : sin (x - π / 2) = -cos x :=
by simp [sin_add]

lemma sin_pi_div_two_sub (x : ℝ) : sin (π / 2 - x) = cos x :=
by simp [sin_add]

lemma cos_add_pi_div_two (x : ℝ) : cos (x + π / 2) = -sin x :=
by simp [cos_add]

lemma cos_sub_pi_div_two (x : ℝ) : cos (x - π / 2) = sin x :=
by simp [cos_add]

lemma cos_pi_div_two_sub (x : ℝ) : cos (π / 2 - x) = sin x :=
by rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

lemma cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two
  {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : 0 < cos x :=
sin_add_pi_div_two x ▸ sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

lemma cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
  {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : 0 ≤ cos x :=
(lt_or_eq_of_le hx₁).elim
  (λ hx₁, (lt_or_eq_of_le hx₂).elim
    (le_of_lt ∘ cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two hx₁)
    (λ hx₂, by simp [hx₂]))
  (λ hx₁, by simp [hx₁.symm])

lemma cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) : cos x < 0 :=
neg_pos.1 $ cos_pi_sub x ▸
  cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) (by linarith)

lemma cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) : cos x ≤ 0 :=
neg_nonneg.1 $ cos_pi_sub x ▸
  cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two (by linarith) (by linarith)

lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
by induction n; simp [add_mul, sin_add, *]

lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
by cases n; simp [add_mul, sin_add, *, sin_nat_mul_pi]

lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
by induction n; simp [*, mul_add, cos_add, add_mul, cos_two_pi, sin_two_pi]

lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
by cases n; simp only [cos_nat_mul_two_pi, int.of_nat_eq_coe,
  int.neg_succ_of_nat_coe, int.cast_coe_nat, int.cast_neg,
  (neg_mul_eq_neg_mul _ _).symm, cos_neg]

lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simp [cos_add, sin_add, cos_int_mul_two_pi]

lemma sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) :
  sin x = 0 ↔ x = 0 :=
⟨λ h, le_antisymm
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 < sin x : sin_pos_of_pos_of_lt_pi h0 hx₂
        ... = 0 : h))
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 = sin x : h.symm
        ... < 0 : sin_neg_of_neg_of_neg_pi_lt h0 hx₁)),
  λ h, by simp [h]⟩

lemma sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
⟨λ h, ⟨⌊x / π⌋, le_antisymm (sub_nonneg.1 (sub_floor_div_mul_nonneg _ pi_pos))
  (sub_nonpos.1 $ le_of_not_gt $ λ h₃, ne_of_lt (sin_pos_of_pos_of_lt_pi h₃ (sub_floor_div_mul_lt _ pi_pos))
    (by simp [sin_add, h, sin_int_mul_pi]))⟩,
  λ ⟨n, hn⟩, hn ▸ sin_int_mul_pi _⟩

lemma sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 :=
by rw [← mul_self_eq_one_iff (cos x), ← sin_pow_two_add_cos_pow_two x,
    pow_two, pow_two, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

lemma cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) : cos x = 1 ↔ x = 0 :=
⟨λ h, (sin_eq_zero_iff_of_lt_of_lt hx₁ hx₂).1 (sin_eq_zero_iff_cos_eq.2 (or.inl h)),
  λ h, by simp [h]⟩

lemma cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
⟨λ h, let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (or.inl h)) in
    ⟨n / 2, (int.mod_two_eq_zero_or_one n).elim
      (λ hn0, by rwa [← mul_assoc, ← @int.cast_two ℝ, ← int.cast_mul, int.div_mul_cancel
        ((int.dvd_iff_mod_eq_zero _ _).2 hn0)])
      (λ hn1, by rw [← int.mod_add_div n 2, hn1, int.cast_add, int.cast_one, add_mul,
          one_mul, add_comm, mul_comm (2 : ℤ), int.cast_mul, mul_assoc, int.cast_two] at hn;
        rw [← hn, cos_int_mul_two_pi_add_pi] at h;
        exact absurd h (by norm_num))⟩,
  λ ⟨n, hn⟩, hn ▸ cos_int_mul_two_pi _⟩

lemma cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π / 2)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π / 2) (hxy : x < y) : cos y < cos x :=
calc cos y = cos x * cos (y - x) - sin x * sin (y - x) :
  by rw [← cos_add, add_sub_cancel'_right]
... < (cos x * 1) - sin x * sin (y - x) :
  sub_lt_sub_right ((mul_lt_mul_left
    (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (lt_of_lt_of_le (neg_neg_of_pos pi_div_two_pos) hx₁)
      (lt_of_lt_of_le hxy hy₂))).2
        (lt_of_le_of_ne (cos_le_one _) (mt (cos_eq_one_iff_of_lt_of_lt
          (show -π < y - x, by linarith) (show y - x < π, by linarith)).1
            (sub_ne_zero.2 (ne_of_lt hxy).symm)))) _
... ≤ _ : by rw mul_one;
  exact sub_le_self _ (mul_nonneg (sin_nonneg_of_nonneg_of_le_pi hx₁ (by linarith))
    (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))

lemma cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π) (hxy : x < y) : cos y < cos x :=
(le_total x (π / 2)).elim
  (λ hx, (le_total y (π / 2)).elim
    (λ hy, cos_lt_cos_of_nonneg_of_le_pi_div_two hx₁ hx hy₁ hy hxy)
    (λ hy, (lt_or_eq_of_le hx).elim
      (λ hx, calc cos y ≤ 0 : cos_nonpos_of_pi_div_two_le_of_le hy (by linarith using [pi_pos])
        ... < cos x : cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) hx)
      (λ hx, calc cos y < 0 : cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith using [pi_pos])
        ... = cos x : by simp [hx, cos_pi_div_two])))
  (λ hx, (le_total y (π / 2)).elim
    (λ hy, by linarith)
    (λ hy, neg_lt_neg_iff.1 $ cos_pi_sub x ▸ cos_pi_sub y ▸
      by apply cos_lt_cos_of_nonneg_of_le_pi_div_two; linarith))

lemma cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π) (hxy : x ≤ y) : cos y ≤ cos x :=
(lt_or_eq_of_le hxy).elim (le_of_lt ∘ cos_lt_cos_of_nonneg_of_le_pi hx₁ hx₂ hy₁ hy₂)
  (λ h, h ▸ le_refl _)

lemma sin_lt_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : x < y) : sin x < sin y :=
by rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two, ← cos_neg (x - _), ← cos_neg (y - _)];
  apply cos_lt_cos_of_nonneg_of_le_pi; linarith

lemma sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : x ≤ y) : sin x ≤ sin y :=
(lt_or_eq_of_le hxy).elim (le_of_lt ∘ sin_lt_sin_of_le_of_le_pi_div_two hx₁ hx₂ hy₁ hy₂)
  (λ h, h ▸ le_refl _)

lemma sin_inj_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : sin x = sin y) : x = y :=
(lt_trichotomy x y).elim
  (λ h, absurd (sin_lt_sin_of_le_of_le_pi_div_two hx₁ hx₂ hy₁ hy₂ h) (by rw hxy; exact lt_irrefl _))
  (λ h, h.elim id
    (λ h, absurd (sin_lt_sin_of_le_of_le_pi_div_two hy₁ hy₂ hx₁ hx₂ h) (by rw hxy; exact lt_irrefl _)))

lemma exists_sin_eq {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : ∃ y, -(π / 2) ≤ y ∧ y ≤ π / 2 ∧ sin y = x :=
@real.intermediate_value sin (-(π / 2)) (π / 2) x
  (λ _ _ _, continuous_iff_tendsto.1 continuous_sin _)
  (by rwa [sin_neg, sin_pi_div_two]) (by rwa sin_pi_div_two)
  (le_trans (neg_nonpos.2 (le_of_lt pi_div_two_pos)) (le_of_lt pi_div_two_pos))

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x` and `arcsin x ≤ π / 2`.
  If the argument is not between `-1` and `1` it defaults to `0` -/
noncomputable def arcsin (x : ℝ) : ℝ :=
if hx : -1 ≤ x ∧ x ≤ 1 then classical.some (exists_sin_eq hx.1 hx.2) else 0

lemma arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ π / 2 :=
if hx : -1 ≤ x ∧ x ≤ 1
then by rw [arcsin, dif_pos hx]; exact (classical.some_spec (exists_sin_eq hx.1 hx.2)).2.1
else by rw [arcsin, dif_neg hx]; exact le_of_lt pi_div_two_pos

lemma neg_pi_div_two_le_arcsin (x : ℝ) : -(π / 2) ≤ arcsin x :=
if hx : -1 ≤ x ∧ x ≤ 1
then by rw [arcsin, dif_pos hx]; exact (classical.some_spec (exists_sin_eq hx.1 hx.2)).1
else by rw [arcsin, dif_neg hx]; exact neg_nonpos.2 (le_of_lt pi_div_two_pos)

lemma sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
by rw [arcsin, dif_pos (and.intro hx₁ hx₂)];
  exact (classical.some_spec (exists_sin_eq hx₁ hx₂)).2.2

lemma arcsin_sin {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : arcsin (sin x) = x :=
sin_inj_of_le_of_le_pi_div_two (neg_pi_div_two_le_arcsin _) (arcsin_le_pi_div_two _) hx₁ hx₂
  (by rw sin_arcsin (neg_one_le_sin _) (sin_le_one _))

@[simp] lemma arcsin_zero : arcsin 0 = 0 :=
sin_inj_of_le_of_le_pi_div_two
  (neg_pi_div_two_le_arcsin _)
  (arcsin_le_pi_div_two _)
  (neg_nonpos.2 (le_of_lt pi_div_two_pos))
  (le_of_lt pi_div_two_pos)
  (by rw [sin_arcsin, sin_zero]; norm_num)

@[simp] lemma arcsin_neg (x : ℝ) : arcsin (-x) = - arcsin x :=
if h : -1 ≤ x ∧ x ≤ 1 then
  have -1 ≤ -x ∧ -x ≤ 1, by rwa [neg_le_neg_iff, neg_le, and.comm],
  sin_inj_of_le_of_le_pi_div_two
    (neg_pi_div_two_le_arcsin _)
    (arcsin_le_pi_div_two _)
    (neg_le_neg (arcsin_le_pi_div_two _))
    (neg_le.1 (neg_pi_div_two_le_arcsin _))
    (by rw [sin_arcsin this.1 this.2, sin_neg, sin_arcsin h.1 h.2])
else
  have ¬(-1 ≤ -x ∧ -x ≤ 1) := by rwa [neg_le_neg_iff, neg_le, and.comm],
  by rw [arcsin, arcsin, dif_neg h, dif_neg this, neg_zero]

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  If the argument is not between `-1` and `1` it defaults to `π / 2` -/
noncomputable def arccos (x : ℝ) : ℝ :=
π / 2 - arcsin x

lemma arccos_eq_arcsin_add_pi_div_two (x : ℝ) : arccos x = π / 2 - arcsin x := rfl

lemma arcsin_eq_arccos_add_pi_div_two (x : ℝ) : arcsin x = π / 2 - arccos x := by simp [arccos]

lemma arccos_le_pi (x : ℝ) : arccos x ≤ π :=
by unfold arccos; linarith using [neg_pi_div_two_le_arcsin x]

lemma arccos_nonneg (x : ℝ) : 0 ≤ arccos x :=
by unfold arccos; linarith using [arcsin_le_pi_div_two x]

lemma cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x :=
by rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]

lemma arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x :=
by rw [arccos, ← sin_pi_div_two_sub, arcsin_sin]; simp; linarith

lemma cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
    (neg_pi_div_two_le_arcsin _) (arcsin_le_pi_div_two _)

lemma cos_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arcsin x) = sqrt (1 - x ^ 2) :=
have sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_pow_two_add_cos_pow_two (arcsin x),
begin
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (pow_two_nonneg _) (sub_nonneg.2 (sin_pow_two_le_one (arcsin x))),
    pow_two, sqrt_mul_self (cos_arcsin_nonneg _)] at this,
  rw [this, sin_arcsin hx₁ hx₂],
end

lemma sin_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arccos x) = sqrt (1 - x ^ 2) :=
by rw [arccos_eq_arcsin_add_pi_div_two, sin_pi_div_two_sub, cos_arcsin hx₁ hx₂]

lemma abs_div_sqrt_one_add_lt (x : ℝ) : abs (x / sqrt (1 + x ^ 2)) < 1 :=
have h₁ : 0 < 1 + x ^ 2, from add_pos_of_pos_of_nonneg zero_lt_one (pow_two_nonneg _),
have h₂ : 0 < sqrt (1 + x ^ 2), from sqrt_pos.2 h₁,
by rw [abs_div, div_lt_iff (abs_pos_of_pos h₂), one_mul,
    mul_self_lt_mul_self_iff (abs_nonneg x) (abs_nonneg _),
    ← abs_mul, ← abs_mul, mul_self_sqrt (add_nonneg zero_le_one (pow_two_nonneg _)),
    abs_of_nonneg (mul_self_nonneg x), abs_of_nonneg (le_of_lt h₁), pow_two, add_comm];
  exact lt_add_one _

lemma div_sqrt_one_add_lt_one (x : ℝ) : x / sqrt (1 + x ^ 2) < 1 :=
(abs_lt.1 (abs_div_sqrt_one_add_lt _)).2

lemma neg_one_lt_div_sqrt_one_add (x : ℝ) : -1 < x / sqrt (1 + x ^ 2) :=
(abs_lt.1 (abs_div_sqrt_one_add_lt _)).1

lemma tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x :=
by rw tan_eq_sin_div_cos; exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith))
  (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) hxp)

lemma tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
(lt_or_eq_of_le h0x).elim
  (λ hx0, (lt_or_eq_of_le hxp).elim
    (le_of_lt ∘ tan_pos_of_pos_of_lt_pi_div_two hx0)
    (λ h, by simp [h, tan_eq_sin_div_cos]))
  (λ h, by simp [h.symm])

lemma tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith using [pi_pos]))

lemma tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) : tan x ≤ 0 :=
neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith using [pi_pos]))

lemma tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x < π / 2) (hy₁ : 0 ≤ y)
  (hy₂ : y < π / 2) (hxy : x < y) : tan x < tan y :=
begin
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos],
  exact div_lt_div
    (sin_lt_sin_of_le_of_le_pi_div_two (by linarith) (le_of_lt hx₂)
      (by linarith) (le_of_lt hy₂) hxy)
    (cos_le_cos_of_nonneg_of_le_pi hx₁ (by linarith) hy₁ (by linarith) (le_of_lt hxy))
    (sin_nonneg_of_nonneg_of_le_pi hy₁ (by linarith))
    (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) hy₂)
end

lemma tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : x < y) : tan x < tan y :=
(le_total x 0).elim
  (λ hx0, (le_total y 0).elim
    (λ hy0, neg_lt_neg_iff.1 $ by rw [← tan_neg, ← tan_neg]; exact
      tan_lt_tan_of_nonneg_of_lt_pi_div_two (neg_nonneg.2 hy0) (neg_lt.2 hy₁)
        (neg_nonneg.2 hx0) (neg_lt.2 hx₁) (neg_lt_neg hxy))
    (λ hy0, (lt_or_eq_of_le hy0).elim
      (λ hy0, calc tan x ≤ 0 : tan_nonpos_of_nonpos_of_neg_pi_div_two_le hx0 (le_of_lt hx₁)
        ... < tan y : tan_pos_of_pos_of_lt_pi_div_two hy0 hy₂)
      (λ hy0, by rw [← hy0, tan_zero]; exact
        tan_neg_of_neg_of_pi_div_two_lt (hy0.symm ▸ hxy) hx₁)))
  (λ hx0, (le_total y 0).elim
    (λ hy0, by linarith)
    (λ hy0, tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0 hx₂ hy0 hy₂ hxy))

lemma tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
(lt_trichotomy x y).elim
  (λ h, absurd (tan_lt_tan_of_lt_of_lt_pi_div_two hx₁ hx₂ hy₁ hy₂ h) (by rw hxy; exact lt_irrefl _))
  (λ h, h.elim id
    (λ h, absurd (tan_lt_tan_of_lt_of_lt_pi_div_two hy₁ hy₂ hx₁ hx₂ h) (by rw hxy; exact lt_irrefl _)))

noncomputable def arctan (x : ℝ) : ℝ :=
arcsin (x / sqrt (1 + x ^ 2))

lemma sin_arctan (x : ℝ) : sin (arctan x) = x / sqrt (1 + x ^ 2) :=
sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _)) (le_of_lt (div_sqrt_one_add_lt_one _))

lemma cos_arctan (x : ℝ) : cos (arctan x) = 1 / sqrt (1 + x ^ 2) :=
have h₁ : (0 : ℝ) < 1 + x ^ 2,
  from add_pos_of_pos_of_nonneg zero_lt_one (pow_two_nonneg _),
have h₂ : (x / sqrt (1 + x ^ 2)) ^ 2 < 1,
  by rw [pow_two, ← abs_mul_self, _root_.abs_mul];
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _)
      (abs_div_sqrt_one_add_lt _) (le_of_lt (abs_div_sqrt_one_add_lt _)),
by rw [arctan, cos_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _)) (le_of_lt (div_sqrt_one_add_lt_one _)),
    one_div_eq_inv, ← sqrt_inv, sqrt_inj (sub_nonneg.2 (le_of_lt h₂)) (inv_nonneg.2 (le_of_lt h₁)),
    div_pow _ (mt sqrt_eq_zero'.1 (not_le.2 h₁)), pow_two (sqrt _), mul_self_sqrt (le_of_lt h₁),
    ← domain.mul_left_inj (ne.symm (ne_of_lt h₁)), mul_sub,
    mul_div_cancel' _ (ne.symm (ne_of_lt h₁)), mul_inv_cancel (ne.symm (ne_of_lt h₁))];
  simp

lemma tan_arctan (x : ℝ) : tan (arctan x) = x :=
by rw [tan_eq_sin_div_cos, sin_arctan, cos_arctan, div_div_div_div_eq, mul_one,
    mul_div_assoc,
    div_self (mt sqrt_eq_zero'.1 (not_le_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (pow_two_nonneg x)))),
    mul_one]

lemma arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
lt_of_le_of_ne (arcsin_le_pi_div_two _)
  (λ h, ne_of_lt (div_sqrt_one_add_lt_one x) $
    by rw [← sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _))
        (le_of_lt (div_sqrt_one_add_lt_one _)), ← arctan, h, sin_pi_div_two])

lemma neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
lt_of_le_of_ne (neg_pi_div_two_le_arcsin _)
  (λ h, ne_of_lt (neg_one_lt_div_sqrt_one_add x) $
    by rw [← sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _))
        (le_of_lt (div_sqrt_one_add_lt_one _)), ← arctan, ← h, sin_neg, sin_pi_div_two])

lemma tan_surjective : function.surjective tan :=
function.surjective_of_has_right_inverse ⟨_, tan_arctan⟩

lemma arctan_tan {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
tan_inj_of_lt_of_lt_pi_div_two (neg_pi_div_two_lt_arctan _)
  (arctan_lt_pi_div_two _) hx₁ hx₂ (by rw tan_arctan)

end real

namespace complex

local notation `π` := real.pi

/-- `arg` returns values in the range (-π, π]. `arg 0 = 0` -/
noncomputable def arg (x : ℂ) : ℝ :=
if 0 ≤ x.re
then real.arcsin (x.im / x.abs)
else if 0 ≤ x.im
then real.arcsin ((-x).im / x.abs) + π
else real.arcsin ((-x).im / x.abs) - π

lemma arg_eq_arg_neg_add_pi {x : ℂ} (hxr : x.re < 0) (hxi : 0 ≤ x.im) : arg x = arg (-x) + π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_pos this, if_pos hxi, abs_neg]

lemma arg_eq_arg_neg_sub_pi {x : ℂ} (hxr : x.re < 0) (hxi : x.im < 0) : arg x = arg (-x) - π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_neg (not_le.2 hxi), if_pos this, abs_neg]

@[simp] lemma arg_zero : arg 0 = 0 :=
by simp [arg, le_refl]

lemma sin_arg (x : ℂ) : real.sin (arg x) = x.im / x.abs :=
by unfold arg; split_ifs;
  simp [arg, real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, real.sin_add, neg_div, real.arcsin_neg,
    real.sin_neg]

private lemma cos_arg_of_re_nonneg {x : ℂ} (hx : x ≠ 0) (hxr : 0 ≤ x.re) : real.cos (arg x) = x.re / x.abs :=
have 0 ≤ 1 - (x.im / abs x) ^ 2,
  from sub_nonneg.2 $ by rw [pow_two, ← _root_.abs_mul_self, _root_.abs_mul, ← pow_two];
  exact pow_le_one _ (_root_.abs_nonneg _) (abs_im_div_abs_le_one _),
by rw [eq_div_iff_mul_eq _ _ (mt abs_eq_zero.1 hx), ← real.mul_self_sqrt (abs_nonneg x),
    arg, if_pos hxr, real.cos_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, ← real.sqrt_mul (abs_nonneg _), ← real.sqrt_mul this,
    sub_mul, div_pow _ (mt abs_eq_zero.1 hx), ← pow_two, div_mul_cancel _ (pow_ne_zero 2 (mt abs_eq_zero.1 hx)),
    one_mul, pow_two, mul_self_abs, norm_sq, pow_two, add_sub_cancel, real.sqrt_mul_self hxr]

lemma cos_arg {x : ℂ} (hx : x ≠ 0) : real.cos (arg x) = x.re / x.abs :=
if hxr : 0 ≤ x.re then cos_arg_of_re_nonneg hx hxr
else
  have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
  if hxi : 0 ≤ x.im
  then have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
    by rw [arg_eq_arg_neg_add_pi (not_le.1 hxr) hxi, real.cos_add_pi,
        cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this];
      simp [neg_div]
  else by rw [arg_eq_arg_neg_sub_pi (not_le.1 hxr) (not_le.1 hxi)];
    simp [real.cos_add, neg_div, cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this]

lemma tan_arg {x : ℂ} : real.tan (arg x) = x.im / x.re :=
if hx : x = 0 then by simp [hx]
else by rw [real.tan_eq_sin_div_cos, sin_arg, cos_arg hx,
    div_div_div_cancel_right _ _ (mt abs_eq_zero.1 hx)]

noncomputable def ln (x : ℂ) : ℂ := real.ln x.abs + arg x * I

lemma exp_ln {x : ℂ} (hx : x ≠ 0) : exp (ln x) = x :=
have h₁ : x.re / x.abs ≤ 1,
  from (abs_le.1 (abs_re_div_abs_le_one x)).2,
have h₂ : -1 ≤ x.re / x.abs,
  from (abs_le.1 (abs_re_div_abs_le_one x)).1,
by rw [ln, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx,
    ← of_real_exp, real.exp_ln (abs_pos.2 hx), mul_add, of_real_div, of_real_div,
    mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ← mul_assoc,
    mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]


end complex