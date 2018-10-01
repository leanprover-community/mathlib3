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

/- TODO move -/
lemma sub_floor_div_mul_nonneg (x : ℝ) {y : ℝ} (hy : 0 < y) :
  0 ≤ x - ⌊x / y⌋ * y :=
begin
  conv in x {rw ← div_mul_cancel x (ne_of_lt hy).symm},
  rw ← sub_mul,
  exact mul_nonneg (sub_nonneg.2 (floor_le _)) (le_of_lt hy)
end
/- TODO move -/
lemma sub_floor_div_mul_lt (x : ℝ) {y : ℝ} (hy : 0 < y) :
  x - ⌊x / y⌋ * y < y :=
sub_lt_iff_lt_add.2 begin
  conv in y {rw ← one_mul y},
  conv in x {rw ← div_mul_cancel x (ne_of_lt hy).symm},
  rw ← add_mul,
  exact (mul_lt_mul_right hy).2 (by rw add_comm; exact lt_floor_add_one _),
end

/- TODO move -/
lemma int.mod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
have h : n % 2 < 2 := abs_of_nonneg (show (2 : ℤ) ≥ 0, from dec_trivial) ▸ int.mod_lt _ dec_trivial,
have h₁ : n % 2 ≥ 0 := int.mod_nonneg _ dec_trivial,
match (n % 2), h, h₁ with
| (0 : ℕ) := λ _ _, or.inl rfl
| (1 : ℕ) := λ _ _, or.inr rfl
| (k + 2 : ℕ) := λ h _, absurd h dec_trivial
| -[1+ a] := λ _ h₁, absurd h₁ dec_trivial
end
/- TODO move -/
lemma int.cast_two {α : Type*} [ring α] : ((2 : ℤ) : α) = 2 := by simp

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

noncomputable def arctan (x : ℝ) : ℝ :=
arcsin (x / sqrt (1 + x ^ 2))

lemma arctan_le_pi_div_two (x : ℝ) : arctan x ≤ π / 2 :=
arcsin_le_pi_div_two _

lemma neg_pi_div_two_le_arctan (x : ℝ) : -(π / 2) ≤ arctan x :=
neg_pi_div_two_le_arcsin _

lemma tan_arctan (x : ℝ) : tan (arctan x) = x :=
have h₁ : ∀ y, 0 ≤ 1 - sin y ^ 2 :=
  λ y, sub_nonneg.2 (sin_pow_two_le_one _),
have h₅ : (x / sqrt (1 + x ^ 2)) ^ 2 < 1,
  by rw [pow_two, ← abs_mul_self, _root_.abs_mul];
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _)
      (abs_div_sqrt_one_add_lt _) (le_of_lt (abs_div_sqrt_one_add_lt _)),
have h₆ : sqrt (1 - (x / sqrt (1 + x ^ 2)) ^ 2) ≠ 0 :=
  mt sqrt_eq_zero'.1 (not_le_of_gt (sub_pos.2 h₅)),
have h₇ : (0 : ℝ) < 1 + x ^ 2,
  from add_pos_of_pos_of_nonneg zero_lt_one (pow_two_nonneg _),
have h₈ : sqrt (1 + x ^ 2) ≠ 0 :=
  mt sqrt_eq_zero'.1 (not_le_of_gt h₇),
have h₉ : 0 ≤ 1 - (x / sqrt (1 + x ^ 2)) ^ 2 :=
  sub_nonneg.2 $ le_of_lt h₅,
have h₁₀ : 1 + x ^ 2 - (x ^ 2 / (1 + x ^ 2) + x ^ 2 / (1 + x ^ 2) * x ^ 2) = 1 :=
  (domain.mul_left_inj (ne.symm (ne_of_lt h₇))).1 $
    by rw [mul_sub, mul_add, mul_add, ← mul_assoc, mul_div_cancel' _ (ne.symm (ne_of_lt h₇))]; ring,
begin
  have := sin_pow_two_add_cos_pow_two (arcsin (x / sqrt (1 + x ^ 2))),
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (pow_two_nonneg _) (h₁ _), sqrt_sqr (cos_arcsin_nonneg _),
    sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _)) (le_of_lt (div_sqrt_one_add_lt_one _))] at this,
  rw [tan_eq_sin_div_cos, arctan, sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _))
    (le_of_lt (div_sqrt_one_add_lt_one _)), this, div_eq_iff_mul_eq h₆,
    eq_div_iff_mul_eq _ _ h₈, mul_assoc, ← sqrt_mul h₉, sub_mul, mul_add, mul_add,
    div_pow _ h₈, pow_two (sqrt (1 + _)), mul_self_sqrt (le_of_lt h₇), one_mul, one_mul, mul_one,
    h₁₀, sqrt_one, mul_one]
end

lemma tan_surjective : function.surjective tan :=
function.surjective_of_has_right_inverse ⟨_, tan_arctan⟩

end real