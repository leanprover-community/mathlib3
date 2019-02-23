/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo
-/
import topology.instances.complex tactic.linarith data.complex.exponential group_theory.quotient_group

open finset filter metric

namespace complex

lemma tendsto_exp_zero_one : tendsto exp (nhds 0) (nhds 1) :=
tendsto_nhds_nhds.2 $ λ ε ε0,
  ⟨min (ε / 2) 1, lt_min (div_pos ε0 (by norm_num)) (by norm_num),
    λ x h, have h : abs x < min (ε / 2) 1, by simpa [dist_eq] using h,
      calc abs (exp x - 1) ≤ 2 * abs x : abs_exp_sub_one_le
          (le_trans (le_of_lt h) (min_le_right _ _))
        ... = abs x + abs x : two_mul (abs x)
        ... < ε / 2 + ε / 2 : add_lt_add
          (lt_of_lt_of_le h (min_le_left _ _)) (lt_of_lt_of_le h (min_le_left _ _))
        ... = ε : by rw add_halves⟩

lemma continuous_exp : continuous exp :=
continuous_iff_continuous_at.2 (λ x,
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
continuous_mul
  (continuous_mul
    (continuous_sub
      ((continuous_mul continuous_neg' continuous_const).comp continuous_exp)
      ((continuous_mul continuous_id continuous_const).comp continuous_exp))
    continuous_const)
  continuous_const

lemma continuous_cos : continuous cos :=
continuous_mul
  (continuous_add
    ((continuous_mul continuous_id continuous_const).comp continuous_exp)
    ((continuous_mul continuous_neg' continuous_const).comp continuous_exp))
  continuous_const

lemma continuous_tan : continuous (λ x : {x // cos x ≠ 0}, tan x) :=
continuous_mul
  (continuous_subtype_val.comp continuous_sin)
  (continuous_inv subtype.property
    (continuous_subtype_val.comp continuous_cos))

lemma continuous_sinh : continuous sinh :=
continuous_mul
  (continuous_sub
    continuous_exp
    (continuous_neg'.comp continuous_exp))
  continuous_const

lemma continuous_cosh : continuous cosh :=
continuous_mul
  (continuous_add
    continuous_exp
    (continuous_neg'.comp continuous_exp))
  continuous_const

end complex

namespace real

lemma continuous_exp : continuous exp :=
(complex.continuous_of_real.comp complex.continuous_exp).comp
  complex.continuous_re

lemma continuous_sin : continuous sin :=
(complex.continuous_of_real.comp complex.continuous_sin).comp
  complex.continuous_re

lemma continuous_cos : continuous cos :=
(complex.continuous_of_real.comp complex.continuous_cos).comp
  complex.continuous_re

lemma continuous_tan : continuous (λ x : {x // cos x ≠ 0}, tan x) :=
by simp only [tan_eq_sin_div_cos]; exact
continuous_mul
  (continuous_subtype_val.comp continuous_sin)
  (continuous_inv subtype.property
    (continuous_subtype_val.comp continuous_cos))

lemma continuous_sinh : continuous sinh :=
(complex.continuous_of_real.comp complex.continuous_sinh).comp
  complex.continuous_re

lemma continuous_cosh : continuous cosh :=
(complex.continuous_of_real.comp complex.continuous_cosh).comp
  complex.continuous_re

private lemma exists_exp_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : ∃ y, exp y = x :=
let ⟨y, hy⟩ := @intermediate_value real.exp 0 (x - 1) x
  (λ _ _ _, continuous_iff_continuous_at.1 continuous_exp _) (by simpa)
  (by simpa using add_one_le_exp_of_nonneg (sub_nonneg.2 hx)) (sub_nonneg.2 hx) in
⟨y, hy.2.2⟩

lemma exists_exp_eq_of_pos {x : ℝ} (hx : 0 < x) : ∃ y, exp y = x :=
match le_total x 1 with
| (or.inl hx1) := let ⟨y, hy⟩ := exists_exp_eq_of_one_le (one_le_inv hx hx1) in
  ⟨-y, by rw [exp_neg, hy, inv_inv']⟩
| (or.inr hx1) := exists_exp_eq_of_one_le hx1
end

noncomputable def log (x : ℝ) : ℝ :=
if hx : 0 < x then classical.some (exists_exp_eq_of_pos hx) else 0

lemma exp_log {x : ℝ} (hx : 0 < x) : exp (log x) = x :=
by rw [log, dif_pos hx]; exact classical.some_spec (exists_exp_eq_of_pos hx)

@[simp] lemma log_exp (x : ℝ) : log (exp x) = x :=
exp_injective $ exp_log (exp_pos x)

@[simp] lemma log_zero : log 0 = 0 :=
by simp [log, lt_irrefl]

@[simp] lemma log_one : log 1 = 0 :=
exp_injective $ by rw [exp_log zero_lt_one, exp_zero]

lemma log_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : log (x * y) = log x + log y :=
exp_injective $ by rw [exp_log (mul_pos hx hy), exp_add, exp_log hx, exp_log hy]

lemma exists_cos_eq_zero : ∃ x, 1 ≤ x ∧ x ≤ 2 ∧ cos x = 0 :=
real.intermediate_value'
  (λ x _ _, continuous_iff_continuous_at.1 continuous_cos _)
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

lemma two_pi_pos : 0 < 2 * π :=
by linarith using [pi_pos]

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
match lt_or_eq_of_le h0x with
| or.inl h0x := (lt_or_eq_of_le hxp).elim
  (le_of_lt ∘ sin_pos_of_pos_of_lt_pi h0x)
  (λ hpx, by simp [hpx])
| or.inr h0x := by simp [h0x.symm]
end

lemma sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
neg_pos.1 $ sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

lemma sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
neg_nonneg.1 $ sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

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
match lt_or_eq_of_le hx₁, lt_or_eq_of_le hx₂ with
| or.inl hx₁, or.inl hx₂ := le_of_lt (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two hx₁ hx₂)
| or.inl hx₁, or.inr hx₂ := by simp [hx₂]
| or.inr hx₁, _          := by simp [hx₁.symm]
end

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

theorem sin_sub_sin (θ ψ : ℝ) : sin θ - sin ψ = 2 * sin((θ - ψ)/2) * cos((θ + ψ)/2) :=
begin
  have s1 := sin_add ((θ + ψ) / 2) ((θ - ψ) / 2),
  have s2 := sin_sub ((θ + ψ) / 2) ((θ - ψ) / 2),
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel, add_self_div_two] at s1,
  rw [div_sub_div_same, ←sub_add, add_sub_cancel', add_self_div_two] at s2,
  rw [s1, s2, ←sub_add, add_sub_cancel', ← two_mul, ← mul_assoc, mul_right_comm]
end

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

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * pi / 2 :=
begin
  rw [←real.sin_pi_div_two_sub, sin_eq_zero_iff],
  split,
  { rintro ⟨n, hn⟩, existsi -n,
    rw [int.cast_neg, add_mul, add_div, mul_assoc, mul_div_cancel_left _ two_ne_zero,
        one_mul, ←neg_mul_eq_neg_mul, hn, neg_sub, sub_add_cancel] },
  { rintro ⟨n, hn⟩, existsi -n,
    rw [hn, add_mul, one_mul, add_div, mul_assoc, mul_div_cancel_left _ two_ne_zero,
        sub_add_eq_sub_sub_swap, sub_self, zero_sub, neg_mul_eq_neg_mul, int.cast_neg] }
end

lemma cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) : cos x = 1 ↔ x = 0 :=
⟨λ h, let ⟨n, hn⟩ := (cos_eq_one_iff x).1 h in
    begin
      clear _let_match,
      subst hn,
      rw [mul_lt_iff_lt_one_left two_pi_pos, ← int.cast_one, int.cast_lt, ← int.le_sub_one_iff, sub_self] at hx₂,
      rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos, neg_lt,
        ← int.cast_one, ← int.cast_neg, int.cast_lt, ← int.add_one_le_iff, neg_add_self] at hx₁,
      exact mul_eq_zero.2 (or.inl (int.cast_eq_zero.2 (le_antisymm hx₂ hx₁))),
    end,
  λ h, by simp [h]⟩

theorem cos_sub_cos (θ ψ : ℝ) : cos θ - cos ψ = -2 * sin((θ + ψ)/2) * sin((θ - ψ)/2) :=
by rw [← sin_pi_div_two_sub, ← sin_pi_div_two_sub, sin_sub_sin, sub_sub_sub_cancel_left,
    add_sub, sub_add_eq_add_sub, add_halves, sub_sub, sub_div π, cos_pi_div_two_sub,
    ← neg_sub, neg_div, sin_neg, ← neg_mul_eq_mul_neg, neg_mul_eq_neg_mul, mul_right_comm]

lemma cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π / 2)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π / 2) (hxy : x < y) : cos y < cos x :=
calc cos y = cos x * cos (y - x) - sin x * sin (y - x) :
  by rw [← cos_add, add_sub_cancel'_right]
... < (cos x * 1) - sin x * sin (y - x) :
  sub_lt_sub_right ((mul_lt_mul_left
    (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (lt_of_lt_of_le (neg_neg_of_pos pi_div_two_pos) hx₁)
      (lt_of_lt_of_le hxy hy₂))).2
        (lt_of_le_of_ne (cos_le_one _) (mt (cos_eq_one_iff_of_lt_of_lt
          (show -(2 * π) < y - x, by linarith) (show y - x < 2 * π, by linarith)).1
            (sub_ne_zero.2 (ne_of_lt hxy).symm)))) _
... ≤ _ : by rw mul_one;
  exact sub_le_self _ (mul_nonneg (sin_nonneg_of_nonneg_of_le_pi hx₁ (by linarith))
    (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))

lemma cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π) (hxy : x < y) : cos y < cos x :=
match (le_total x (π / 2) : x ≤ π / 2 ∨ π / 2 ≤ x), le_total y (π / 2) with
| or.inl hx, or.inl hy := cos_lt_cos_of_nonneg_of_le_pi_div_two hx₁ hx hy₁ hy hxy
| or.inl hx, or.inr hy := (lt_or_eq_of_le hx).elim
  (λ hx, calc cos y ≤ 0 : cos_nonpos_of_pi_div_two_le_of_le hy (by linarith using [pi_pos])
    ... < cos x : cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) hx)
  (λ hx, calc cos y < 0 : cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith using [pi_pos])
    ... = cos x : by rw [hx, cos_pi_div_two])
| or.inr hx, or.inl hy := by linarith
| or.inr hx, or.inr hy := neg_lt_neg_iff.1 (by rw [← cos_pi_sub, ← cos_pi_sub];
  apply cos_lt_cos_of_nonneg_of_le_pi_div_two; linarith)
end

lemma cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π) (hxy : x ≤ y) : cos y ≤ cos x :=
(lt_or_eq_of_le hxy).elim
  (le_of_lt ∘ cos_lt_cos_of_nonneg_of_le_pi hx₁ hx₂ hy₁ hy₂)
  (λ h, h ▸ le_refl _)

lemma sin_lt_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : x < y) : sin x < sin y :=
by rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two, ← cos_neg (x - _), ← cos_neg (y - _)];
  apply cos_lt_cos_of_nonneg_of_le_pi; linarith

lemma sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : x ≤ y) : sin x ≤ sin y :=
(lt_or_eq_of_le hxy).elim
  (le_of_lt ∘ sin_lt_sin_of_le_of_le_pi_div_two hx₁ hx₂ hy₁ hy₂)
  (λ h, h ▸ le_refl _)

lemma sin_inj_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : sin x = sin y) : x = y :=
match lt_trichotomy x y with
| or.inl h          := absurd (sin_lt_sin_of_le_of_le_pi_div_two hx₁ hx₂ hy₁ hy₂ h) (by rw hxy; exact lt_irrefl _)
| or.inr (or.inl h) := h
| or.inr (or.inr h) := absurd (sin_lt_sin_of_le_of_le_pi_div_two hy₁ hy₂ hx₁ hx₂ h) (by rw hxy; exact lt_irrefl _)
end

lemma cos_inj_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) (hy₁ : 0 ≤ y) (hy₂ : y ≤ π)
  (hxy : cos x = cos y) : x = y :=
begin
  rw [← sin_pi_div_two_sub, ← sin_pi_div_two_sub] at hxy,
  refine (sub_left_inj).1 (sin_inj_of_le_of_le_pi_div_two _ _ _ _ hxy);
  linarith
end

lemma exists_sin_eq {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : ∃ y, -(π / 2) ≤ y ∧ y ≤ π / 2 ∧ sin y = x :=
@real.intermediate_value sin (-(π / 2)) (π / 2) x
  (λ _ _ _, continuous_iff_continuous_at.1 continuous_sin _)
  (by rwa [sin_neg, sin_pi_div_two]) (by rwa sin_pi_div_two)
  (le_trans (neg_nonpos.2 (le_of_lt pi_div_two_pos)) (le_of_lt pi_div_two_pos))

namespace angle

/-- The type of angles -/
def angle : Type :=
quotient_add_group.quotient (gmultiples (2 * π))

instance angle.add_comm_group : add_comm_group angle :=
quotient_add_group.add_comm_group _

instance angle.has_coe : has_coe ℝ angle :=
⟨quotient.mk'⟩

instance angle.is_add_group_hom : is_add_group_hom (coe : ℝ → angle) :=
@quotient_add_group.is_add_group_hom _ _ _ (normal_add_subgroup_of_add_comm_group _)

@[simp] lemma coe_zero : ↑(0 : ℝ) = (0 : angle) := rfl
@[simp] lemma coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : angle) := rfl
@[simp] lemma coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : angle) := rfl
@[simp] lemma coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : angle) := rfl
@[simp] lemma coe_gsmul (x : ℝ) (n : ℤ) : ↑(gsmul n x : ℝ) = gsmul n (↑x : angle) := is_add_group_hom.gsmul _ _ _
@[simp] lemma coe_two_pi : ↑(2 * π : ℝ) = (0 : angle) :=
quotient.sound' ⟨-1, by dsimp only; rw [neg_one_gsmul, add_zero]⟩

lemma angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k :=
by simp only [quotient_add_group.eq, gmultiples, set.mem_range, gsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : ℝ} : cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
begin
  split,
  { intro Hcos,
    rw [←sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero, eq_false_intro two_ne_zero,
        false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos,
    rcases Hcos with ⟨n, hn⟩ | ⟨n, hn⟩,
    { right,
      rw [eq_div_iff_mul_eq _ _ two_ne_zero, ← sub_eq_iff_eq_add] at hn,
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc,
          ← gsmul_eq_mul, coe_gsmul, mul_comm, coe_two_pi, gsmul_zero] },
    { left,
      rw [eq_div_iff_mul_eq _ _ two_ne_zero, eq_sub_iff_add_eq] at hn,
      rw [← hn, coe_add, mul_assoc,
          ← gsmul_eq_mul, coe_gsmul, mul_comm, coe_two_pi, gsmul_zero, zero_add] } },
  { rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub], 
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero_iff_eq, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left _ two_ne_zero, 
      mul_comm π _, sin_int_mul_pi, mul_zero],
    rw [←sub_eq_zero_iff_eq, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k, 
      mul_div_cancel_left _ two_ne_zero, mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul] }
end

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : ℝ} : sin θ = sin ψ ↔ (θ : angle) = ψ ∨ (θ : angle) + ψ = π :=
begin
  split,
  { intro Hsin, rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin,
    cases cos_eq_iff_eq_or_eq_neg.mp Hsin with h h,
    { left, rw coe_sub at h, exact sub_left_inj.1 h },
      right, rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub,
      sub_add_eq_add_sub, ← coe_add, add_halves, sub_sub, sub_eq_zero] at h,
    exact h.symm },
  { rw [angle_eq_iff_two_pi_dvd_sub, ←eq_sub_iff_add_eq, ←coe_sub, angle_eq_iff_two_pi_dvd_sub], 
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero_iff_eq, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left _ two_ne_zero,
      mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul],
    have H' : θ + ψ = (2 * k) * π + π := by rwa [←sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, 
      mul_assoc, mul_comm π _, ←mul_assoc] at H,
    rw [← sub_eq_zero_iff_eq, sin_sub_sin, H', add_div, mul_assoc 2 _ π, mul_div_cancel_left _ two_ne_zero, 
      cos_add_pi_div_two, sin_int_mul_pi, neg_zero, mul_zero] }
end

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : angle) = ψ :=
begin
  cases cos_eq_iff_eq_or_eq_neg.mp Hcos with hc hc, { exact hc },
  cases sin_eq_iff_eq_or_add_eq_pi.mp Hsin with hs hs, { exact hs },
  rw [eq_neg_iff_add_eq_zero, hs] at hc,
  cases quotient.exact' hc with n hn, dsimp only at hn,
  rw [← neg_one_mul, add_zero, ← sub_eq_zero_iff_eq, gsmul_eq_mul, ← mul_assoc, ← sub_mul,
      mul_eq_zero, eq_false_intro (ne_of_gt pi_pos), or_false, sub_neg_eq_add,
      ← int.cast_zero, ← int.cast_one, ← int.cast_bit0, ← int.cast_mul, ← int.cast_add, int.cast_inj] at hn,
  have : (n * 2 + 1) % (2:ℤ) = 0 % (2:ℤ) := congr_arg (%(2:ℤ)) hn,
  rw [add_comm, int.add_mul_mod_self] at this,
  exact absurd this one_ne_zero
end

end angle

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

lemma arcsin_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1)
  (hxy : arcsin x = arcsin y) : x = y :=
by rw [← sin_arcsin hx₁ hx₂, ← sin_arcsin hy₁ hy₂, hxy]

@[simp] lemma arcsin_zero : arcsin 0 = 0 :=
sin_inj_of_le_of_le_pi_div_two
  (neg_pi_div_two_le_arcsin _)
  (arcsin_le_pi_div_two _)
  (neg_nonpos.2 (le_of_lt pi_div_two_pos))
  (le_of_lt pi_div_two_pos)
  (by rw [sin_arcsin, sin_zero]; norm_num)

@[simp] lemma arcsin_one : arcsin 1 = π / 2 :=
sin_inj_of_le_of_le_pi_div_two
  (neg_pi_div_two_le_arcsin _)
  (arcsin_le_pi_div_two _)
  (by linarith using [pi_pos])
  (le_refl _)
  (by rw [sin_arcsin, sin_pi_div_two]; norm_num)

@[simp] lemma arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x :=
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

@[simp] lemma arcsin_neg_one : arcsin (-1) = -(π / 2) := by simp

lemma arcsin_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ arcsin x :=
if hx₁ : x ≤ 1 then
not_lt.1 (λ h, not_lt.2 hx begin
  have := sin_lt_sin_of_le_of_le_pi_div_two
    (neg_pi_div_two_le_arcsin _) (arcsin_le_pi_div_two _)
    (neg_nonpos.2 (le_of_lt pi_div_two_pos)) (le_of_lt pi_div_two_pos) h,
  rw [real.sin_arcsin, sin_zero] at this; linarith
end)
else by rw [arcsin, dif_neg]; simp [hx₁]

lemma arcsin_eq_zero_iff {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : arcsin x = 0 ↔ x = 0 :=
⟨λ h, have sin (arcsin x) = 0, by simp [h],
  by rwa [sin_arcsin hx₁ hx₂] at this,
λ h, by simp [h]⟩

lemma arcsin_pos {x : ℝ} (hx₁ : 0 < x) (hx₂ : x ≤ 1) : 0 < arcsin x :=
lt_of_le_of_ne (arcsin_nonneg (le_of_lt hx₁))
  (ne.symm (mt (arcsin_eq_zero_iff (by linarith) hx₂).1 (ne_of_lt hx₁).symm))

lemma arcsin_nonpos {x : ℝ} (hx : x ≤ 0) : arcsin x ≤ 0 :=
neg_nonneg.1 (arcsin_neg x ▸ arcsin_nonneg (neg_nonneg.2 hx))

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  If the argument is not between `-1` and `1` it defaults to `π / 2` -/
noncomputable def arccos (x : ℝ) : ℝ :=
π / 2 - arcsin x

lemma arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = π / 2 - arcsin x := rfl

lemma arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = π / 2 - arccos x := by simp [arccos]

lemma arccos_le_pi (x : ℝ) : arccos x ≤ π :=
by unfold arccos; linarith using [neg_pi_div_two_le_arcsin x]

lemma arccos_nonneg (x : ℝ) : 0 ≤ arccos x :=
by unfold arccos; linarith using [arcsin_le_pi_div_two x]

lemma cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x :=
by rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]

lemma arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x :=
by rw [arccos, ← sin_pi_div_two_sub, arcsin_sin]; simp; linarith

lemma arccos_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1)
  (hxy : arccos x = arccos y) : x = y :=
arcsin_inj hx₁ hx₂ hy₁ hy₂ $ by simp [arccos, *] at *

@[simp] lemma arccos_zero : arccos 0 = π / 2 := by simp [arccos]

@[simp] lemma arccos_one : arccos 1 = 0 := by simp [arccos]

@[simp] lemma arccos_neg_one : arccos (-1) = π := by simp [arccos, add_halves]

lemma arccos_neg (x : ℝ) : arccos (-x) = π - arccos x :=
by rw [← add_halves π, arccos, arcsin_neg, arccos, add_sub_assoc, sub_sub_self]; simp

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
by rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin hx₁ hx₂]

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
match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
| or.inl hx0, or.inl hxp := le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
| or.inl hx0, or.inr hxp := by simp [hxp, tan_eq_sin_div_cos]
| or.inr hx0, _          := by simp [hx0.symm]
end

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
match le_total x 0, le_total y 0 with
| or.inl hx0, or.inl hy0 := neg_lt_neg_iff.1 $ by rw [← tan_neg, ← tan_neg]; exact
  tan_lt_tan_of_nonneg_of_lt_pi_div_two (neg_nonneg.2 hy0) (neg_lt.2 hy₁)
    (neg_nonneg.2 hx0) (neg_lt.2 hx₁) (neg_lt_neg hxy)
| or.inl hx0, or.inr hy0 := (lt_or_eq_of_le hy0).elim
  (λ hy0, calc tan x ≤ 0 : tan_nonpos_of_nonpos_of_neg_pi_div_two_le hx0 (le_of_lt hx₁)
    ... < tan y : tan_pos_of_pos_of_lt_pi_div_two hy0 hy₂)
  (λ hy0, by rw [← hy0, tan_zero]; exact
    tan_neg_of_neg_of_pi_div_two_lt (hy0.symm ▸ hxy) hx₁)
| or.inr hx0, or.inl hy0 := by linarith
| or.inr hx0, or.inr hy0 := tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0 hx₂ hy0 hy₂ hxy
end

lemma tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
match lt_trichotomy x y with
| or.inl h          := absurd (tan_lt_tan_of_lt_of_lt_pi_div_two hx₁ hx₂ hy₁ hy₂ h) (by rw hxy; exact lt_irrefl _)
| or.inr (or.inl h) := h
| or.inr (or.inr h) := absurd (tan_lt_tan_of_lt_of_lt_pi_div_two hy₁ hy₂ hx₁ hx₂ h) (by rw hxy; exact lt_irrefl _)
end

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and `arctan x < π / 2` -/
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

@[simp] lemma arctan_zero : arctan 0 = 0 :=
by simp [arctan]

@[simp] lemma arctan_neg (x : ℝ) : arctan (-x) = - arctan x :=
by simp [arctan, neg_div]

end real

namespace complex

local notation `π` := real.pi

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x,abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
if 0 ≤ x.re
then real.arcsin (x.im / x.abs)
else if 0 ≤ x.im
then real.arcsin ((-x).im / x.abs) + π
else real.arcsin ((-x).im / x.abs) - π

lemma arg_le_pi (x : ℂ) : arg x ≤ π :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact le_trans (real.arcsin_le_pi_div_two _) (le_of_lt (half_lt_self real.pi_pos))
else
  have hx : x ≠ 0, from λ h, by simpa [h, lt_irrefl] using hx₁,
  if hx₂ : 0 ≤ x.im
  then by rw [arg, if_neg hx₁, if_pos hx₂];
    exact le_sub_iff_add_le.1 (by rw sub_self;
      exact real.arcsin_nonpos (by rw [neg_im, neg_div, neg_nonpos]; exact div_nonneg hx₂ (abs_pos.2 hx)))
  else by rw [arg, if_neg hx₁, if_neg hx₂];
      exact sub_le_iff_le_add.2 (le_trans (real.arcsin_le_pi_div_two _)
        (by linarith using [real.pi_pos]))

lemma neg_pi_lt_arg (x : ℂ) : -π < arg x :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact lt_of_lt_of_le (neg_lt_neg (half_lt_self real.pi_pos)) (real.neg_pi_div_two_le_arcsin _)
else
  have hx : x ≠ 0, from λ h, by simpa [h, lt_irrefl] using hx₁,
  if hx₂ : 0 ≤ x.im
  then by rw [arg, if_neg hx₁, if_pos hx₂];
    exact sub_lt_iff_lt_add.1
      (lt_of_lt_of_le (by linarith using [real.pi_pos]) (real.neg_pi_div_two_le_arcsin _))
  else by rw [arg, if_neg hx₁, if_neg hx₂];
    exact lt_sub_iff_add_lt.2 (by rw neg_add_self;
      exact real.arcsin_pos (by rw [neg_im]; exact div_pos (neg_pos.2 (lt_of_not_ge hx₂))
        (abs_pos.2 hx)) (by rw [← abs_neg x]; exact (abs_le.1 (abs_im_div_abs_le_one _)).2))

lemma arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : 0 ≤ x.im) :
  arg x = arg (-x) + π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_pos this, if_pos hxi, abs_neg]

lemma arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : x.im < 0) :
  arg x = arg (-x) - π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_neg (not_le.2 hxi), if_pos this, abs_neg]

@[simp] lemma arg_zero : arg 0 = 0 :=
by simp [arg, le_refl]

@[simp] lemma arg_one : arg 1 = 0 :=
by simp [arg, zero_le_one]

@[simp] lemma arg_neg_one : arg (-1) = π :=
by simp [arg, le_refl, not_le.2 (@zero_lt_one ℝ _)]

@[simp] lemma arg_I : arg I = π / 2 :=
by simp [arg, le_refl]

@[simp] lemma arg_neg_I : arg (-I) = -(π / 2) :=
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
    by rw [arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg (not_le.1 hxr) hxi, real.cos_add_pi,
        cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this];
      simp [neg_div]
  else by rw [arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg (not_le.1 hxr) (not_le.1 hxi)];
    simp [real.cos_add, neg_div, cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this]

lemma tan_arg {x : ℂ} : real.tan (arg x) = x.im / x.re :=
if hx : x = 0 then by simp [hx]
else by rw [real.tan_eq_sin_div_cos, sin_arg, cos_arg hx,
    div_div_div_cancel_right _ _ (mt abs_eq_zero.1 hx)]

lemma arg_cos_add_sin_mul_I {x : ℝ} (hx₁ : -π < x) (hx₂ : x ≤ π) :
  arg (cos x + sin x * I) = x :=
if hx₃ : -(π / 2) ≤ x ∧ x ≤ π / 2
then
  have hx₄ : 0 ≤ (cos x + sin x * I).re,
    by simp; exact real.cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two hx₃.1 hx₃.2,
  by rw [arg, if_pos hx₄];
    simp [abs_cos_add_sin_mul_I, sin_of_real_re, real.arcsin_sin hx₃.1 hx₃.2]
else if hx₄ : x < -(π / 2)
then
  have hx₅ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬ 0 ≤ real.cos x, by simpa,
    not_le.2 $ by rw ← real.cos_neg;
      apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₆ : ¬0 ≤ (cos ↑x + sin ↑x * I).im :=
    suffices real.sin x < 0, by simpa,
    by apply real.sin_neg_of_neg_of_neg_pi_lt; linarith,
  suffices -π + -real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₅, if_neg hx₆];
    simpa [abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.arcsin_neg, ← real.sin_add_pi, real.arcsin_sin]; simp; linarith
else
  have hx₅ : π / 2 < x, by cases not_and_distrib.1 hx₃; linarith,
  have hx₆ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬0 ≤ real.cos x, by simpa,
    not_le.2 $ by apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₇ : 0 ≤ (cos x + sin x * I).im :=
    suffices 0 ≤ real.sin x, by simpa,
    by apply real.sin_nonneg_of_nonneg_of_le_pi; linarith,
  suffices π - real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₆, if_pos hx₇];
      simpa [abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.sin_pi_sub, real.arcsin_sin]; simp; linarith

lemma arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
  arg x = arg y ↔ (abs y / abs x : ℂ) * x = y :=
have hax : abs x ≠ 0, from (mt abs_eq_zero.1 hx),
have hay : abs y ≠ 0, from (mt abs_eq_zero.1 hy),
⟨λ h,
  begin
    have hcos := congr_arg real.cos h,
    rw [cos_arg hx, cos_arg hy, div_eq_div_iff hax hay] at hcos,
    have hsin := congr_arg real.sin h,
    rw [sin_arg, sin_arg, div_eq_div_iff hax hay] at hsin,
    apply complex.ext,
    { rw [mul_re, ← of_real_div, of_real_re, of_real_im, zero_mul, sub_zero, mul_comm,
        ← mul_div_assoc, hcos, mul_div_cancel _ hax] },
    { rw [mul_im, ← of_real_div, of_real_re, of_real_im, zero_mul, add_zero,
        mul_comm, ← mul_div_assoc, hsin, mul_div_cancel _ hax] }
  end,
λ h,
  have hre : abs (y / x) * x.re = y.re,
    by rw ← of_real_div at h;
      simpa [-of_real_div] using congr_arg re h,
  have hre' : abs (x / y) * y.re = x.re,
    by rw [← hre, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have him : abs (y / x) * x.im = y.im,
    by rw ← of_real_div at h;
      simpa [-of_real_div] using congr_arg im h,
  have him' : abs (x / y) * y.im = x.im,
    by rw [← him, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have hxya : x.im / abs x = y.im / abs y,
    by rw [← him, abs_div, mul_comm, ← mul_div_comm, mul_div_cancel_left _ hay],
  have hnxya : (-x).im / abs x = (-y).im / abs y,
    by rw [neg_im, neg_im, neg_div, neg_div, hxya],
  if hxr : 0 ≤ x.re
  then
    have hyr : 0 ≤ y.re, from hre ▸ mul_nonneg (abs_nonneg _) hxr,
    by simp [arg, *] at *
  else
    have hyr : ¬ 0 ≤ y.re, from λ hyr, hxr $ hre' ▸ mul_nonneg (abs_nonneg _) hyr,
    if hxi : 0 ≤ x.im
    then
      have hyi : 0 ≤ y.im, from him ▸ mul_nonneg (abs_nonneg _) hxi,
      by simp [arg, *] at *
    else
      have hyi : ¬ 0 ≤ y.im, from λ hyi, hxi $ him' ▸ mul_nonneg (abs_nonneg _) hyi,
      by simp [arg, *] at *⟩

lemma arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x :=
if hx : x = 0 then by simp [hx]
else (arg_eq_arg_iff (mul_ne_zero (of_real_ne_zero.2 (ne_of_lt hr).symm) hx) hx).2 $
  by rw [abs_mul, abs_of_nonneg (le_of_lt hr), ← mul_assoc,
    of_real_mul, mul_comm (r : ℂ), ← div_div_eq_div_mul,
    div_mul_cancel _ (of_real_ne_zero.2 (ne_of_lt hr).symm),
    div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), one_mul]

lemma ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y :=
if hy : y = 0 then by simp * at *
else have hx : x ≠ 0, from λ hx, by simp [*, eq_comm] at *,
  by rwa [arg_eq_arg_iff hx hy, h₁, div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hy)), one_mul] at h₂

lemma arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 :=
by simp [arg, hx]

lemma arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
by rw [arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg, ← of_real_neg, arg_of_real_of_nonneg];
  simp [*, le_iff_eq_or_lt, lt_neg]

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
noncomputable def log (x : ℂ) : ℂ := x.abs.log + arg x * I

lemma log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]

lemma log_im (x : ℂ) : x.log.im = x.arg := by simp [log]

lemma exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x :=
by rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx,
  ← of_real_exp, real.exp_log (abs_pos.2 hx), mul_add, of_real_div, of_real_div,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ← mul_assoc,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]

lemma exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π)
  (hy₁ : - π < y.im) (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y :=
by rw [exp_eq_exp_re_mul_sin_add_cos, exp_eq_exp_re_mul_sin_add_cos y] at hxy;
  exact complex.ext
    (real.exp_injective $
      by simpa [abs_mul, abs_cos_add_sin_mul_I] using congr_arg complex.abs hxy)
    (by simpa [(of_real_exp _).symm, - of_real_exp, arg_real_mul _ (real.exp_pos _),
      arg_cos_add_sin_mul_I hx₁ hx₂, arg_cos_add_sin_mul_I hy₁ hy₂] using congr_arg arg hxy)

lemma log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂: x.im ≤ π) : log (exp x) = x :=
exp_inj_of_neg_pi_lt_of_le_pi
  (by rw log_im; exact neg_pi_lt_arg _)
  (by rw log_im; exact arg_le_pi _)
  hx₁ hx₂ (by rw [exp_log (exp_ne_zero _)])

lemma of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
complex.ext
  (by rw [log_re, of_real_re, abs_of_nonneg hx])
  (by rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

@[simp] lemma log_zero : log 0 = 0 := by simp [log]

@[simp] lemma log_one : log 1 = 0 := by simp [log]

lemma log_neg_one : log (-1) = π * I := by simp [log]

lemma log_I : log I = π / 2 * I := by simp [log]

lemma log_neg_I : log (-I) = -(π / 2) * I := by simp [log]

lemma exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :=
have real.exp (x.re) * real.cos (x.im) = 1 → real.cos x.im ≠ -1,
  from λ h₁ h₂, begin
    rw [h₂, mul_neg_eq_neg_mul_symm, mul_one, neg_eq_iff_neg_eq] at h₁,
    have := real.exp_pos x.re,
    rw ← h₁ at this,
    exact absurd this (by norm_num)
  end,
calc exp x = 1 ↔ (exp x).re = 1 ∧ (exp x).im = 0 : by simp [complex.ext_iff]
  ... ↔ real.cos x.im = 1 ∧ real.sin x.im = 0 ∧ x.re = 0 :
    begin
      rw exp_eq_exp_re_mul_sin_add_cos,
      simp [complex.ext_iff, cos_of_real_re, sin_of_real_re, exp_of_real_re,
        real.exp_ne_zero],
      split; finish [real.sin_eq_zero_iff_cos_eq]
    end
  ... ↔ (∃ n : ℤ, ↑n * (2 * π) = x.im) ∧ (∃ n : ℤ, ↑n * π = x.im) ∧ x.re = 0 :
    by rw [real.sin_eq_zero_iff, real.cos_eq_one_iff]
  ... ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :
    ⟨λ ⟨⟨n, hn⟩, ⟨m, hm⟩, h⟩, ⟨n, by simp [complex.ext_iff, hn.symm, h]⟩,
      λ ⟨n, hn⟩, ⟨⟨n, by simp [hn]⟩, ⟨2 * n, by simp [hn, mul_comm, mul_assoc, mul_left_comm]⟩,
        by simp [hn]⟩⟩

lemma exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 :=
by rw [exp_sub, div_eq_one_iff_eq _ (exp_ne_zero _)]

lemma exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * ((2 * π) * I) :=
by simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
calc cos (π / 2) = real.cos (π / 2) : by rw [of_real_cos]; simp
... = 0 : by simp

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
calc sin (π / 2) = real.sin (π / 2) : by rw [of_real_sin]; simp
... = 1 : by simp

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← of_real_sin, real.sin_pi]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← of_real_cos, real.cos_pi]; simp

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

section pow

noncomputable def cpow (x y : ℂ) : ℂ :=
if x = 0
  then if y = 0
    then 1
    else 0
  else exp (log x * y)

noncomputable instance : has_pow ℂ ℂ := ⟨cpow⟩

lemma cpow_def (x y : ℂ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log x * y) := rfl

@[simp] lemma cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]

@[simp] lemma zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 :=
by simp [cpow_def, *]

@[simp] lemma cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
if hx : x = 0 then by simp [hx, cpow_def]
else by rw [cpow_def, if_neg (@one_ne_zero ℂ _), if_neg hx, mul_one, exp_log hx]

@[simp] lemma one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 :=
by rw cpow_def; split_ifs; simp [one_ne_zero, *] at *

lemma cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
by simp [cpow_def]; split_ifs; simp [*, exp_add, mul_add] at *

lemma cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
  x ^ (y * z) = (x ^ y) ^ z :=
begin
  simp [cpow_def],
  split_ifs;
  simp [*, exp_ne_zero, log_exp h₁ h₂, mul_assoc] at *
end

lemma cpow_neg (x y : ℂ) : x ^ -y = (x ^ y)⁻¹ :=
by simp [cpow_def]; split_ifs; simp [exp_neg]

@[simp] lemma cpow_nat_cast (x : ℂ) : ∀ (n : ℕ), x ^ (n : ℂ) = x ^ n
| 0       := by simp
| (n + 1) := if hx : x = 0 then by simp only [hx, pow_succ,
    complex.zero_cpow (nat.cast_ne_zero.2 (nat.succ_ne_zero _)), zero_mul]
  else by simp [cpow_def, hx, mul_add, exp_add, pow_succ, (cpow_nat_cast n).symm, exp_log hx]

@[simp] lemma cpow_int_cast (x : ℂ) : ∀ (n : ℤ), x ^ (n : ℂ) = x ^ n
| (n : ℕ) := by simp; refl
| -[1+ n] := by rw fpow_neg_succ_of_nat;
  simp only [int.neg_succ_of_nat_coe, int.cast_neg, complex.cpow_neg, inv_eq_one_div,
    int.cast_coe_nat, cpow_nat_cast]

lemma cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : 0 < n) : (x ^ (n⁻¹ : ℂ)) ^ n = x :=
have (log x * (↑n)⁻¹).im = (log x).im / n,
  by rw [div_eq_mul_inv, ← of_real_nat_cast, ← of_real_inv, mul_im,
                of_real_re, of_real_im]; simp,
have h : -π < (log x * (↑n)⁻¹).im ∧ (log x * (↑n)⁻¹).im ≤ π,
  from (le_total (log x).im 0).elim
    (λ h, ⟨calc -π < (log x).im : by simp [log, neg_pi_lt_arg]
            ... ≤ ((log x).im * 1) / n : le_div_of_mul_le (nat.cast_pos.2 hn)
              (mul_le_mul_of_nonpos_left (by rw ← nat.cast_one; exact nat.cast_le.2 hn) h)
            ... = (log x * (↑n)⁻¹).im : by simp [this],
          this.symm ▸ le_trans (div_nonpos_of_nonpos_of_pos h (nat.cast_pos.2 hn))
            (le_of_lt real.pi_pos)⟩)
    (λ h, ⟨this.symm ▸ lt_of_lt_of_le (neg_neg_of_pos real.pi_pos)
            (div_nonneg h (nat.cast_pos.2 hn)),
          calc (log x * (↑n)⁻¹).im = (1 * (log x).im) / n : by simp [this]
            ... ≤ (log x).im : (div_le_of_le_mul (nat.cast_pos.2 hn)
              (mul_le_mul_of_nonneg_right (by rw ← nat.cast_one; exact nat.cast_le.2 hn) h))
            ... ≤ _ : by simp [log, arg_le_pi]⟩),
by rw [← cpow_nat_cast, ← cpow_mul _ h.1 h.2,
    inv_mul_cancel (show (n : ℂ) ≠ 0, from nat.cast_ne_zero.2 (nat.pos_iff_ne_zero.1 hn)),
    cpow_one]

end pow

end complex

namespace real

noncomputable def rpow (x y : ℝ) := ((x : ℂ) ^ (y : ℂ)).re

noncomputable instance : has_pow ℝ ℝ := ⟨rpow⟩

lemma rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl

lemma rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log x * y) :=
by simp only [rpow_def, complex.cpow_def];
  split_ifs;
  simp [*, (complex.of_real_log hx).symm, -complex.of_real_mul,
    (complex.of_real_mul _ _).symm, complex.exp_of_real_re] at *

end real

namespace complex

lemma of_real_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) :=
by simp [real.rpow_def_of_nonneg hx, complex.cpow_def]; split_ifs; simp [complex.of_real_log hx]

@[simp] lemma abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ (y : ℂ)) = x.abs ^ y :=
begin
  rw [real.rpow_def_of_nonneg (abs_nonneg _), complex.cpow_def],
  split_ifs;
  simp [*, abs_of_nonneg (le_of_lt (real.exp_pos _)), complex.log, complex.exp_add,
    add_mul, mul_right_comm _ I, exp_mul_I, abs_cos_add_sin_mul_I,
    (complex.of_real_mul _ _).symm, -complex.of_real_mul] at *
end

@[simp] lemma abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (n⁻¹ : ℂ)) = x.abs ^ (n⁻¹ : ℝ) :=
by rw ← abs_cpow_real; simp [-abs_cpow_real]

end complex

namespace real

@[simp] lemma rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 :=
by simp [rpow_def, *]

@[simp] lemma rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]

@[simp] lemma one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]

lemma rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y :=
by rw [rpow_def_of_nonneg hx];
  split_ifs; simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

lemma rpow_add {x : ℝ} (y z : ℝ) (hx : 0 < x) : x ^ (y + z) = x ^ y * x ^ z :=
by simp only [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_lt hx).symm, mul_add, exp_add]

lemma rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
by rw [← complex.of_real_inj, complex.of_real_cpow (rpow_nonneg_of_nonneg hx _),
    complex.of_real_cpow hx, complex.of_real_mul, complex.cpow_mul, complex.of_real_cpow hx];
  simp only [(complex.of_real_mul _ _).symm, (complex.of_real_log hx).symm,
    complex.of_real_im, neg_lt_zero, pi_pos, le_of_lt pi_pos]

lemma rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
by simp only [rpow_def_of_nonneg hx]; split_ifs; simp [*, exp_neg] at *

@[simp] lemma rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_pow _ _).symm, complex.cpow_nat_cast,
  complex.of_real_nat_cast, complex.of_real_re]

@[simp] lemma rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_fpow _ _).symm, complex.cpow_int_cast,
  complex.of_real_int_cast, complex.of_real_re]

lemma pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) : 
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
have hn0 : (n : ℝ) ≠ 0, by simpa [nat.pos_iff_ne_zero'] using hn,
by rw [← rpow_nat_cast, ← rpow_mul hx, mul_inv_cancel hn0, rpow_one]

end real
