/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import analysis.calculus.taylor
import analysis.calculus.cont_diff
import data.set.intervals.unordered_interval

/-!
# Stuff for analysis.calculus.taylor
-/

open set

open_locale nat

section

variables {α : Type*} [lattice α]

def uIoo (x y : α) : set α := Ioo (x ⊓ y) (x ⊔ y)

lemma uIoo_of_le {x y : α} (h : x ≤ y) : uIoo x y = Ioo x y :=
by rw [uIoo, inf_eq_left.2 h, sup_eq_right.2 h]

lemma uIoo_of_ge {x y : α} (h : y ≤ x) : uIoo x y = Ioo y x :=
by rw [uIoo, inf_eq_right.2 h, sup_eq_left.2 h]

lemma uIoo_comm (x y : α) : uIoo x y = uIoo y x := by rw [uIoo, uIoo, inf_comm, sup_comm]

lemma uIoo_subset_Ioo {a₁ a₂ b₁ b₂ : α} (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) :
  uIoo a₁ b₁ ⊆ Ioo a₂ b₂ :=
Ioo_subset_Ioo (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

end

lemma taylor_mean_remainder_unordered {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
  (hf : cont_diff_on ℝ n f (uIcc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (uIcc x₀ x)) (uIoo x₀ x))
  (gcont : continuous_on g (uIcc x₀ x))
  (gdiff : ∀ (x_1 : ℝ), x_1 ∈ uIoo x₀ x → has_deriv_at g (g' x_1) x_1)
  (g'_ne : ∀ (x_1 : ℝ), x_1 ∈ uIoo x₀ x → g' x_1 ≠ 0) :
  ∃ (x' : ℝ) (hx' : x' ∈ uIoo x₀ x), f x - taylor_within_eval f n (uIcc x₀ x) x₀ x =
  ((x - x')^n /n! * (g x - g x₀) / g' x') •
    (iterated_deriv_within (n+1) f (uIcc x₀ x) x') :=
begin
  rcases ne.lt_or_lt hx with hx₀ | hx₀,
  { rw [uIcc_of_le hx₀.le] at hf hf' gcont ⊢,
    rw [uIoo_of_le hx₀.le] at g'_ne gdiff hf' ⊢,
    exact taylor_mean_remainder hx₀ hf hf' gcont gdiff g'_ne },
  rw [uIcc_of_ge hx₀.le] at hf hf' gcont ⊢,
  rw [uIoo_of_ge hx₀.le] at g'_ne gdiff hf' ⊢,
  rcases exists_ratio_has_deriv_at_eq_ratio_slope (λ t, taylor_within_eval f n (Icc x x₀) t x)
    (λ t, ((n! : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (Icc x x₀) t)) hx₀
    (continuous_on_taylor_within_eval (unique_diff_on_Icc hx₀) hf)
    (λ _ hy, taylor_within_eval_has_deriv_at_Ioo x hx₀ hy hf hf')
    g g' gcont gdiff with ⟨y, hy, h⟩,
  use [y, hy],
  -- The rest is simplifications and trivial calculations
  simp only [taylor_within_eval_self] at h,
  rw [mul_comm, ←div_left_inj' (g'_ne y hy), mul_div_cancel _ (g'_ne y hy)] at h,
  rw [←neg_sub, ←h],
  field_simp [g'_ne y hy, n.factorial_ne_zero],
  ring,
end

lemma taylor_mean_remainder_lagrange_unordered {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
  (hf : cont_diff_on ℝ n f (uIcc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (uIcc x₀ x)) (uIoo x₀ x)) :
  ∃ (x' : ℝ) (hx' : x' ∈ uIoo x₀ x), f x - taylor_within_eval f n (uIcc x₀ x) x₀ x =
  (iterated_deriv_within (n+1) f (uIcc x₀ x) x') * (x - x₀)^(n+1) /(n+1)! :=
begin
  have gcont : continuous_on (λ (t : ℝ), (x - t) ^ (n + 1)) (uIcc x₀ x) :=
  by { refine continuous.continuous_on _, continuity },
  have xy_ne : ∀ (y : ℝ), y ∈ uIoo x₀ x → (x - y)^n ≠ 0 :=
  begin
    intros y hy,
    refine pow_ne_zero _ _,
    rw [sub_ne_zero],
    cases le_total x₀ x,
    { rw [uIoo_of_le h] at hy,
      exact hy.2.ne' },
    { rw [uIoo_of_ge h] at hy,
      exact hy.1.ne }
  end,
  have hg' : ∀ (y : ℝ), y ∈ uIoo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 :=
  λ y hy, mul_ne_zero (neg_ne_zero.mpr (nat.cast_add_one_ne_zero n)) (xy_ne y hy),
  -- We apply the general theorem with g(t) = (x - t)^(n+1)
  rcases taylor_mean_remainder_unordered hx hf hf' gcont (λ y _, monomial_has_deriv_aux y x _) hg'
    with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [sub_self, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h,
  rw [h, neg_div, ←div_neg, neg_mul, neg_neg],
  field_simp [n.cast_add_one_ne_zero, n.factorial_ne_zero, xy_ne y hy],
  ring,
end

-- x' should be in uIoo x₀ x
lemma taylor_mean_remainder_central_aux {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x₀ x a b : ℝ} {n : ℕ}
  (hab : a < b) (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b)
  (hf : cont_diff_on ℝ n f (Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Ioo a b))
  (gcont : continuous_on g (Icc a b))
  (gdiff : ∀ (y : ℝ), y ∈ Ioo a b → has_deriv_at g (g' y) y) :
  ∃ (x' : ℝ) (hx' : x' ∈ Ioo a b), x' ≠ x ∧ (f x - taylor_within_eval f n (Icc a b) x₀ x) * g' x' =
  ((x - x')^n / n! * (g x - g x₀)) • (iterated_deriv_within (n+1) f (Icc a b) x') :=
begin
  rcases eq_or_ne x₀ x with rfl | hx',
  { simp only [sub_self, taylor_within_eval_self, mul_zero, zero_div, zero_smul, eq_self_iff_true,
      exists_prop, and_true, zero_mul],
    obtain ⟨x', hx'⟩ := ((Ioo_infinite hab).diff (set.finite_singleton x₀)).nonempty,
    exact ⟨x', by simpa using hx'⟩ },
  rcases ne.lt_or_lt hx' with hx' | hx',
  { have h₁ : Icc x₀ x ⊆ Icc a b := Icc_subset_Icc hx₀.1 hx.2,
    have h₂ : Ioo x₀ x ⊆ Ioo a b := Ioo_subset_Ioo hx₀.1 hx.2,
    obtain ⟨y, hy, h⟩ := exists_ratio_has_deriv_at_eq_ratio_slope
      (λ t, taylor_within_eval f n (Icc a b) t x)
      (λ t, ((n! : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (Icc a b) t)) hx'
      ((continuous_on_taylor_within_eval (unique_diff_on_Icc hab) hf).mono h₁)
      (λ _ hy, taylor_within_eval_has_deriv_at_Ioo _ hab (h₂ hy) hf hf') g g'
      (gcont.mono h₁) (λ y hy, gdiff y (h₂ hy)),
    refine ⟨y, h₂ hy, hy.2.ne, _⟩,
    -- The rest is simplifications and trivial calculations
    simp only [taylor_within_eval_self] at h,
    field_simp [←h, n.factorial_ne_zero],
    ring },
  { have h₁ : Icc x x₀ ⊆ Icc a b := Icc_subset_Icc hx.1 hx₀.2,
    have h₂ : Ioo x x₀ ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hx₀.2,
    obtain ⟨y, hy, h⟩ := exists_ratio_has_deriv_at_eq_ratio_slope
      (λ t, taylor_within_eval f n (Icc a b) t x)
      (λ t, ((n! : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (Icc a b) t)) hx'
      ((continuous_on_taylor_within_eval (unique_diff_on_Icc hab) hf).mono h₁)
      (λ _ hy, taylor_within_eval_has_deriv_at_Ioo _ hab (h₂ hy) hf hf') g g'
      (gcont.mono h₁) (λ y hy, gdiff y (h₂ hy)),
    refine ⟨y, h₂ hy, hy.1.ne', _⟩,
    -- The rest is simplifications and trivial calculations
    simp only [taylor_within_eval_self] at h,
    rw [←neg_sub, neg_mul, ←h],
    field_simp [n.factorial_ne_zero],
    ring },
end

lemma taylor_mean_remainder_central {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x₀ x a b : ℝ} {n : ℕ} (hab : a < b)
  (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b)
  (hf : cont_diff_on ℝ n f (Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Ioo a b))
  (gcont : continuous_on g (Icc a b))
  (gdiff : ∀ (y : ℝ), y ∈ Ioo a b → has_deriv_at g (g' y) y)
  (g'_ne : ∀ (y : ℝ), y ∈ Ioo a b → g' y ≠ 0) :
  ∃ (x' : ℝ) (hx' : x' ∈ Ioo a b), f x - taylor_within_eval f n (Icc a b) x₀ x =
  ((x - x')^n / n! * (g x - g x₀) / g' x') •
    (iterated_deriv_within (n+1) f (Icc a b) x') :=
begin
  obtain ⟨y, hy, hyx, h⟩ := taylor_mean_remainder_central_aux hab hx hx₀ hf hf' gcont gdiff,
  refine ⟨y, hy, _⟩,
  rw [smul_eq_mul] at h,
  rw [smul_eq_mul, div_mul_eq_mul_div, ←h, mul_div_cancel],
  exact g'_ne _ hy,
end

lemma taylor_mean_remainder_lagrange_central {f : ℝ → ℝ} {x x₀ a b : ℝ} {n : ℕ} (hab : a < b)
  (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b)
  (hf : cont_diff_on ℝ n f (Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Ioo a b)) :
  ∃ (x' : ℝ) (hx' : x' ∈ Ioo a b), f x - taylor_within_eval f n (Icc a b) x₀ x =
  (iterated_deriv_within (n+1) f (Icc a b) x') * (x - x₀)^(n+1) / (n+1)! :=
begin
  have gcont : continuous_on (λ (t : ℝ), (x - t) ^ (n + 1)) (Icc a b) :=
  by { refine continuous.continuous_on _, continuity },
  rcases taylor_mean_remainder_central_aux hab hx hx₀ hf hf' gcont
    (λ y _, monomial_has_deriv_aux y x _) with ⟨y, hy, hy', h⟩,
  have hy_ne : x - y ≠ 0 := sub_ne_zero_of_ne hy'.symm,
  use [y, hy],
  dsimp at h,
  rw [←eq_div_iff] at h,
  swap,
  { exact mul_ne_zero (neg_ne_zero.2 (by positivity)) (by positivity) },
  simp only [h, sub_self, zero_pow' _ (nat.succ_ne_zero n), zero_sub, mul_neg, neg_mul,
    nat.factorial_succ, nat.cast_add_one, neg_div_neg_eq, nat.cast_mul] with field_simps,
  rw [mul_left_comm, ←mul_assoc, ←div_div, div_eq_iff (pow_ne_zero _ hy_ne), div_mul_eq_mul_div],
  congr' 1,
  ring_nf
end

lemma taylor_mean_remainder_cauchy_central {f : ℝ → ℝ} {x x₀ a b : ℝ} {n : ℕ} (hab : a < b)
  (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b)
  (hf : cont_diff_on ℝ n f (Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Ioo a b)) :
  ∃ (x' : ℝ) (hx' : x' ∈ Ioo a b), f x - taylor_within_eval f n (Icc a b) x₀ x =
  (iterated_deriv_within (n+1) f (Icc a b) x') * (x - x')^n /n! * (x - x₀) :=
begin
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder_central hab hx hx₀ hf hf' continuous_on_id
    (λ _ _, has_deriv_at_id _) (λ _ _, by simp) with ⟨y, hy, h⟩,
  refine ⟨y, hy, _⟩,
  rw h,
  field_simp [n.factorial_ne_zero],
  ring,
end

lemma taylor_mean_remainder_bound_central {f : ℝ → ℝ} {a b C x x₀ : ℝ} {n : ℕ}
  (hab : a ≤ b) (hf : cont_diff_on ℝ (n+1) f (Icc a b)) (hx : x ∈ Icc a b) (hx₀ : x₀ ∈ Icc a b)
  (hC : ∀ y ∈ Ioo a b, ‖iterated_deriv_within (n + 1) f (Icc a b) y‖ ≤ C) :
  ‖f x - taylor_within_eval f n (Icc a b) x₀ x‖ ≤ C * |x - x₀| ^ (n + 1) / (n + 1)! :=
begin
  rcases eq_or_lt_of_le hab with rfl | hab,
  { simp only [Icc_self, mem_singleton_iff] at hx hx₀,
    substs hx₀ hx,
    rw [taylor_within_eval_self, sub_self, sub_self, abs_zero, zero_pow nat.succ_pos', mul_zero,
      zero_div, norm_zero] },
  have : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Ioo a b),
  { refine (hf.differentiable_on_iterated_deriv_within _ (unique_diff_on_Icc hab)).mono
      Ioo_subset_Icc_self,
    rw [←nat.cast_add_one, nat.cast_lt],
    exact nat.lt_succ_self _ },
  obtain ⟨x', hx', h⟩ := taylor_mean_remainder_lagrange_central hab hx hx₀ hf.of_succ this,
  rw [h, norm_div, norm_mul, real.norm_coe_nat, real.norm_eq_abs ((x - x₀) ^ _), ←abs_pow],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  exact mul_le_mul_of_nonneg_right (hC _ hx') (abs_nonneg _),
end

lemma exists_taylor_mean_remainder_bound_central {f : ℝ → ℝ} {a b x₀ : ℝ} {n : ℕ}
  (hab : a ≤ b) (hf : cont_diff_on ℝ (n+1) f (Icc a b)) (hx₀ : x₀ ∈ Icc a b) :
  ∃ C, ∀ x ∈ Icc a b, ‖f x - taylor_within_eval f n (Icc a b) x₀ x‖ ≤ C * |x - x₀| ^ (n + 1) :=
begin
  rcases eq_or_lt_of_le hab with rfl | h,
  { refine ⟨0, λ x hx, _⟩,
    rw [Icc_self, mem_singleton_iff] at hx hx₀,
    rw [hx₀, hx, taylor_within_eval_self, sub_self, zero_mul, norm_zero] },
  let C := Sup ((λ y, ‖iterated_deriv_within (n + 1) f (Icc a b) y‖) '' Icc a b),
  refine ⟨C / (n + 1)!, λ x hx, _⟩,
  rw [div_mul_eq_mul_div],
  refine taylor_mean_remainder_bound_central hab hf hx hx₀ _,
  intros y hy,
  refine continuous_on.le_Sup_image_Icc _ (Ioo_subset_Icc_self hy),
  exact (hf.continuous_on_iterated_deriv_within le_rfl (unique_diff_on_Icc h)).norm,
end
