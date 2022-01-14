import analysis.special_functions.exp_deriv
import analysis.special_functions.log_deriv
import analysis.special_functions.pow
-- import data.complex.exponential_bounds

open real set

lemma exp_sub_mul (x : ℝ) {c : ℝ} (hc : 0 ≤ c) : c - c * log c ≤ exp x - c * x :=
begin
  rcases eq_or_lt_of_le hc with rfl | hc,
  { simp [(exp_pos _).le] },
  suffices : exp (log c) - c * log c ≤ exp x - c * x,
  { rwa exp_log hc at this },
  have h₁ : differentiable ℝ (λ x, exp x - c * x) :=
    differentiable_exp.sub (differentiable_id.const_mul _),
  have h₂ : ∀ t, deriv (λ y, exp y - c * y) t = exp t - c := by simp,
  cases le_total (log c) x with hx hx,
  { refine (convex_Icc (log c) x).monotone_on_of_deriv_nonneg h₁.continuous.continuous_on
      h₁.differentiable_on _ (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx,
    intros y hy,
    rw interior_Icc at hy,
    rw [h₂, sub_nonneg, ←log_le_iff_le_exp hc],
    apply hy.1.le },
  { refine (convex_Icc x (log c)).antitone_on_of_deriv_nonpos h₁.continuous.continuous_on
      h₁.differentiable_on _ (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx,
    intros y hy,
    rw interior_Icc at hy,
    rw [h₂, sub_nonpos, ←le_log_iff_exp_le hc],
    apply hy.2.le },
end

example {a b c : ℝ} (hc : 0 ≤ c) : a ≤ b → a ≤ b + c :=
begin
  intro h,
  exact le_add_of_le_of_nonneg h hc,
end

example : 2⁻¹ ≤ (log 2)⁻¹ + (log 2)⁻¹ * log (log 2) :=
begin
  sorry
end


lemma thomas {x : ℝ} (hx : 0 ≤ x) : x + 1/2 ≤ 2 ^ x :=
begin
  have h₁ : 0 < log 2 := log_pos one_lt_two,
  have h₂ : 0 < (log 2)⁻¹ := inv_pos.2 h₁,
  rw ←le_sub_iff_add_le',
  have := exp_sub_mul (x * log 2) h₂.le,
  rw [log_inv, mul_neg_eq_neg_mul_symm, sub_neg_eq_add, mul_comm x, ←rpow_def_of_pos zero_lt_two,
    inv_mul_cancel_left₀ h₁.ne'] at this,
  apply le_trans _ this,
  rw ←inv_eq_one_div,
  -- simp only [log_inv, mul_neg_eq_neg_mul_symm, sub_neg_eq_add, mul_comm x, ←rpow_def_of_pos h₁,
  --   inv_mul_cancel_left₀ h₁.ne'] at this,
end
