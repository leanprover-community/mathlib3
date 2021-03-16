import data.polynomial.iterated_deriv
import analysis.special_functions.integrals
import ring_theory.algebraic


open interval_integral real polynomial finset set
open_locale big_operators

noncomputable theory

protected def I (f : polynomial ℝ) := λ t, ∫ x in 0..t, exp (t - x) * f.eval x

protected def D (n : ℕ) (f : polynomial ℝ) := λ x, (f.iterated_deriv n).eval x

section main
variables

@[simp] lemma I_zero_t (t : ℝ) : I 0 t = 0 := by simp [I]

lemma I_eq_I_deriv (f : polynomial ℝ) (t : ℝ) :
  I f t = exp t * f.eval 0 - f.eval t + I f.derivative t :=
begin
  unfold I,
  simp only [mul_comm],
  have hu : ∀ x ∈ interval 0 t, has_deriv_at (λ x, f.eval x) (f.derivative.eval x) x, { sorry },
  have hv : ∀ x ∈ interval 0 t, has_deriv_at (λ x, -exp(t - x)) (exp (t - x)) x, { sorry },
  rw integral_mul_deriv_eq_deriv_mul hu hv _ _,
  simp [mul_comm],
  sorry,
  sorry
end

lemma add_sub_add_eq_sub_add_sub {G : Type*} [add_comm_group G] (a b c d : G) :
a + b - (c + d) = (a - c) + (b - d) := by abel


lemma I_eq_sum_sub_sum' (n : ℕ) (f : polynomial ℝ) (t : ℝ) : I f t =
  exp t * ∑ j in range n, D j f 0 - ∑ j in range n, D j f t + I (f.iterated_deriv n) t :=
begin
  induction n with k ih generalizing, { simp },
  rw [sum_range_succ, sum_range_succ, mul_add, add_sub_add_eq_sub_add_sub, ih,
    I_eq_I_deriv (f.iterated_deriv k) t, iterated_deriv_succ],
  abel,
end

lemma I_eq_sum_sub_sum (f : polynomial ℝ) (t : ℝ) : I f t =
  exp t * ∑ j in range (f.nat_degree + 1), D j f 0 - ∑ j in range (f.nat_degree + 1), D j f t :=
begin
  have := I_eq_sum_sub_sum' (f.nat_degree + 1) f t,
  rwa [iterated_deriv_eq_zero_of_nat_degree_lt, I_zero_t, add_zero] at this,
  exact nat.lt_succ_self _,
end

lemma lemma_3 {n : ℕ}
  (α : fin n → ℝ) (hα : function.injective α) (ha : ∀ i, is_algebraic ℤ (α i))
  (β : fin n → ℕ) (hβ : ∀ i, β i ≠ 0) :
  ∑ i, (β i : ℝ) * exp (α i) ≠ 0 :=
begin
  sorry
end

/-- final goal -/
theorem lindemann {n : ℕ}
  (α : fin n → ℝ) (hα : function.injective α) (ha : ∀ i, is_algebraic ℤ (α i))
  (β : fin n → ℝ) (hβ : ∀ i, β i ≠ 0) :
  ∑ i, β i * exp (α i) ≠ 0 :=
begin
  by_contradiction,
  rw not_not at h,
  sorry
end

end main
