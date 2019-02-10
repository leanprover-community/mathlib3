import .derivative_props
import data.polynomial
import analysis.exponential

open real

theorem derivative_id_one : has_derivative_everywhere id 1 :=
begin
  intro x, rw has_derivative_at_iff_eps_del',
  intros ε He, existsi (1 : ℝ), split, norm_num, 
  intros h ha hb, simp, rw [div_self ha], simpa,
end

theorem derivative_pow {n : ℕ} : has_derivative_everywhere (λ x, x ^ n) (λ x, n * x ^ (n - 1)) := 
begin 
  induction n with n h, { simp, apply derivative_constant_zero },
  have rw1 : (λ (x : ℝ), x ^ nat.succ n) = (λ (x : ℝ), x ^ n * x) := by { funext, rw pow_succ' },
  have rw2 : (λ (x : ℝ), ↑(nat.succ n) * x ^ (nat.succ n - 1)) = (λ (x : ℝ), (↑n * x ^ (n - 1)) * x + x ^ n * 1),
    funext,
    cases n, { simp },
    { rw [nat.succ_sub_one, mul_assoc, ←pow_succ', nat.sub_add_cancel (nat.succ_pos n), 
          nat.cast_succ, add_mul, one_mul, mul_one] },
  rw [rw1, rw2],
  apply derivative_everywhere_mul _ _ _ _ h (derivative_id_one)
end

theorem derivative_sq : has_derivative_everywhere (λ x, x ^ 2) (λ x, 2 * x) :=
begin
  rw (by simp : (λ (x : ℝ), 2 * x) = (λ (x : ℝ), ↑2 * x ^ (2 - 1))), 
  apply @derivative_pow 2,
end

theorem derivative_polynomial (p : polynomial ℝ) 
: has_derivative_everywhere (λ x, polynomial.eval x p) (λ x, polynomial.eval x (polynomial.derivative p)) :=
begin
  apply polynomial.induction_on p,
  { simp [polynomial.eval_C], exact derivative_constant_zero },
  { simp [polynomial.derivative_add, polynomial.eval_add],
    intros p1 q1 Dp1 Dq1,
    apply derivative_everywhere_add _ _ _ _ Dp1 Dq1 },
  { intros n a Dxn,
    simp [polynomial.eval_mul, polynomial.derivative_monomial, polynomial.eval_pow],
    rw [←nat.add_sub_cancel n 1] {occs := occurrences.pos [3]}, rw add_comm, simp only [mul_assoc],
    conv {congr, skip, rw [←nat.cast_one, ←nat.cast_add]},
    apply derivative_everywhere_const_mul _ _ _ derivative_pow }
end

theorem derivative_polynomial' (a : ℕ → ℝ) (N : ℕ) : has_derivative_everywhere 
(λ x : ℝ, finset.sum (finset.range N) (λ (k : ℕ), a k * x ^ k))
(λ x : ℝ, finset.sum (finset.range N) (λ (k : ℕ), k * a k * x ^ (k - 1))) :=
begin
  induction N with n ih,
  { simp, apply derivative_constant_zero },
  { simp [finset.range_succ],
    apply derivative_everywhere_add,
    { conv { congr, skip, funext, rw [mul_comm ↑n _, mul_assoc] },
      apply derivative_everywhere_const_mul',
      apply derivative_pow },
    { exact ih } }
end

theorem derivative_exp_zero : has_derivative_at exp 0 1 :=
begin
  rw [has_derivative_at_iff_eps_del'],
  intros ε hε, 
  existsi min (abs(log (1 + ε))) (abs(log (1 - ε))),
  
end
