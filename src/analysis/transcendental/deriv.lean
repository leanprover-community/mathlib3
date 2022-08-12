import data.polynomial.derivative

open_locale big_operators
open_locale polynomial

/-- # Definition and some theorems about differentiating multiple times
-/

variables {R : Type*} [comm_ring R]

namespace polynomial

lemma iterate_derivative_mul (p q : R[X]) (n : ℕ) :
  derivative ^[n] (p * q) =
  ∑ k in finset.range n.succ, n.choose k * (derivative ^[n - k] p) * (derivative ^[k] q) :=
begin
  induction n with n IH,
  { simp only [finset.range_one, finset.sum_singleton, nat.choose_self, nat.cast_one, one_mul, zero_tsub,
      function.iterate_zero_apply] },
  { transitivity
      (∑ x in finset.range n,
        (↑((n + 1).choose (x + 1)) * (derivative ^[n - x] p) * (derivative ^[x + 1] q))) +
      (p * (derivative ^[n + 1] q) + (derivative ^[n + 1] p) * q),
    { rw [function.iterate_succ', function.comp_apply, IH, derivative_sum],
      simp only [derivative_mul, zero_mul, derivative_cast_nat, zero_add],
      rw [finset.sum_add_distrib, finset.sum_range_succ', finset.sum_range_succ],
      simp only [nat.choose_self, one_mul, nat.choose_zero_right, id.def, nat.sub_self,
        function.comp_apply, function.iterate_zero, nat.sub_zero,
        nat.cast_one, ←function.iterate_succ_apply' derivative, nat.succ_eq_add_one],
      transitivity
        (∑ x in finset.range n, ↑(n.choose (x + 1)) * (derivative^[(n - (x + 1)) + 1] p) * (derivative^[x + 1] q)) +
        ((∑ x in finset.range n, ↑(n.choose x) * (derivative^[n - x] p) * (derivative^[x + 1] q))) +
        (p * (derivative^[n + 1] q) + (derivative^[n + 1] p * q)),
      { ring },

      congr' 1,
      rw [←finset.sum_add_distrib],
      refine finset.sum_congr rfl (λ x hx, _),
      simp only [finset.mem_range, ←nat.succ_le_iff, nat.succ_eq_add_one] at hx,
      rw [←nat.sub_add_comm hx, nat.add_sub_add_right, nat.choose_succ_succ, nat.cast_add],
      ring },

    { conv_rhs { rw [finset.sum_range_succ', finset.sum_range_succ] },
      simp only [nat.choose_self, nat.succ_eq_add_one, one_mul, nat.succ_sub_succ_eq_sub,
        nat.choose_zero_right, id.def, nat.sub_self, function.comp_app, function.iterate_zero,
        nat.sub_zero, nat.cast_one],
      ring } },
end

theorem dvd_iterate_derivative_pow (f : R[X]) (n m : ℕ) (c : R) (hm : 0 < m) :
  (n:R) ∣ eval c (derivative^[m] (f^n)) :=
begin
  obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero hm.ne',
  rw [function.iterate_succ_apply, derivative_pow, mul_assoc, iterate_derivative_cast_nat_mul,
    eval_mul, eval_nat_cast],
  exact dvd_mul_right _ _,
end

lemma iterate_derivative_X_pow_eq_C_mul (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (derivative^[k] (X^n : R[X])) = (C ((finset.range k).prod (λ i, (n-i:R)))) * (X ^ (n-k)) :=
begin
  induction k with k ih,
  { rw [function.iterate_zero_apply, finset.range_zero, finset.prod_empty, C_1, one_mul,
      nat.sub_zero] },
  have hk': k ≤ n := (nat.lt_of_succ_le hk).le,
  rw [function.iterate_succ_apply', ih hk', derivative_C_mul_X_pow, nat.succ_eq_add_one,
    finset.prod_range_succ, nat.sub_sub, ←nat.cast_sub hk'],
end

lemma iterate_derivative_X_pow_eq_smul (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (derivative^[k] (X^n : R[X])) = (∏ i in finset.range k, (n - i : R)) • X ^ (n - k) :=
by rw [iterate_derivative_X_pow_eq_C_mul n k hk, smul_eq_C_mul]

lemma derivative_X_add_pow (c:R) (m:ℕ) : ((X + C c) ^ m).derivative = m * (X + C c) ^ (m - 1) :=
by rw [derivative_pow, derivative_add, derivative_X, derivative_C, add_zero, mul_one]

lemma derivative_X_sub_pow (c:R) (m:ℕ) : ((X - C c) ^ m).derivative = m * (X - C c) ^ (m - 1) :=
by rw [derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]

lemma iterate_derivative_X_add_pow (n k : ℕ) (c : R) (hk : k ≤ n) :
  (derivative^[k] ((X + C c) ^ n)) =
  (C (∏ i in finset.range k, (n - i : R))) * (X + C c) ^ (n - k) :=
begin
  induction k with k IH,
  { simp only [function.iterate_zero_apply, one_mul, C_1, finset.range_zero, finset.prod_empty,
      nat.sub_zero] },
  { simp only [function.iterate_succ_apply', IH (nat.le_of_succ_le hk), derivative_mul, zero_mul,
      derivative_C, zero_add, finset.prod_range_succ, C_eq_nat_cast, nat.sub_sub, mul_assoc,
      ←nat.cast_sub (nat.le_of_succ_le hk), C_mul, derivative_X_add_pow, nat.succ_eq_add_one] },
end

lemma iterate_derivative_X_sub_pow (n k : ℕ) (c : R) (hk : k ≤ n) :
  (derivative^[k] ((X - C c) ^ n)) =
  (C (∏ i in finset.range k, (n - i : R))) * (X - C c) ^ (n - k) :=
by simp_rw [sub_eq_add_neg, ←C_neg, iterate_derivative_X_add_pow _ _ _ hk, ←sub_eq_add_neg]

end polynomial
