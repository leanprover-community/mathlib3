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

open polynomial

/-Definition
For any integer polynomial $f$ and $n\in\mathbb N$ we define `deriv_n f n` to be the $n$-th derivative of polynomial $f$. $h^{[n]}$ means $h\circ h\circ h\cdots\circ h$ $n$-times.
-/
noncomputable def deriv_n (f : R[X]) (n : ℕ) : R[X] := derivative ^[n] f

/-Lemma
the zeroth derivative of polynomial $f$ is $f$ itself.
-/
lemma zeroth_deriv (f : R[X]) : deriv_n f 0 = f :=
function.iterate_zero_apply _ _

/-Lemma
the derivative of $f^{(n)}$ is $f^{(n+1)}$
-/
lemma deriv_succ (f : R[X]) (n : ℕ) : (deriv_n f n).derivative = (deriv_n f (n+1)) :=
(function.iterate_succ_apply' _ _ _).symm

/-Lemma
the $n$-th derivative of zero polynomial is $0$
-/
lemma deriv_zero_p (n : ℕ) : deriv_n (0 : R[X]) n = 0 :=
iterate_derivative_zero

/-Lemma
Like first derivative, higher derivatives still respect addition
-/
lemma deriv_n_add (p q :R[X]) (n : ℕ) : (deriv_n (p+q) n) = (deriv_n p n) + (deriv_n q n) :=
iterate_derivative_add

/-Theorem
We also have that for $p,q\in\mathbb Z[x]$,
\[
    (p\times q)^{(n)} = \sum_{i=0}^n\left({n\choose i}p^{(i)}q^{(n-i)}\right)
\]
-/

lemma deriv_n_poly_prod (p q : R[X]) (n : ℕ) :
  derivative ^[n] (p * q) =
  ∑ k in finset.range n.succ, n.choose k * (derivative ^[n - k] p) * (derivative ^[k] q) :=
polynomial.iterate_derivative_mul p q n

theorem deriv_n_C_mul (c : R) (n : ℕ) (f : R[X]) :
  (deriv_n (C c * f) n) = (C c) * (deriv_n f n) :=
iterate_derivative_C_mul _ _ _

lemma deriv_X_pow (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (derivative^[k] (X^n : R[X])) = ((finset.range k).prod (λ i, (n-i:R))) • (X ^ (n-k)) :=
iterate_derivative_X_pow_eq_smul n k hk

lemma deriv_X_pow' (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (derivative^[k] (X^n : R[X])) = (C ((finset.range k).prod (λ i, (n-i:R)))) * (X ^ (n-k)) :=
iterate_derivative_X_pow_eq_C_mul n k hk

lemma deriv_X_pow_too_much (n : ℕ) (k : ℕ) (hk : n < k) :
  (deriv_n (X^n : R[X]) k) = 0 :=
iterate_derivative_eq_zero $ (nat_degree_X_pow_le n).trans_lt hk

lemma deriv1_X_sub_pow (c:R) (m:ℕ) : ((X - C c)^m).derivative = m * (X - C c)^ (m-1) :=
derivative_X_sub_pow _ _

lemma deriv_X_sub_pow (n k : ℕ) (c : R) (hk : k ≤ n) :
  (derivative^[k] ((X-C c)^n)) =
  (C ((finset.range k).prod (λ i, (n-i:R)))) * ((X - C c) ^ (n-k)) :=
iterate_derivative_X_sub_pow _ _ _ hk

lemma deriv_X_sub_pow_too_much (n k : ℕ) (c : R) (hk : n < k) :
  (deriv_n ((X - C c)^n) k) = 0 :=
iterate_derivative_eq_zero $
  (nat_degree_pow_le.trans $ mul_le_of_le_one_right' nat_degree_X_sub_C_le).trans_lt hk
