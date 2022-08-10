import data.polynomial.derivative

open polynomial

open_locale big_operators
open_locale polynomial

/-- # Definition and some theorems about differentiating multiple times
-/

variables {R : Type*} [comm_ring R]

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

/-Lemma
For any polynomial $f$ with degree $d$, the $d+1$-th derivative is zero.
-/
theorem deriv_too_much (f : R[X]): (deriv_n f (f.nat_degree + 1)) = 0 :=
iterate_derivative_eq_zero $ nat.lt_succ_self _

/-Theorem
We also have that for $p,q\in\mathbb Z[x]$,
\[
    (p\times q)^{(n)} = \sum_{i=0}^n\left({n\choose i}p^{(i)}q^{(n-i)}\right)
\]
-/

lemma deriv_n_poly_prod (p q : R[X]) (n : ℕ) :
  derivative ^[n] (p * q) =
  ∑ k in finset.range n.succ,
    n.choose k * (derivative ^[n - k] p) * (derivative ^[k] q) :=
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

/-Theorem
For a polynomial $f$ we have $f^{(n)}=f^{(n-1)}\times f'$
-/

theorem poly_pow_deriv (f : R[X]) (n : ℕ) : (f ^ n).derivative = n * f ^ (n - 1) * f.derivative :=
by simpa [mul_comm] using derivative_comp (X^n) f

theorem deriv_n_C_mul (c : R) (n : ℕ) (f : R[X]) :
  (deriv_n (C c * f) n) = (C c) * (deriv_n f n) :=
iterate_derivative_C_mul _ _ _

theorem dvd_poly_pow_deriv (f : R[X]) (n m : ℕ) (c : R) (hn : 0 < n) (hm : 0 < m) :
  (n:R) ∣ eval c (deriv_n (f^n) m) :=
begin
  obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero hm.ne',
  rw [deriv_n, function.iterate_succ, function.comp_app, ←deriv_n, poly_pow_deriv, mul_assoc,
    deriv_n, iterate_derivative_cast_nat_mul, eval_mul,
    eval_nat_cast],
  exact dvd_mul_right _ _,
end

lemma deriv_X_pow (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (deriv_n (X^n : R[X]) k) = ((finset.range k).prod (λ i, (n-i:R))) • (X ^ (n-k)) :=
begin
  induction k with k ih,
  {simp only [zeroth_deriv, one_smul, finset.range_zero, finset.prod_empty, nat.sub_zero]},
  have hk': k ≤ n,
  { rw nat.succ_le_iff at hk, exact hk.le },
  rw [<-deriv_succ, ih hk', derivative_smul],
  ext i, rw coeff_smul, rw coeff_smul, rw coeff_derivative,
  simp only [coeff_X_pow, boole_mul, mul_ite, mul_zero],
  split_ifs,
  { rw [finset.prod_range_succ, smul_eq_mul, smul_eq_mul, mul_one],
    apply congr_arg,
    norm_cast, rw h },

  { rw [nat.sub_succ, ←h, nat.pred_succ] at h_1, exfalso, exact h_1 rfl },

  { rw nat.sub_succ at h_1, rw h_1 at h, rw <-nat.succ_eq_add_one at h,
    rw nat.succ_pred_eq_of_pos at h, exfalso, simp only [eq_self_iff_true, not_true] at h,
    exact h, exact nat.sub_pos_of_lt hk },

  { rw [smul_zero, smul_zero] },
end

lemma deriv_X_pow' (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (deriv_n (X^n) k) = (C ((finset.range k).prod (λ i, (n-i:R)))) * (X ^ (n-k)) :=
by rw [deriv_X_pow _ _ hk, smul_eq_C_mul]

lemma deriv_X_pow_too_much (n : ℕ) (k : ℕ) (hk : n < k) :
  (deriv_n (X^n : R[X]) k) = 0 :=
iterate_derivative_eq_zero $ (nat_degree_X_pow_le n).trans_lt hk

lemma deriv1_X_sub_pow (c:R) (m:ℕ) : ((X - C c)^m).derivative = m * (X - C c)^ (m-1) :=
by rw [derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]

lemma deriv_X_sub_pow (n k : ℕ) (c : R) (hk : k ≤ n) :
  (deriv_n ((X-C c)^n) k) =
  (C ((finset.range k).prod (λ i, (n-i:R)))) * ((X - C c) ^ (n-k)) :=
begin
  induction k with k IH,
  { simp only [zeroth_deriv, one_mul, C_1, finset.range_zero, finset.prod_empty,
      nat.sub_zero] },
  { rw [deriv_n, function.iterate_succ_apply', ←deriv_n, IH (nat.le_of_succ_le hk),
      derivative_mul, derivative_C, zero_mul, zero_add,
      finset.prod_range_succ],
    simp only [C_sub, C_mul],
    suffices : ((X - C c) ^ (n - k)).derivative  = (C (n:R) - C (k:R)) * (X - C c) ^ (n - k.succ),
      rw this, ring,
    have triv : (C (n:R) - C (k:R)) = (C (n-k:R)),
    { simp only [C_sub], },
    rw deriv1_X_sub_pow,
    rw triv,
    simp only [C_eq_nat_cast, map_sub],
    rw nat.cast_sub (nat.le_of_succ_le hk),
    rw nat.sub_succ' n k,
  },
end

lemma deriv_X_sub_pow_too_much (n k : ℕ) (c : R) (hk : n < k) :
  (deriv_n ((X - C c)^n) k) = 0 :=
iterate_derivative_eq_zero $
  (nat_degree_pow_le.trans $ mul_le_of_le_one_right' nat_degree_X_sub_C_le).trans_lt hk
