import data.polynomial.derivative

open_locale big_operators
open_locale polynomial

/-- # Definition and some theorems about differentiating multiple times
-/

variables {R : Type*} [comm_ring R]

/-Definition
For any integer polynomial $f$ and $n\in\mathbb N$ we define `deriv_n f n` to be the $n$-th derivative of polynomial $f$. $h^{[n]}$ means $h\circ h\circ h\cdots\circ h$ $n$-times.
-/
noncomputable def deriv_n (f : R[X]) (n : ℕ) : R[X] := polynomial.derivative ^[n] f

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
polynomial.iterate_derivative_zero

/-Lemma
Like first derivative, higher derivatives still respect addition
-/
lemma deriv_n_add (p q :R[X]) (n : ℕ) : (deriv_n (p+q) n) = (deriv_n p n) + (deriv_n q n) :=
polynomial.iterate_derivative_add

/-Lemma
For any polynomial $f$ with degree $d$, the $d+1$-th derivative is zero.
-/
theorem deriv_too_much (f : R[X]): (deriv_n f (f.nat_degree + 1)) = 0 :=
polynomial.iterate_derivative_eq_zero $ nat.lt_succ_self _

/-Theorem
We also have that for $p,q\in\mathbb Z[x]$,
\[
    (p\times q)^{(n)} = \sum_{i=0}^n\left({n\choose i}p^{(i)}q^{(n-i)}\right)
\]
-/

lemma deriv_n_poly_prod (p q : R[X]) (n : ℕ) : deriv_n (p * q) n = ∑ k in finset.range n.succ, (polynomial.C (n.choose k:R)) * (deriv_n p (n-k)) * (deriv_n q k) :=
begin
  induction n with n IH,
  { simp only [nat.choose_self, nat.nat_zero_eq_zero, one_mul, zero_tsub, eq_self_iff_true,
      polynomial.C_eq_nat_cast, nat.cast_one, finset.sum_singleton, finset.range_one,
      zeroth_deriv, finset.sum_congr] },

  {
    transitivity
      ∑ (x : ℕ) in finset.range n, ↑((n + 1).choose (x + 1)) * deriv_n p (n - x) * deriv_n q (x + 1) + (p * deriv_n q (n + 1) + deriv_n p (n + 1) * q),

    { rw deriv_n, rw function.iterate_succ', dsimp, rw <-deriv_n,
    rw IH,
    simp only [polynomial.derivative_sum, polynomial.derivative_mul, zero_mul,
      polynomial.derivative_C, zero_add],
    rw [finset.sum_add_distrib],
    conv_lhs {
      rw finset.sum_range_succ', rw finset.sum_range_succ,
      simp only [zeroth_deriv, nat.choose_self, one_mul, nat.choose_zero_right, int.coe_nat_zero, nat.sub_self, polynomial.C_1, int.coe_nat_succ, nat.sub_zero, zero_add]},

    transitivity
        (∑ (i : ℕ) in finset.range n,
            polynomial.C (n.choose (i + 1):R) * (deriv_n p (n - (i + 1))).derivative * deriv_n q (i + 1)) +
        (∑ (x : ℕ) in finset.range n, polynomial.C (n.choose x:R) * deriv_n p (n - x) * (deriv_n q x).derivative) +
        ((p * (deriv_n q n).derivative) + (deriv_n p n).derivative * q),
    { simp[polynomial.C_eq_nat_cast], ring },
    congr' 1,
    swap, {
      simp only [deriv_n],
      rw function.iterate_succ',
    },
    rw [<-finset.sum_add_distrib],

    transitivity
        (∑ (x : ℕ) in finset.range n,
            ((polynomial.C ((n+1).choose (x + 1):R)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
    { apply finset.sum_congr rfl, intros x hx,
      simp only [finset.mem_range, ←nat.succ_le_iff, nat.succ_eq_add_one] at hx,

      transitivity
        (polynomial.C (n.choose (x + 1):R) * (deriv_n p (n - x)) * deriv_n q (x + 1) +
          polynomial.C (n.choose x:R) * deriv_n p (n - x) * (deriv_n q (x+1))),
      { simp only [deriv_succ, int.cast_coe_nat, ring_hom.eq_int_cast, add_left_inj],
        rw [←nat.sub_sub, nat.sub_add_cancel (le_tsub_of_add_le_left hx)] },
      { simp only [map_add, eq_self_iff_true, polynomial.C_eq_nat_cast, nat.cast_add,
          nat.choose_succ_succ],
        rw [←add_mul, ←add_mul, add_comm] } },

    simp} ,

    conv_rhs {rw finset.sum_range_succ', rw finset.sum_range_succ},
    simp only [deriv_succ, zeroth_deriv, nat.succ_eq_add_one, nat.choose_self, int.cast_coe_nat,
        ring_hom.eq_int_cast, one_mul, nat.succ_sub_succ_eq_sub, nat.choose_zero_right,
        int.coe_nat_zero, nat.sub_self, int.cast_one, int.coe_nat_succ, nat.sub_zero, zero_add],
    simp only [one_mul, map_one, polynomial.C_eq_nat_cast, nat.cast_one, finset.sum_congr],
    ring },
end

/-Theorem
For a polynomial $f$ we have $f^{(n)}=f^{(n-1)}\times f'$
-/

theorem poly_pow_deriv (f : R[X]) (n : ℕ) : (f ^ n).derivative = n * f ^ (n - 1) * f.derivative :=
begin
  induction n with n IH,
  { rw [pow_zero, polynomial.derivative_one, nat.cast_zero, zero_mul, zero_mul] },
  { cases n,
    { simp only [nat.nat_zero_eq_zero, one_mul, eq_self_iff_true, map_one, pow_one,
        nat.cast_one, tsub_self, pow_zero] },
    rw [pow_succ', polynomial.derivative_mul, IH, nat.succ_eq_add_one,
      nat.succ_eq_add_one, nat.add_sub_cancel, nat.add_sub_cancel, mul_right_comm, ←add_mul,
      nat.cast_add (n + 1), nat.cast_one, mul_assoc, ←pow_succ', add_one_mul] },
end

theorem deriv_n_C_mul (c : R) (n : ℕ) (f : R[X]) :
  (deriv_n (polynomial.C c * f) n) = (polynomial.C c) * (deriv_n f n) :=
begin
  rw [deriv_n, deriv_n, polynomial.iterate_derivative_C_mul],
end

theorem dvd_poly_pow_deriv (f : R[X]) (n m : ℕ) (c : R) (hn : 0 < n) (hm : 0 < m) :
  (n:R) ∣ polynomial.eval c (deriv_n (f^n) m) :=
begin
  obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero hm.ne',
  rw [deriv_n, function.iterate_succ, function.comp_app, ←deriv_n, poly_pow_deriv, mul_assoc,
    deriv_n, polynomial.iterate_derivative_cast_nat_mul, polynomial.eval_mul,
    polynomial.eval_nat_cast],
  exact dvd_mul_right _ _,
end

lemma deriv_X_pow (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (deriv_n (polynomial.X^n : R[X]) k) = ((finset.range k).prod (λ i, (n-i:R))) • (polynomial.X ^ (n-k)) :=
begin
  induction k with k ih,
  {simp only [zeroth_deriv, one_smul, finset.range_zero, finset.prod_empty, nat.sub_zero]},
  have hk': k ≤ n,
  { rw nat.succ_le_iff at hk, exact hk.le },
  rw [<-deriv_succ, ih hk', polynomial.derivative_smul],
  ext i, rw polynomial.coeff_smul, rw polynomial.coeff_smul, rw polynomial.coeff_derivative,
  simp only [polynomial.coeff_X_pow, boole_mul, mul_ite, mul_zero],
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
  (deriv_n (polynomial.X^n) k) = (polynomial.C ((finset.range k).prod (λ i, (n-i:R)))) * (polynomial.X ^ (n-k)) :=
begin
  rw deriv_X_pow _ _ hk, ext, rw [polynomial.coeff_smul, polynomial.coeff_C_mul, smul_eq_mul],
end

lemma deriv_X_pow_too_much (n : ℕ) (k : ℕ) (hk : n < k) :
  (deriv_n (polynomial.X^n : R[X]) k) = 0 :=
begin
  induction k with k IH, exfalso, linarith,
  {
    replace hk : n < k ∨ n = k := lt_or_eq_of_le (nat.lt_succ_iff.mp hk),
    cases hk,
      rw [<-deriv_succ, IH hk], simp only [polynomial.derivative_zero],
      rw [<-hk, <-deriv_succ, deriv_X_pow'], simp only [mul_one, nat.sub_self, polynomial.derivative_C, pow_zero],
      exact le_refl n,
  }
end

lemma deriv1_X_sub_pow (c:R) (m:ℕ) : ((polynomial.X - polynomial.C c)^m).derivative = m * (polynomial.X - polynomial.C c)^ (m-1) :=
begin
  cases m,
  { rw [pow_zero, polynomial.derivative_one, nat.cast_zero, zero_mul] },

  induction m with m IH,
  { rw [pow_one, polynomial.derivative_sub, polynomial.derivative_X, polynomial.derivative_C,
      sub_zero, nat.cast_one, one_mul, tsub_self, pow_zero] },

  simp only [nat.succ_eq_add_one] at IH ⊢ ,
  rw [pow_succ', polynomial.derivative_mul, IH],
  simp only [nat.add_sub_cancel, add_zero, mul_one, polynomial.derivative_sub, sub_zero,
    polynomial.derivative_X, polynomial.derivative_C, nat.cast_add, nat.cast_one],
  rw [mul_assoc, ←pow_succ', ←add_one_mul],
end

lemma deriv_X_sub_pow (n k : ℕ) (c : R) (hk : k ≤ n) :
  (deriv_n ((polynomial.X-polynomial.C c)^n) k) =
  (polynomial.C ((finset.range k).prod (λ i, (n-i:R)))) * ((polynomial.X - polynomial.C c) ^ (n-k)) :=
begin
  induction k with k IH,
  { simp only [zeroth_deriv, one_mul, polynomial.C_1, finset.range_zero, finset.prod_empty,
      nat.sub_zero] },
  { rw [deriv_n, function.iterate_succ_apply', ←deriv_n, IH (nat.le_of_succ_le hk),
      polynomial.derivative_mul, polynomial.derivative_C, zero_mul, zero_add,
      finset.prod_range_succ],
    simp only [polynomial.C_sub, polynomial.C_mul],
    suffices : ((polynomial.X - polynomial.C c) ^ (n - k)).derivative  = (polynomial.C (n:R) - polynomial.C (k:R)) * (polynomial.X - polynomial.C c) ^ (n - k.succ),
      rw this, ring,
    have triv : (polynomial.C (n:R) - polynomial.C (k:R)) = (polynomial.C (n-k:R)),
    { simp only [polynomial.C_sub], },
    rw deriv1_X_sub_pow,
    rw triv,
    simp only [polynomial.C_eq_nat_cast, map_sub],
    rw nat.cast_sub (nat.le_of_succ_le hk),
    rw nat.sub_succ' n k,
  },
end

lemma deriv_X_sub_pow_too_much (n k : ℕ) (c : R) (hk : n < k) :
  (deriv_n ((polynomial.X - polynomial.C c)^n) k) = 0 :=
begin
  induction k with k IH, exfalso, have triv : n ≥ 0, exact bot_le, replace triv : ¬ n < 0, exact not_lt.mpr triv, exact triv hk,
  {
    replace hk : n < k ∨ n = k, exact lt_or_eq_of_le (nat.lt_succ_iff.mp hk),
    cases hk,
      have triv := IH hk,
      rw <-deriv_succ, rw triv, simp only [polynomial.derivative_zero],
      rw <-deriv_succ, rw hk, rw deriv_X_sub_pow,
      simp only [mul_one, nat.sub_self, polynomial.derivative_C, pow_zero], exact le_refl k,
  },
end
