import data.polynomial.derivative

open_locale big_operators
open_locale polynomial

/-- # Definition and some theorems about differentiating multiple times
-/

/-Definition
For any integer polynomial $f$ and $n\in\mathbb N$ we define `deriv_n f n` to be the $n$-th derivative of polynomial $f$. $h^{[n]}$ means $h\circ h\circ h\cdots\circ h$ $n$-times.
-/
noncomputable def deriv_n (f : ℤ[X]) (n : ℕ) : ℤ[X] := polynomial.derivative ^[n] f

/-Lemma
the zeroth derivative of polynomial $f$ is $f$ itself.
-/
lemma zeroth_deriv (f : ℤ[X]) : deriv_n f 0 = f :=
function.iterate_zero_apply _ _

/-Lemma
the derivative of $f^{(n)}$ is $f^{(n+1)}$
-/
lemma deriv_succ (f : ℤ[X]) (n : ℕ) : (deriv_n f n).derivative = (deriv_n f (n+1)) :=
(function.iterate_succ_apply' _ _ _).symm

/-Lemma
the $n$-th derivative of zero polynomial is $0$
-/
lemma deriv_zero_p (n : ℕ) : deriv_n 0 n = 0 :=
polynomial.iterate_derivative_zero

/-Lemma
Like first derivative, higher derivatives still respect addition
-/
lemma deriv_n_add (p q :ℤ[X]) (n : ℕ) : (deriv_n (p+q) n) = (deriv_n p n) + (deriv_n q n) :=
polynomial.iterate_derivative_add

/-Lemma
For any polynomial $f$ with degree $d$, the $d+1$-th derivative is zero.
-/
theorem deriv_too_much (f : ℤ[X]): (deriv_n f (f.nat_degree + 1)) = 0 :=
polynomial.iterate_derivative_eq_zero $ nat.lt_succ_self _

/-Theorem
We also have that for $p,q\in\mathbb Z[x]$,
\[
    (p\times q)^{(n)} = \sum_{i=0}^n\left({n\choose i}p^{(i)}q^{(n-i)}\right)
\]
-/

lemma deriv_n_poly_prod (p q : ℤ[X]) (n : ℕ) : deriv_n (p * q) n = ∑ k in finset.range n.succ, (polynomial.C (n.choose k:ℤ)) * (deriv_n p (n-k)) * (deriv_n q k) :=
begin

    -- We prove by induction on $n$.
    induction n with n IH,
    -- For $n=0$, we are using `zeroth_deriv`.
    simp only [zeroth_deriv, nat.choose_self, int.cast_coe_nat, ring_hom.eq_int_cast, one_mul, nat.cast_one, finset.sum_singleton, finset.range_one],

    {
        -- For inductive case
        -- We use $(pq)^{(n+1)}=d(pq)^{(n)}$, inductive hypothesis and that derivative is linear.
        rw deriv_n, rw function.iterate_succ', dsimp, rw <-deriv_n,
        rw IH, simp only [polynomial.derivative_sum, polynomial.derivative_mul, zero_mul, polynomial.derivative_C, zero_add, polynomial.derivative_sum, polynomial.derivative_mul, zero_mul, polynomial.derivative_C, zero_add],
        -- The rest of the proves is essentially openning and closing brackets and renaming summing indeces.
        rw finset.sum_add_distrib,
        conv_lhs {rw finset.sum_range_succ', rw finset.sum_range_succ, simp only [zeroth_deriv, nat.choose_self, one_mul, nat.choose_zero_right, int.coe_nat_zero, nat.sub_self, polynomial.C_1, int.coe_nat_succ, nat.sub_zero, zero_add]},

        transitivity
            (∑ (i : ℕ) in finset.range n,
                polynomial.C (n.choose (i + 1):ℤ) * (deriv_n p (n - (i + 1))).derivative * deriv_n q (i + 1)) +
            (∑ (x : ℕ) in finset.range n, polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q x).derivative) +
            ((deriv_n p n).derivative * q + (p * (deriv_n q n).derivative)),
        { ring },
        rw [<-finset.sum_add_distrib, ←eq_sub_iff_add_eq],

        transitivity
            (∑ (x : ℕ) in finset.range n,
                (polynomial.C (n.choose (x + 1):ℤ) * (deriv_n p (n - x)) * deriv_n q (x + 1) +
                 polynomial.C (n.choose x:ℤ) * deriv_n p (n - x) * (deriv_n q (x+1)))),
        {
            apply finset.sum_congr rfl, intros i hi,
            simp only [deriv_succ, int.cast_coe_nat, ring_hom.eq_int_cast, add_left_inj],
            simp only [finset.mem_range, ←nat.succ_le_iff, nat.succ_eq_add_one] at hi,
            rw [←nat.sub_sub, nat.sub_add_cancel (le_tsub_of_add_le_left hi)],
        },

        transitivity
            (∑ (x : ℕ) in finset.range n,
                ((polynomial.C (n.choose x:ℤ) + polynomial.C (n.choose (x + 1):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i, ring,
        },

        transitivity
            (∑ (x : ℕ) in finset.range n,
                ((polynomial.C (n.choose x + (n.choose (x + 1)):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i,
            simp only [int.cast_add, ring_hom.eq_int_cast],
        },

        transitivity
            (∑ (x : ℕ) in finset.range n,
                ((polynomial.C ((n+1).choose (x + 1):ℤ)) * (deriv_n p (n - x)) * deriv_n q (x + 1))),
        {
            apply congr_arg, rw function.funext_iff, intro i,
            rw [nat.choose_succ_succ, int.coe_nat_add],
        },

        conv_rhs {rw finset.sum_range_succ', rw finset.sum_range_succ},
        simp only [deriv_succ, zeroth_deriv, nat.succ_eq_add_one, nat.choose_self, int.cast_coe_nat,
            ring_hom.eq_int_cast, one_mul, nat.succ_sub_succ_eq_sub, nat.choose_zero_right,
            int.coe_nat_zero, nat.sub_self, int.cast_one, int.coe_nat_succ, nat.sub_zero, zero_add],
        ring,
    }
end

/-Theorem
For a polynomial $f$ then if $n>0$, we have $f^{(n)}=f^{(n-1)}\times f'$
-/

theorem poly_pow_deriv (f : ℤ[X]) (n : ℕ) (hn : 0 < n) : (f ^ n).derivative = (polynomial.C (n:ℤ)) * (f ^ (n-1)) * f.derivative :=
begin
    induction n with n IH,
    exfalso, linarith,
    {
        cases n,
        simp only [ring_hom.eq_int_cast, one_mul, int.coe_nat_zero, int.cast_one, int.coe_nat_succ, pow_one, zero_add, pow_zero],
        replace IH := IH (nat.succ_pos n),
        rw nat.succ_eq_add_one, rw pow_add, simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, polynomial.derivative_mul, int.cast_one, nat.succ_add_sub_one,
 int.coe_nat_succ, pow_one], rw IH, simp only [nat.succ_sub_succ_eq_sub, polynomial.C_add, polynomial.C_1, int.coe_nat_succ, nat.sub_zero, nat.succ_sub_succ_eq_sub,
 int.coe_nat_succ, nat.sub_zero],
        have eq1 : (polynomial.C ↑n + 1) * f ^ n * f.derivative * f = (polynomial.C ↑n + 1) * f ^ (n+1) * f.derivative,
        {
            rw pow_add, simp only [int.cast_coe_nat, ring_hom.eq_int_cast, pow_one], ring,
        } ,
        rw eq1, rw nat.succ_eq_add_one, repeat {rw add_mul}, simp only [int.cast_coe_nat, ring_hom.eq_int_cast, one_mul],
    }
end

theorem deriv_n_C_mul (c : ℤ) (n : ℕ) (f : ℤ[X]) :
  (deriv_n (polynomial.C c * f) n) = (polynomial.C c) * (deriv_n f n) :=
begin
  rw [deriv_n, deriv_n, polynomial.iterate_derivative_C_mul],
end

theorem dvd_poly_pow_deriv (f : ℤ[X]) (n m : ℕ) (c : ℤ) (hn : 0 < n) (hm : 0 < m) :
  (n:ℤ) ∣ polynomial.eval c (deriv_n (f^n) m) :=
begin
    cases m, linarith,

    rw [deriv_n, function.iterate_succ], simp only [function.comp_app], rw [<-deriv_n], rw poly_pow_deriv,
    have triv : polynomial.C ↑n * f ^ (n - 1) * f.derivative = polynomial.C ↑n * (f ^ (n - 1) * f.derivative) := by ring,
    rw triv,
    rw deriv_n_C_mul, rw polynomial.eval_mul, simp only [polynomial.eval_C, dvd_mul_right], assumption,
end

lemma deriv_X_pow (n : ℕ) (k : ℕ) (hk : k ≤ n) :
  (deriv_n (polynomial.X^n) k) = ((finset.range k).prod (λ i, (n-i:ℤ))) • (polynomial.X ^ (n-k)) :=
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
  (deriv_n (polynomial.X^n) k) = (polynomial.C ((finset.range k).prod (λ i, (n-i:ℤ)))) * (polynomial.X ^ (n-k)) :=
begin
  rw deriv_X_pow _ _ hk, ext, rw [polynomial.coeff_smul, polynomial.coeff_C_mul, smul_eq_mul],
end

lemma deriv_X_pow_too_much (n : ℕ) (k : ℕ) (hk : n < k) :
  (deriv_n (polynomial.X^n) k) = 0 :=
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

lemma deriv1_X_sub_pow (c:ℤ) (m:ℕ) : ((polynomial.X - polynomial.C c)^m).derivative = (polynomial.C (m:ℤ)) * (polynomial.X - polynomial.C c)^ (m-1) :=
begin
  cases m, simp only [polynomial.derivative_one, int.coe_nat_zero, zero_mul, polynomial.C_0, pow_zero],

  induction m with m IH,
  simp only [mul_one, int.coe_nat_zero, polynomial.derivative_sub, polynomial.C_1, sub_zero, int.coe_nat_succ, pow_one, polynomial.derivative_X, polynomial.derivative_C, zero_add, pow_zero],

  simp only [nat.succ_sub_succ_eq_sub, polynomial.C_add, polynomial.C_1, int.coe_nat_succ, nat.sub_zero], rw [nat.succ_eq_add_one, pow_add, pow_one, polynomial.derivative_mul, IH],
  rw [mul_assoc],
  have triv : (polynomial.X - polynomial.C c) ^ (m.succ - 1) * (polynomial.X - polynomial.C c) = (polynomial.X - polynomial.C c) ^ (m.succ - 1) * (polynomial.X - polynomial.C c) ^ 1 := by simp only [pow_one],
  rw triv,
  rw <-pow_add, simp only [mul_one, nat.succ_sub_succ_eq_sub, polynomial.C_add, polynomial.derivative_sub, polynomial.C_1, sub_zero,
 int.coe_nat_succ, polynomial.derivative_X, polynomial.derivative_C, nat.sub_zero], rw <-nat.succ_eq_add_one,
  have triv : (polynomial.C ↑m + 1) * (polynomial.X - polynomial.C c) ^ m.succ + (polynomial.X - polynomial.C c) ^ m.succ
            = (polynomial.C ↑m + 1) * (polynomial.X - polynomial.C c) ^ m.succ + polynomial.C 1 * (polynomial.X - polynomial.C c) ^ m.succ := by simp only [one_mul, polynomial.C_1],
  rw triv, rw <-add_mul, simp only [polynomial.C_1],
end

lemma deriv_X_sub_pow (n k : ℕ) (c : ℤ) (hk : k ≤ n) :
  (deriv_n ((polynomial.X-polynomial.C c)^n) k) = (polynomial.C ((finset.range k).prod (λ i, (n-i:ℤ)))) * ((polynomial.X - polynomial.C c) ^ (n-k)) :=
begin
  induction k with k IH, simp only [zeroth_deriv, one_mul, polynomial.C_1, finset.range_zero, finset.prod_empty, nat.sub_zero],
  {
    rw deriv_n, rw function.iterate_succ_apply', rw <-deriv_n, rw IH, rw polynomial.derivative_mul, simp only [zero_mul, polynomial.derivative_C, zero_add], rw finset.prod_range_succ, simp only [polynomial.C_sub, polynomial.C_mul],
    suffices : ((polynomial.X - polynomial.C c) ^ (n - k)).derivative  = (polynomial.C (n:ℤ) - polynomial.C (k:ℤ)) * (polynomial.X - polynomial.C c) ^ (n - k.succ),
      rw this, ring,
    have triv : (polynomial.C (n:ℤ) - polynomial.C (k:ℤ)) = (polynomial.C (n-k:ℤ)), simp only [polynomial.C_sub], rw deriv1_X_sub_pow, rw triv,
    suffices : polynomial.C ↑(n - k) = polynomial.C (n - k:ℤ),
      rw this, refl,
    ext, rw polynomial.coeff_C, split_ifs, rw h, simp only [polynomial.coeff_C_zero, polynomial.C_sub, polynomial.coeff_sub],
    suffices : int.of_nat (n-k) = ↑n - ↑k, rw <-this, simp only [int.of_nat_eq_coe], apply int.of_nat_sub, exact le_of_lt hk, rw polynomial.coeff_C, simp only [h, if_false], exact le_of_lt hk,
  },
end

lemma deriv_X_sub_pow_too_much (n k : ℕ) (c : ℤ) (hk : n < k) :
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
