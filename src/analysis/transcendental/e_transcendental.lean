import ring_theory.algebraic
import analysis.transcendental.e_transcendental_lemmas
import analysis.transcendental.small_lemmas

noncomputable theory
open small_lemmas e_transcendental_lemmas
open_locale classical
open_locale big_operators
notation α`[X]` := polynomial α

/--
e is defined to be `exp 1`
-/
def e : ℝ := real.exp 1

/--
Definition
For any prime number $p$ and natural number $n$, we can define a polynomial
\[f_{p,n}:=X^{p-1}(X-1)^p\cdots(X-n)^p\]
-/
def f_p (p : ℕ) (n : ℕ): ℤ[X] := polynomial.X ^ (p - 1) * (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p)

/--
Theorem
The degree of $f_{p,n}$ is $(n+1)p-1$
- `polynomial.nat_degree_mul_eq` asserts that the degree of $pq$ is degree of $p$ plus degree of $q$ provided $p$ and $q$ are nonzero
- `prod_deg` asserts that degree of $\prod_{i} p_i$ equals $\sum_i,\mathrm {degree of } p_i$ provided that for all $i,p_i\ne 0$.
-/
lemma deg_f_p (p : ℕ) (hp : nat.prime p) (n : ℕ) : (f_p p n).nat_degree = (n+1)*p - 1 :=
begin
  rw f_p,
  -- So we have degree of `f_p` is degree of $X^{p-1}$ plus degree of $(X-1)^p\cdots(X-n)^p$
  have eq1 := @polynomial.nat_degree_mul ℤ _ _ (polynomial.X ^ (p - 1)) (∏ i in finset.range n, (polynomial.X - (polynomial.C (i+1:ℤ)))^p) _ _,
  { rw eq1,
    simp only [int.cast_coe_nat, mul_one, polynomial.nat_degree_X, int.cast_add, ring_hom.eq_int_cast, int.cast_one, polynomial.nat_degree_pow],
    -- degree of $(X-1)^p\cdots(X-n)^p$ is $p\times$(degree of $(X-1)$+degree of $(X-2)$+...+ degree of $(X-n)$)
    have triv' : (∏ (i : ℕ) in finset.range n, (polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree
                = ∑ i in finset.range n, ((polynomial.X - polynomial.C (i+1:ℤ)) ^ p).nat_degree,
    {
      apply prod_deg,
      intros i hi, intro rid,
      replace rid := @pow_eq_zero (ℤ[X]) _ _ (polynomial.X - polynomial.C (i+1:ℤ)) p rid,
      rw sub_eq_zero at rid,
      have rid' : (polynomial.C (i+1:ℤ)).nat_degree = 1,
      {rw <-rid, exact polynomial.nat_degree_X},
      have rid'' := polynomial.nat_degree_C (i+1:ℤ),
      linarith,
    },
    simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_one, polynomial.nat_degree_pow] at triv',
    rw triv',
    -- each of $(X-i)^p$ has degree p. So The sum of degree is n*p.
    have triv'' : (∑ (i : ℕ) in finset.range n, p * (polynomial.X - (polynomial.C (i + 1:ℤ))).nat_degree) = ∑ x in finset.range n, p,
    {
      apply congr_arg, ext i,
      rw polynomial.nat_degree_X_sub_C, rw mul_one,
    },
    simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, nat.cast_id, finset.sum_const, nsmul_eq_mul, int.cast_one, finset.card_range] at triv'' ⊢,
    rw triv'',
    rw [add_comm, ←nat.add_sub_assoc hp.one_lt.le (n * p), add_mul, one_mul] },

  {intro rid, replace rid := pow_eq_zero rid, exact polynomial.X_ne_zero rid},

  { intro rid, rw finset.prod_eq_zero_iff at rid,
    choose i hi using rid, have hi2 := hi.2, replace hi2 := pow_eq_zero hi2,
    exact not_not.mpr hi2 (polynomial.X_sub_C_ne_zero (↑i + 1))},
end

/--
Definition
For a prime number $p$ and a polynomial $g$
$$J_p(g):= \sum_{i=0}^d g_i I(f_{p,d},i)$$ where $d$ is the degree of $g$.
-/
def J (g : ℤ[X]) (p : ℕ) : ℝ :=
  ∑ i in finset.range g.nat_degree.succ, (g.coeff i : ℝ) * (II (f_p p g.nat_degree) i)

/--
Theorem
$$J_{p}(g) = \sum_{i=0}^d g_i\left(e^i\sum_{j=0}^{(n+1)p-1} f_{p,d}^{(j)}(0)-\sum_{j=0}^{(n+1)p-1}f_{p,d}^{(j)}(i)\right)$
-/
private lemma J_eq1 (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  (J g p) = ∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p g.nat_degree) i) :=
begin
  rw J, apply congr_arg, ext, rw II_eq_I, norm_cast, exact zero_le x,
end


private lemma J_eq2 (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  (∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p g.nat_degree) i)) =
   (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) 0)))
  -(∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) (k:ℝ))))) :=
begin
  rw <-finset.sum_sub_distrib, apply congr_arg, ext i, rw <-mul_sub, rw <-I,
end

private lemma J_eq3 (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0) (p : ℕ) (hp : nat.prime p):
  (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) 0)))) = 0 :=
begin
  have eq1 :
    (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) 0)))) =
    ∑ k in finset.range g.nat_degree.succ, ((g.coeff k:ℝ) * (k:ℝ).exp) * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) 0)),
      apply congr_arg, ext i, ring,
  rw eq1, rw <-finset.sum_mul,
  have eq2 : (∑ x in g.support, (g.coeff x:ℝ) * (x:ℝ).exp) = (∑ (x : ℕ) in finset.range g.nat_degree.succ, (g.coeff x:ℝ) * (x:ℝ).exp),
  {
    apply finset.sum_subset,
    { intros i hi,
      simp only [finset.mem_range],
      suffices : i ≤ g.nat_degree, {exact nat.lt_succ_iff.mpr this},
      apply polynomial.le_nat_degree_of_ne_zero,
      rwa ←polynomial.mem_support_iff },
    { intros i hi Hi, rw mul_eq_zero, left, norm_cast, rwa ←polynomial.not_mem_support_iff, },
  }, rw <-eq2,

  have eq3 : (∑ x in g.support, (g.coeff x:ℝ) * (x:ℝ).exp) = @polynomial.aeval ℤ ℝ _ _ _ e g,
  {
    rw [polynomial.aeval_def, polynomial.eval₂, polynomial.sum], apply congr_arg,
    ext, simp only [ring_hom.eq_int_cast], rw e,
    rw <-real.exp_nat_mul, simp only [mul_one],
  }, rw eq3, rw e_root_g, rw zero_mul,
end

theorem J_eq' (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0)
              (p : ℕ) (hp : nat.prime p) :
  (J g p) = - ∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
                (∑ k in finset.range g.nat_degree.succ,
                  (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) (k:ℝ))) :=
begin
  rw [J_eq1, J_eq2, J_eq3, finset.sum_comm], simp only [zero_sub, neg_inj],
  apply congr_arg, ext, rw finset.mul_sum,
  exact e_root_g, exact hp, exact hp, exact hp,
end

private lemma f_eval_on_ℝ_nat (f : ℤ[X]) (k : ℕ) : (f_eval_on_ℝ f (k:ℝ)) = ℤembℝ (polynomial.eval k f) :=
begin
  simp only [f_eval_on_ℝ], rw polynomial.eval_map, rw polynomial.eval₂, rw polynomial.sum,
  rw polynomial.eval,
  rw polynomial.eval₂, rw polynomial.sum, simp only [ring_hom.id_apply], rw ring_hom.map_sum,
  apply congr_arg, ext n, simp only [int.cast_coe_nat, int.cast_pow, ring_hom.eq_int_cast, int.cast_mul],
end

lemma coe_J (g : ℤ[X]) (p : ℕ) :
    ∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
      (∑ k in finset.range g.nat_degree.succ,
        (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) (k:ℝ))) =
    ℤembℝ (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
            (∑ k in finset.range g.nat_degree.succ,
              (g.coeff k) * (polynomial.eval (k:ℤ) (deriv_n (f_p p g.nat_degree) j)))) :=
begin
  rw ring_hom.map_sum, apply finset.sum_congr, exact rfl,
  intros i hi, rw ring_hom.map_sum, apply finset.sum_congr, refl,
  intros j hj, rw ring_hom.map_mul, simp only [ring_hom.eq_int_cast], apply mul_eq_mul', exact rfl, rw f_eval_on_ℝ_nat, simp only [ring_hom.eq_int_cast],
end

theorem J_eq'' (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0)
              (p : ℕ) (hp : nat.prime p) :
  (J g p) =  - ℤembℝ (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
            (∑ k in finset.range g.nat_degree.succ,
              (g.coeff k) * (polynomial.eval (k:ℤ) (deriv_n (f_p p g.nat_degree) j)))) :=
begin
  rw J_eq', rw neg_eq_iff_neg_eq, rw neg_neg, rw <-coe_J, exact e_root_g, exact hp,
end

theorem deriv_n_C_mul (c : ℤ) (n : ℕ) : ∀ f : ℤ[X], (deriv_n (polynomial.C c * f) n) = (polynomial.C c) * (deriv_n f n) :=
begin
  induction n with n IH, simp only [zeroth_deriv, forall_const, eq_self_iff_true],
  intro f,
  rw deriv_n, rw function.iterate_succ, simp only [polynomial.derivative_mul, zero_mul, function.comp_app, polynomial.derivative_C, zero_add], rw <-deriv_n, rw IH, refl,
end

theorem dvd_poly_pow_deriv (f : ℤ[X]) (n m : ℕ) (c : ℤ) (hn : 0 < n) (hm : 0 < m) : (n:ℤ) ∣ polynomial.eval c (deriv_n (f^n) m) :=
begin
    cases m, linarith,

    rw [deriv_n, function.iterate_succ], simp only [function.comp_app], rw [<-deriv_n], rw poly_pow_deriv,
    have triv : polynomial.C ↑n * f ^ (n - 1) * f.derivative = polynomial.C ↑n * (f ^ (n - 1) * f.derivative) := by ring,
    rw triv,
    rw deriv_n_C_mul, rw polynomial.eval_mul, simp only [polynomial.eval_C, dvd_mul_right], assumption,
end


private lemma succ_pred (a b : ℕ) (h : a.succ = b) : a = b.pred :=
begin
  rw <-h, simp only [nat.pred_succ],
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

  { rw nat.sub_succ at h_1, rw <-nat.succ_eq_add_one at h, exfalso,
    exact h_1 (succ_pred i (n-k) h) },

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

lemma deriv_f_p_k_eq_zero_k_eq_0_when_j_lt_p_sub_one (p : ℕ) (n j : ℕ) (hj : j < p - 1):
  polynomial.eval 0 (deriv_n (f_p p n) j) = 0 :=
begin
  rw [f_p, deriv_n_poly_prod, eval_sum'],
  apply finset.sum_eq_zero, intros i hi, rw polynomial.eval_mul,
  simp only [nat.succ_pos', finset.mem_range] at hi,
  rw [mul_eq_zero], left,
  have ineq : j - i < p - 1 := gt_of_gt_of_ge hj (nat.sub_le j i),
  rw [polynomial.eval_mul, mul_eq_zero], right,
  rw [deriv_X_pow', polynomial.eval_mul], simp only [polynomial.eval_X, polynomial.eval_C, int.coe_nat_zero, polynomial.eval_pow, mul_eq_zero], right, apply zero_pow,
  exact nat.sub_pos_of_lt ineq,
  exact le_of_lt ineq,
end

lemma fact_eq_prod (n : ℕ) : (n.factorial:ℤ) = ∏ i in finset.range n, (i+1:ℤ) :=
begin
  induction n with n ih,
  { simp only [int.coe_nat_zero, int.coe_nat_succ, finset.range_zero, finset.prod_empty,
      zero_add, nat.factorial_zero] },
  rw [nat.factorial_succ, finset.prod_range_succ], simp only [int.coe_nat_succ, int.coe_nat_mul],
  rw [ih, mul_comm],
end

lemma fact_eq_prod' (n : ℕ) : (n.factorial:ℤ) = ∏ i in finset.range n, (n-i:ℤ) :=
begin
  induction n with n ih,
  { simp only [int.coe_nat_zero, int.coe_nat_succ, finset.range_zero, finset.prod_empty, zero_add,
      nat.factorial_zero] },
  rw [nat.factorial_succ, finset.prod_range_succ'],
  simp only [int.coe_nat_zero, add_sub_add_right_eq_sub, sub_zero, int.coe_nat_succ, nat.factorial,
    int.coe_nat_mul],
  rw ih, rw mul_comm,
end

theorem deriv_f_p_zero_when_j_eq_p_sub_one (p : ℕ) (hp : nat.prime p) (n : ℕ) :
  polynomial.eval 0 (deriv_n (f_p p n) (p-1)) = (p-1).factorial * (-1)^(n*p)*(n.factorial)^p :=
begin
  rw [f_p, deriv_n_poly_prod, eval_sum'],
  rw finset.sum_eq_single 0,
  { simp only [nat.choose_self, int.cast_add, one_mul, int.coe_nat_zero, polynomial.eval_mul,
      int.coe_nat_succ, zero_add, nat.factorial, zeroth_deriv, int.cast_coe_nat,
      ring_hom.eq_int_cast, nat.choose_zero_right, deriv_X_pow, eval_prod', polynomial.eval_X,
      mul_one, algebra.id.smul_eq_mul, zero_sub, nat.sub_self, polynomial.eval_one,
      polynomial.eval_pow, int.cast_one, polynomial.eval_smul, polynomial.eval_nat_cast,
      nat.sub_zero, polynomial.eval_add, neg_add_rev, polynomial.eval_sub, pow_zero],

    rw fact_eq_prod', rw mul_assoc, apply congr_arg,
    rw fact_eq_prod, rw pow_mul, rw <-mul_pow, simp_rw <-neg_add,

    have rhs : ((-1:ℤ) ^ n * ∏ (i : ℕ) in finset.range n, (↑i + 1)) = (∏ (i : ℕ) in finset.range n, (-1) * (↑i + 1)),
    {rw finset.prod_mul_distrib, rw finset.prod_const, rw [finset.card_range]},
    rw rhs, rw finset.prod_pow, congr' 1, apply finset.prod_congr rfl, rintro x -,
    rw neg_one_mul, rw add_comm },

  { intros i hi1 hi2,
    simp only [polynomial.eval_mul, int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast,
      int.coe_nat_eq_zero, int.cast_one, polynomial.eval_mul, polynomial.eval_nat_cast],
    apply mul_eq_zero_of_left,
    apply mul_eq_zero_of_right,
    rw [deriv_X_pow _ _ (nat.sub_le _ _), polynomial.eval_smul, polynomial.eval_pow,
      polynomial.eval_X, algebra.id.smul_eq_mul],
    apply mul_eq_zero_of_right,
    apply zero_pow,

    apply nat.sub_pos_of_lt, apply nat.sub_lt,
    { apply nat.sub_pos_of_lt, exact nat.prime.one_lt hp },
    { exact nat.pos_of_ne_zero hi2 } },
  { intro rid, exfalso, simp only [nat.succ_pos', not_true, finset.mem_range] at rid, exact rid },
end

theorem f_p_n_succ (p : ℕ) (n : ℕ) : (f_p p n.succ) = (f_p p n) * (polynomial.X- polynomial.C (n+1:ℤ))^p :=
begin
  rw f_p, rw f_p, rw finset.prod_range_succ, ring,
end

lemma deriv_f_p_when_j_lt_p (p : ℕ) (n : ℕ) : ∀ x : ℕ, ∀ j : ℕ, j < p ->
  0 < x -> x < n.succ -> polynomial.eval (x:ℤ) (deriv_n (f_p p n) j) = 0 :=
begin
  induction n with n IH,
  intros x j hj hx1 hx2,
  linarith,
  {
    intros x j hj hx1 hx2,
    rw [f_p_n_succ, deriv_n_poly_prod, eval_sum'], apply finset.sum_eq_zero, intros y hy, simp only [finset.mem_range] at hy,
    rw polynomial.eval_mul, rw polynomial.eval_mul, rw polynomial.eval_C,
    replace hx2 : x < n.succ ∨ x = n.succ, exact nat.lt_succ_iff_lt_or_eq.mp hx2,
    cases hx2,
      simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, gt_iff_lt, int.coe_nat_eq_zero, int.cast_one, mul_eq_zero] at *,
      rw IH x (j-y) (gt_of_gt_of_ge hj (nat.sub_le j y)) hx1 hx2, tauto,
    {
      -- x = n.succ
      rw mul_eq_zero, right, rw [hx2, deriv_X_sub_pow, polynomial.eval_mul, polynomial.eval_pow],
      simp only [polynomial.eval_X, polynomial.eval_C, int.coe_nat_succ, polynomial.eval_sub, sub_self, mul_eq_zero],
      right, apply zero_pow (nat.sub_pos_of_lt (gt_of_ge_of_gt hj hy)),
      exact le_of_lt (gt_of_ge_of_gt hj hy),
    },
  },
end

theorem deriv_f_p_k_eq_zero_when_j_lt_p_sub_one (p : ℕ) (n j : ℕ) (hj : j < p - 1) (k : ℕ) (hk : k ∈ finset.range n.succ):
  polynomial.eval (k:ℤ) (deriv_n (f_p p n) j) = 0 :=
begin
  cases k, exact deriv_f_p_k_eq_zero_k_eq_0_when_j_lt_p_sub_one p n j hj,
  apply deriv_f_p_when_j_lt_p p n k.succ j (nat.lt_of_lt_pred hj) (nat.succ_pos k) (finset.mem_range.mp hk),
end

lemma dvd_iff_mul (m n : ℤ) : n ∣ m ↔ ∃ c : ℤ, m = n * c := iff.rfl
lemma dvd_iff_mul_nat (m n : ℕ) : n ∣ m ↔ ∃ c : ℕ, m = n * c := iff.rfl

private lemma k_eq_0_case_when_j_ge_p (p : ℕ) (hp : nat.prime p) (n:ℕ) :
  ∀ j : ℕ, p ≤ j -> (p.factorial:ℤ) ∣ polynomial.eval 0 (deriv_n (f_p p n) j) :=
begin
  rw f_p, intros j j_ge_p, rw [deriv_n_poly_prod, eval_sum'], apply finset.dvd_sum,
  intros x hx,
  simp only [polynomial.eval_C, polynomial.C_add, polynomial.C_1, polynomial.eval_mul, nat.factorial],
  by_cases j - x = p - 1,
  {
    rw h, rw deriv_X_pow', simp only [mul_one, polynomial.eval_C, nat.sub_self, pow_zero],
    rw <-fact_eq_prod',
    suffices : (p:ℤ) ∣ polynomial.eval 0 (deriv_n (∏ (x : ℕ) in finset.range n, (polynomial.X - (polynomial.C ↑x + 1)) ^ p) x),
    {
      rw dvd_iff_mul at this, choose c hc using this, rw hc,
      have triv : ↑(j.choose x) * ↑((p - 1).factorial) * (↑p * c)
        = ↑(j.choose x) * (↑((p - 1).factorial) * ↑p) * c := by ring,
      rw triv,
      replace triv : ((p - 1).factorial:ℤ) * ↑p = (p.factorial:ℤ),
      { have triv' : p = (p-1).succ,
        { rw nat.sub_one, apply eq.symm, apply nat.succ_pred_eq_of_pos, exact nat.prime.pos hp },
        conv_rhs {rw triv'}, rw [nat.factorial_succ, ←nat.succ_eq_add_one, <-triv', mul_comm],
        norm_cast },
      rw triv,
      replace triv : ↑(j.choose x) * ↑(p.factorial) * c = ↑(p.factorial) * (↑(j.choose x) * c) := by ring,
      rw triv,
      exact dvd.intro (↑(nat.choose j x) * c) rfl,
    },
    cases x,
      simp only [nat.sub_zero] at h, rw h at j_ge_p,
      have this := @nat.sub_one_sub_lt p 0 (nat.prime.pos hp), simp only [nat.sub_zero] at this, linarith,

      rw finset.prod_pow, apply dvd_poly_pow_deriv, exact nat.prime.pos hp, exact nat.succ_pos x,
    exact le_refl (p - 1),
  },
  replace h : j - x < p - 1 ∨ j - x > p - 1, exact lt_or_gt_of_ne h,
  cases h,
    rw (deriv_X_pow' (p-1) (j-x) (le_of_lt h)), rw polynomial.eval_mul, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow], rw (zero_pow (nat.sub_pos_of_lt h)), simp only [zero_mul, mul_zero, dvd_zero],
    rw deriv_X_pow_too_much, simp only [zero_mul, mul_zero, polynomial.eval_zero, dvd_zero], assumption,
end

private lemma p_fact_dvd_prod_part (n : ℕ) :  ∀ j : ℕ, ∀ k : ℕ, ∀ p : ℕ, p > 0 ->
  k > 0 -> k < n.succ ->
  (p.factorial:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (∏ i in finset.range n, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j) :=
begin
  intros j,
  apply nat.case_strong_induction_on j,
  { intros k p hp hk1 hk2,
    rw zeroth_deriv,
    simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_one, nat.factorial],
    suffices : polynomial.eval (k:ℤ) (∏ (i : ℕ) in finset.range n, (polynomial.X - (↑i + 1)) ^ p) = 0,
    {rw this, exact dvd_zero _},
    rw eval_prod', rw finset.prod_eq_zero_iff, use k.pred,
    split,
    { simp only [finset.mem_range], rw nat.lt_succ_iff at hk2,
      have hk3 : k.pred < k := nat.pred_lt (ne_of_gt hk1),
      exact gt_of_ge_of_gt hk2 hk3 },
    { simp only [polynomial.eval_X, polynomial.eval_one, polynomial.eval_pow,
        polynomial.eval_nat_cast, polynomial.eval_add, polynomial.eval_sub],
      suffices : (k - (↑(k.pred) + 1):ℤ) = 0,
      {rw this,  apply zero_pow, exact hp},
      rw sub_eq_zero, norm_cast, exact (nat.succ_pred_eq_of_pos hk1).symm } },


  intros j IH k p hp hk1 hk2,
  rw [deriv_n, function.iterate_succ_apply, <-deriv_n, finset.prod_pow, poly_pow_deriv _ _ hp,
    deriv_n_poly_prod, eval_sum'],
  apply finset.dvd_sum,
  intros x hx,
  obtain rfl|h := (nat.succ_le_iff.mpr hp).eq_or_lt,
  { norm_num },

  replace IH := IH (j-x) (nat.sub_le j x) k (p-1) (nat.sub_pos_of_lt h) hk1 hk2,
  have eq : p-1+1=p,
  {apply nat.sub_add_cancel, exact le_of_lt h},
  replace eq : p.factorial = (p-1).factorial * p,
  { conv_lhs {rw <-eq}, rw [nat.factorial_succ, nat.sub_add_cancel], ring,
    exact hp },
  rw [polynomial.eval_mul],
  apply dvd_mul_of_dvd_left,
  rw [polynomial.eval_mul],
  apply dvd_mul_of_dvd_right,
  rw deriv_n_C_mul, rw [polynomial.eval_mul, polynomial.eval_C],
  rw eq, conv_lhs {rw mul_comm},
  simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_one, int.coe_nat_mul],
  apply mul_dvd_mul, refl,
  simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_one, nat.factorial] at IH ⊢,
  norm_cast at IH ⊢,
  rw finset.prod_pow at IH, exact IH,
end

private lemma k_ge_1_case_when_j_ge_p (p : ℕ) (hp : nat.prime p) (n:ℕ) :
  ∀ j : ℕ, p ≤ j ->
    ∀ k : ℕ, k < n.succ -> k > 0 -> (p.factorial:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (f_p p n) j) :=
begin
  intros j hj k hk1 hk2,
  rw f_p, rw deriv_n_poly_prod, rw eval_sum', apply finset.dvd_sum, intros x hx,
  rw polynomial.eval_mul, rw polynomial.eval_mul,
  apply dvd_mul_of_dvd_right,
  apply p_fact_dvd_prod_part n _ _ _ (nat.prime.pos hp) hk2 hk1,
end

theorem when_j_ge_p_k (p : ℕ) (hp : nat.prime p) (n:ℕ) :
  ∀ j : ℕ, p ≤ j ->
    ∀ k : ℕ, k ∈ finset.range n.succ ->
      (p.factorial:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (f_p p n) j) :=
begin
  intros j j_ge_p k hk,
  simp only [finset.mem_range] at hk,
  cases k,
    exact k_eq_0_case_when_j_ge_p p hp n j j_ge_p,
    exact k_ge_1_case_when_j_ge_p p hp n j j_ge_p k.succ hk (nat.succ_pos k),
end


private lemma p_sub_one_le (p m : ℕ) (hp : nat.prime p) : p - 1 ≤ m.succ * p - 1 :=
begin
  induction m with m IH, simp only [one_mul], rw nat.succ_eq_add_one, rw add_mul, simp only [one_mul],
  suffices : m.succ * p - 1 ≤ m.succ * p + p - 1, exact le_trans IH this,
  have triv : m.succ * p + p - 1 = m.succ * p - 1 + p,
    rw nat.sub_add_comm, apply nat.mul_pos, exact nat.succ_pos m, exact nat.prime.pos hp,
  rw triv, suffices : p ≥ 0, exact nat.le.intro rfl, exact bot_le,
end

theorem J_partial_sum_from_one_to_p_sub_one (g : ℤ[X])
             (p : ℕ) :
  ∑ (j : ℕ) in finset.range (p - 1),
  ∑ (k : ℕ) in finset.range g.nat_degree.succ,
    g.coeff k * polynomial.eval ↑k (deriv_n (f_p p g.nat_degree) j) = 0 :=
begin
  rw finset.sum_eq_zero, intros, rw finset.sum_eq_zero, intros,
  rw mul_eq_zero, right, rw deriv_f_p_k_eq_zero_when_j_lt_p_sub_one, simp only [finset.mem_range] at H,
  exact H,
  exact H_1,
end

theorem J_partial_sum_from_p_sub_one_to_p (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
   ∑ (k : ℕ) in finset.range g.nat_degree.succ, g.coeff k * polynomial.eval ↑k (deriv_n (f_p p g.nat_degree) (p - 1)) =
   g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.factorial) ^ p) :=
begin
  rw finset.sum_eq_single 0,

  simp only [int.coe_nat_zero],
  rw deriv_f_p_zero_when_j_eq_p_sub_one p hp g.nat_degree,

  intros i hi1 hi2, rw mul_eq_zero, right,
  apply deriv_f_p_when_j_lt_p p g.nat_degree,
  apply nat.sub_lt (nat.prime.pos hp), exact nat.one_pos, exact nat.pos_of_ne_zero hi2,
  exact finset.mem_range.mp hi1, intro rid, exfalso, simp only [nat.succ_pos', not_true, finset.mem_range] at rid, exact rid,
end

theorem J_partial_sum_rest (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  (p.factorial:ℤ) ∣
    ∑ (j : ℕ) in finset.Ico p (f_p p g.nat_degree).nat_degree.succ,
    ∑ (k : ℕ) in finset.range g.nat_degree.succ, g.coeff k * polynomial.eval (k:ℤ) (deriv_n (f_p p g.nat_degree) j) :=
begin
  apply finset.dvd_sum, intros x hx, apply finset.dvd_sum, intros y hy,
  apply dvd_mul_of_dvd_right,
  apply when_j_ge_p_k _ hp _ _ _ _ hy,
  simp only [finset.mem_Ico] at hx, exact hx.1,
end

theorem J_eq_final (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0) (p : ℕ) (hp : nat.prime p) :
  ∃ M : ℤ, (J g p) = ℤembℝ ((-(g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.factorial) ^ p))) + (p.factorial:ℤ) * M) :=
begin
  have J_eq := J_eq'' g e_root_g p hp, rw J_eq, rw <-ring_hom.map_neg,
  have seteq : finset.range (f_p p g.nat_degree).nat_degree.succ = finset.range (p-1) ∪ {p-1} ∪ finset.Ico p (f_p p g.nat_degree).nat_degree.succ,
  {
    ext, split,
    {
      intros ha, simp only [finset.mem_range] at ha,
      by_cases (a < p - 1),
      { simp only [finset.mem_Ico, finset.mem_union, finset.union_assoc, finset.mem_singleton,
          finset.mem_range],
        left, exact h },
      { replace h : a ≥ p - 1, exact not_lt.mp h,
        replace h : p - 1 = a ∨ a > p - 1, exact eq_or_lt_of_le h,
        simp only [finset.mem_Ico, finset.mem_union, finset.union_assoc, finset.mem_singleton,
          finset.mem_range],
        cases h,
        { right, left, exact eq.symm h },
        { right, right, split, exact nat.le_of_pred_lt h, assumption } },
    },
    {
      intros ha,
      simp only [finset.mem_Ico, finset.mem_union, finset.union_assoc, finset.mem_singleton,
        finset.mem_range] at ha ⊢,
      cases ha,
      { have triv : p - 1 ≤ (f_p p g.nat_degree).nat_degree,
        {rw deg_f_p _ hp, apply p_sub_one_le _ _  hp},
        have ineq := lt_of_lt_of_le ha triv,
        exact nat.lt.step ineq },
      { cases ha,
        { rw ha,
          have triv : p - 1 ≤ (f_p p g.nat_degree).nat_degree,
          { rw deg_f_p _ hp, apply p_sub_one_le _ _ hp },
          exact nat.lt_succ_iff.mpr triv},
        {exact ha.2} } },
  },
  rw seteq, rw finset.sum_union, rw finset.sum_union,
  rw J_partial_sum_from_one_to_p_sub_one g, rw zero_add, rw finset.sum_singleton,
  rw J_partial_sum_from_p_sub_one_to_p g,

  have H3 := J_partial_sum_rest g p hp,
  rw dvd_iff_mul at H3,
  choose c eq3 using H3, rw eq3, rw neg_add, use -c, rw neg_mul_eq_mul_neg ↑(p.factorial), exact hp,

  rw finset.disjoint_iff_inter_eq_empty, simp only [finset.not_mem_range_self, not_false_iff, finset.inter_singleton_of_not_mem],
  {
    rw finset.disjoint_iff_inter_eq_empty, rw finset.eq_empty_iff_forall_not_mem, intros, intro rid,
    simp only [finset.mem_Ico, finset.mem_union, finset.mem_singleton, finset.mem_range,
      finset.mem_inter] at rid,
    have h1 := rid.1, have h2 := rid.2.1, have h3 := rid.2.2, cases h1,
      have contra : p < p - 1, exact gt_of_gt_of_ge h1 h2,
      replace contra : ¬ (p ≥  p - 1), exact not_le.mpr contra, have triv : p ≥ p - 1, exact nat.sub_le p 1, exact contra triv,

    rw h1 at h2,
    have triv : p > p - 1, have rid := @nat.sub_one_sub_lt p 0 (nat.prime.pos hp), simp only [nat.sub_zero] at rid, exact rid, have rid : p < p,
    exact gt_of_gt_of_ge triv h2, exact lt_irrefl p rid,
  },
end

private lemma coe_abs_ineq (z1 z2 : ℤ) : z1 ≤ abs z2 -> (z1:ℝ) ≤ abs(ℤembℝ z2) :=
begin
  simp only [ring_hom.eq_int_cast], norm_cast, exact id,
end

theorem abs_J_lower_bound (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0)
  (coeff_nonzero : (g.coeff 0) ≠ 0) (p : ℕ) (hp : nat.prime p)
  (hp2 : g.nat_degree < p  ∧ (g.coeff 0).nat_abs < p) :
  ((p-1).factorial:ℝ) ≤ (abs (J g p)) :=
begin
  have J_eq := J_eq_final g e_root_g p hp,
  choose c eq1 using J_eq, rw eq1,
  have H := coe_abs_ineq ((p-1).factorial:ℤ) (-(g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.factorial) ^ p)) + ↑(p.factorial) * c) _,
  { conv_lhs at H {simp only [int.cast_coe_nat, int.cast_pow, int.cast_add, ring_hom.eq_int_cast, int.cast_mul, int.cast_one, ne.def, triv, not_false_iff, neg_eq_zero, one_ne_zero, int.cast_neg, int.coe_nat_mul],},
    exact H },

  norm_cast,
  have triv : p = (p-1).succ,
  {rw nat.sub_one, rw nat.succ_pred_eq_of_pos, exact nat.prime.pos hp},
  replace triv : p.factorial = (p-1).factorial * p,
  { conv_lhs {rw triv,}, rw [nat.factorial_succ, ←nat.succ_eq_add_one], rw <-triv, rw mul_comm },

  rw neg_mul_eq_mul_neg, rw neg_mul_eq_mul_neg,
  have eq2 : (g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) +
         ↑p.factorial * c) =
         ((p - 1).factorial:ℤ) * ((g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p))) + (↑p*c)),
  { rw mul_add,
    have triv1 : g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) = ↑((p - 1).factorial) * (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p))) := by ring,
    rw triv1,
    congr' 1,
    replace triv1 : ↑p.factorial * c = ↑((p - 1).factorial) * (↑p * c),
    { rw ←nat.mul_factorial_pred hp.pos,
      simp only [int.coe_nat_mul], ring},
    rw triv1 },
  rw eq2, rw abs_mul,
  have triv : abs ↑((p - 1).factorial) = ((p-1).factorial:ℤ),
  {apply abs_of_pos, norm_cast, exact (p - 1).factorial_pos},
  rw triv,
  suffices : 1 ≤ abs (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) + ↑p * c),
  { have triv : ((p - 1).factorial:ℤ) = ↑((p - 1).factorial) * 1 := (mul_one _).symm,
    conv_lhs {rw triv,}, apply mul_le_mul le_rfl this zero_le_one,
    norm_cast, exact bot_le },

  change 0 < abs (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) + ↑p * c),
  rw abs_pos, intro rid,
  have rid2 : (p:ℤ) ∣ g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) + ↑p * c,
  rw rid, exact dvd_zero ↑p,

  replace rid2 : (p:ℤ) ∣ g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)),
    refine (dvd_add_iff_left _).2 rid2, exact dvd.intro c rfl,
  have triv : (-1:ℤ) ^ (g.nat_degree * p) = 1 ∨ (-1:ℤ) ^ (g.nat_degree * p) = -1 := neg_one_pow_eq_or _ _,
  cases triv,
  {
    rw triv_1 at rid2, simp only [one_mul, int.coe_nat_pow, dvd_neg, int.mul_neg_eq_neg_mul_symm] at rid2,
    replace rid2 := int.dvd_nat_abs_of_of_nat_dvd rid2,
    rw int.nat_abs_mul at rid2,
    rw nat.prime.dvd_mul at rid2,
    cases rid2,
    {
      have ineq1 : (g.coeff 0).nat_abs > 0 := int.nat_abs_pos_of_ne_zero coeff_nonzero,
      rw dvd_iff_mul_nat at rid2, choose m hm using rid2,
      cases m, rw mul_zero at hm, linarith,
        have ineq2 : p * m.succ ≥ p, exact nat.le_add_left p (nat.mul p m), rw <-hm at ineq2,
        have contra : ¬(p > (g.coeff 0).nat_abs), exact not_lt.mpr ineq2, exact contra hp2.2,
    },
    {
      rw int.nat_abs_pow at rid2,
      have H := nat.prime.dvd_of_dvd_pow hp rid2,
      have eq1 : (g.nat_degree.factorial:ℤ).nat_abs = g.nat_degree.factorial,
      {
        suffices : ((g.nat_degree.factorial:ℤ).nat_abs:ℤ)= (g.nat_degree.factorial:ℤ), norm_cast, rw <-int.abs_eq_nat_abs,
        rw abs_of_pos, norm_cast, exact (polynomial.nat_degree g).factorial_pos,
      }, rw eq1 at H,
      rw nat.prime.dvd_factorial at H,
      replace H : ¬(p > g.nat_degree), exact not_lt.mpr H, exact H hp2.1, exact hp,
    },
    exact hp,
  },
  {
    rw triv_1 at rid2, simp only [int.neg_mul_eq_neg_mul_symm, one_mul, int.coe_nat_pow, neg_neg] at rid2,
    replace rid2 := int.dvd_nat_abs_of_of_nat_dvd rid2,
    rw int.nat_abs_mul at rid2,
    rw nat.prime.dvd_mul at rid2,
    cases rid2,
    {
      have ineq1 : (g.coeff 0).nat_abs > 0 := int.nat_abs_pos_of_ne_zero coeff_nonzero,
      rw dvd_iff_mul_nat at rid2, choose m hm using rid2,
      cases m, rw mul_zero at hm, linarith,
      have ineq2 : p * m.succ ≥ p, exact nat.le_add_left p (nat.mul p m), rw <-hm at ineq2,
      have contra : ¬(p > (g.coeff 0).nat_abs), exact not_lt.mpr ineq2, exact contra hp2.2,
    },
    {
      rw int.nat_abs_pow at rid2,
      have H := nat.prime.dvd_of_dvd_pow hp rid2,
      have eq1 : (g.nat_degree.factorial:ℤ).nat_abs = g.nat_degree.factorial,
      {
        suffices : ((g.nat_degree.factorial:ℤ).nat_abs:ℤ)= (g.nat_degree.factorial:ℤ), norm_cast, rw <-int.abs_eq_nat_abs,
        rw abs_of_pos, norm_cast, exact (polynomial.nat_degree g).factorial_pos,
      }, rw eq1 at H,
      rw nat.prime.dvd_factorial at H,
      replace H : ¬(p > g.nat_degree), exact not_lt.mpr H, exact H hp2.1, exact hp,
    },
    exact hp,
  },
end


lemma abs_sum_le_sum_abs' {f : (ℕ×ℕ) → ℤ} {s : finset (ℕ×ℕ)} :
  abs (∑ x in s, f x) ≤ ∑ x in s, abs (f x) :=
begin
  apply finset.induction_on s,
  { simp },
    intros a s ha H,
    rw finset.sum_insert, rw finset.sum_insert,
    have triv := @abs_add ℤ _ (f a) (∑ (x : ℕ × ℕ) in s, f x),
    have triv2 : abs (f a) + abs (∑ (x : ℕ × ℕ) in s, f x) ≤ abs (f a) + (∑ (x : ℕ × ℕ) in s, abs (f x)), exact add_le_add_left H (abs (f a)),
    exact le_trans triv triv2, assumption, assumption,
end

theorem eval_f_bar_mul (f g : ℤ[X]) (k : ℕ) : polynomial.eval (k:ℤ) (f_bar (f * g)) ≤ (polynomial.eval (k:ℤ) (f_bar f)) * (polynomial.eval (k:ℤ) (f_bar g)) :=
begin
  by_cases (f=0 ∨ g=0),
  { cases h, rw h, simp only [f_bar_0, zero_mul, polynomial.eval_zero], rw h, simp only [f_bar_0, mul_zero, polynomial.eval_zero] },
  replace h := not_or_distrib.1 h,
  rw polynomial.as_sum_range (f_bar (f*g)), rw eval_sum', rw bar_same_deg, rw <-polynomial.eval_mul,
  rw polynomial.as_sum_range ((f_bar f)*(f_bar g)),
  have deg_eq : (f_bar f * f_bar g).nat_degree = f.nat_degree + g.nat_degree,
  { rw polynomial.nat_degree_mul, rw bar_same_deg, rw bar_same_deg, intro rid, exact h.1 (f_bar_eq_0 f rid), intro rid, exact h.2 (f_bar_eq_0 g rid) },
  rw deg_eq,
  replace deg_eq : (f * g).nat_degree = f.nat_degree + g.nat_degree,
  { rw polynomial.nat_degree_mul, intro rid, exact h.1 rid, intro rid, exact h.2 rid },
  rw deg_eq, rw eval_sum', apply finset.sum_le_sum,
  intros x hx, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow, polynomial.eval_mul], rw coeff_f_bar_mul, rw polynomial.coeff_mul,
  cases k,
  { cases x,
    { simp only [mul_one, finset.nat.antidiagonal_zero, finset.sum_singleton, pow_zero],
      rw bar_coeff, rw bar_coeff, rw abs_mul },
    { simp only [int.coe_nat_zero, polynomial.eval_monomial, linear_map.map_sum, mul_zero,
        zero_pow (nat.succ_pos x), polynomial.eval_finset_sum],
      exact finset.sum_nonneg (λ i hi, le_rfl), } },

   { have ineq : abs (∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, f.coeff p.fst * g.coeff p.snd) ≤
              ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, abs(f.coeff p.fst * g.coeff p.snd) := abs_sum_le_sum_abs',
    have triv : ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, abs(f.coeff p.fst * g.coeff p.snd) = ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x, abs(f.coeff p.fst) * abs(g.coeff p.snd),
    { apply congr_arg, ext, rw abs_mul },
    rw triv at ineq,
    simp only [polynomial.eval_monomial],
    apply mul_le_mul ineq le_rfl,
    { apply pow_nonneg, norm_cast, exact bot_le },
    { apply finset.sum_nonneg, intros, rw <-abs_mul, exact abs_nonneg _ } }
end

lemma f_bar_1 : f_bar 1 = 1 :=
begin
  ext, simp only [bar_coeff, polynomial.coeff_one], split_ifs, exact rfl, exact rfl,
end


lemma eval_f_bar_nonneg (f : ℤ[X]) (i:ℕ) : 0 ≤ polynomial.eval (i:ℤ) (f_bar f) :=
begin
  rw [f_bar_eq, eval_sum'],
  apply finset.sum_nonneg,
  intros x hx,
  simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow, polynomial.eval_mul],
  exact mul_nonneg (abs_nonneg (polynomial.coeff f x)) (pow_nonneg (int.coe_nat_nonneg _) _),
end

theorem eval_f_bar_pow (f : ℤ[X]) (k n : ℕ) : polynomial.eval (k:ℤ) (f_bar (f^n)) ≤ (polynomial.eval (k:ℤ) (f_bar f))^n :=
begin
  induction n with n H,
  simp only [f_bar_1, polynomial.eval_one, pow_zero],
  rw pow_succ, have ineq := eval_f_bar_mul f (f^n) k,
  have ineq2 : polynomial.eval ↑k (f_bar f) * polynomial.eval ↑k (f_bar (f ^ n)) ≤  polynomial.eval ↑k (f_bar f) * polynomial.eval ↑k (f_bar f) ^ n,
    apply mul_le_mul, exact le_refl (polynomial.eval ↑k (f_bar f)), exact H, exact eval_f_bar_nonneg (f ^ n) k, exact eval_f_bar_nonneg f k,
  exact le_trans ineq ineq2,
end

theorem eval_f_bar_prod (f : ℕ -> (ℤ[X])) (k : ℕ) (s:finset ℕ): polynomial.eval (k:ℤ) (f_bar (∏ i in s, (f i))) ≤ (∏ i in s, polynomial.eval (k:ℤ) (f_bar (f i))) :=
begin
  apply finset.induction_on s, simp only [f_bar_1, polynomial.eval_one, finset.prod_empty],
  intros a s ha H, rw finset.prod_insert, rw finset.prod_insert,
  have ineq := eval_f_bar_mul (f a) (∏ (x : ℕ) in s, f x) k,
  have ineq2 : polynomial.eval ↑k (f_bar (f a)) * polynomial.eval ↑k (f_bar (∏ (x : ℕ) in s, f x)) ≤
    polynomial.eval ↑k (f_bar (f a)) * ∏ (i : ℕ) in s, polynomial.eval ↑k (f_bar (f i)),
  apply mul_le_mul, exact le_refl _, exact H, exact eval_f_bar_nonneg (∏ (x : ℕ) in s, f x) k, exact eval_f_bar_nonneg (f a) k,
  exact le_trans ineq ineq2, exact ha, exact ha,
end


theorem abs_J_ineq1' (g : ℤ[X]) (p : ℕ) :
  abs (J g p) ≤ ∑ i in finset.range g.nat_degree.succ, (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * (f_eval_on_ℝ (f_bar (f_p p g.nat_degree)) (i:ℝ)) :=
begin
  have ineq1 : abs (J g p) ≤ (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ) * (II (f_p p g.nat_degree) i))) := finset.abs_sum_le_sum_abs _ _,
  have triv :
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ) * (II (f_p p g.nat_degree) i))) =
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ)) * abs((II (f_p p g.nat_degree) i))),
    apply finset.sum_congr, refl, intros, rw abs_mul,
  rw triv at ineq1,
  have ineq2:
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ)) * abs((II (f_p p g.nat_degree) i))) ≤
    (∑ i in finset.range g.nat_degree.succ, abs ((g.coeff i : ℝ)) * (i:ℝ)*(i:ℝ).exp * (f_eval_on_ℝ (f_bar (f_p p g.nat_degree)) (i:ℝ))),
  {
    apply finset.sum_le_sum, intros x hx, replace triv : (x:ℝ) ≥ 0, {norm_cast, exact bot_le,},
    have ineq3 := abs_II_le2 (f_p p g.nat_degree) (x:ℝ) triv,
    have triv2 : (II (f_p p g.nat_degree) ↑x) = (II (f_p p g.nat_degree) ↑x) := by rw II,
    rw triv2, rw mul_assoc, rw mul_assoc, apply mul_le_mul, exact le_refl (abs ↑(polynomial.coeff g x)),
    rw <-mul_assoc, exact ineq3, exact abs_nonneg (II (f_p p (polynomial.nat_degree g)) ↑x), exact abs_nonneg _,
  },
  exact le_trans ineq1 ineq2,
end

private lemma coe_sum (s : finset ℕ) (f : ℕ -> ℤ) : ↑(∑ i in s, f i) = (∑ i in s, ((f i):ℝ)) :=
begin
  apply finset.induction_on s, simp only [int.cast_zero, finset.sum_empty], intros a s ha H, rw finset.sum_insert, simp only [int.cast_add], rw H, rw finset.sum_insert, assumption, assumption,
end

lemma coe_f_eval (f : ℤ[X]) (i : ℕ) : f_eval_on_ℝ f (i:ℝ) = ((@polynomial.eval ℤ _ (i : ℤ) f):ℝ) :=
begin
  simp only [f_eval_on_ℝ, polynomial.eval_map, polynomial.eval, polynomial.eval₂, polynomial.sum, coe_sum],
  apply finset.sum_congr,
  { apply polynomial.support_map_of_injective _ ℤembℝ_inj },
  intros, simp only [int.cast_coe_nat, int.cast_pow, ring_hom.eq_int_cast, id.def, int.cast_mul],
  simp only [int.cast_eq_zero,
 int.cast_id,
 ring_hom.eq_int_cast,
 ring_hom.map_int_cast,
 mul_eq_mul_left_iff,
 true_or,
 eq_self_iff_true,
 polynomial.coeff_map],
end

private lemma f_bar_X_pow {n : ℕ} : f_bar (polynomial.X ^ n) = polynomial.X^n :=
begin
  ext, rw bar_coeff, simp only [polynomial.coeff_X_pow], split_ifs; exact rfl
end

private lemma f_bar_X_sub_pow (n k : ℕ) (c:ℕ) : polynomial.eval (k:ℤ) (f_bar ((polynomial.X - polynomial.C (c:ℤ))^n)) ≤ polynomial.eval (k:ℤ) (polynomial.X + polynomial.C (c:ℤ))^n :=
begin
  induction n with n hn,
  {simp only [pow_zero], rw f_bar_1, simp only [polynomial.eval_one]},
  rw pow_succ,
  have ineq1 := eval_f_bar_mul (polynomial.X - polynomial.C (c:ℤ)) ((polynomial.X - polynomial.C (c:ℤ)) ^ n) k,
  have id1 : f_bar (polynomial.X - polynomial.C ↑c) = polynomial.X + polynomial.C (c:ℤ),
  { ext, rw bar_coeff, simp only [polynomial.coeff_add, polynomial.coeff_sub],
    rw polynomial.coeff_X,
    split_ifs,
    { rw <-h, rw polynomial.coeff_C, split_ifs,
      { exfalso, linarith },
      { simp only [add_zero, sub_zero, abs_one] } },
    { simp only [zero_sub, abs_neg, zero_add], rw polynomial.coeff_C, split_ifs,
      { apply abs_of_nonneg, apply int.coe_nat_nonneg },
      { simp only [abs_zero] } } },
  rw id1 at ineq1,
  rw pow_succ,
  have ineq2 : polynomial.eval ↑k (polynomial.X + polynomial.C ↑c) *
      polynomial.eval ↑k (f_bar ((polynomial.X - polynomial.C ↑c) ^ n)) ≤
      polynomial.eval ↑k (polynomial.X + polynomial.C ↑c) * polynomial.eval ↑k (polynomial.X + polynomial.C ↑c) ^ n,
  { apply mul_le_mul_of_nonneg_left hn,
    simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_add],
    apply add_nonneg; apply int.coe_nat_nonneg },
  exact le_trans ineq1 ineq2,
end

lemma f_p_bar_est (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) (j:ℕ) (hi : j ∈ finset.range g.nat_degree.succ) : @polynomial.eval ℤ _ (j:ℤ) (f_bar (f_p p g.nat_degree)) ≤ (2 * ↑(g.nat_degree.succ)) ^ (p + p * g.nat_degree) :=
begin
  simp only [finset.mem_range] at hi,
  rw f_p,
  have ineq1 := eval_f_bar_mul (polynomial.X ^ (p - 1)) (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j,
  rw f_bar_X_pow at ineq1,
  have triv : (polynomial.eval (j:ℤ) (polynomial.X ^ (p - 1))) = (↑j)^(p-1) := by simp only [polynomial.eval_X, polynomial.eval_pow],
  rw triv at ineq1,
  replace triv : (j:ℤ)^(p-1) < (2*↑g.nat_degree.succ)^(p-1),
  {
    norm_cast, apply nat.pow_lt_pow_of_lt_left,
    have ineq : 1 * g.nat_degree.succ ≤ 2 * g.nat_degree.succ,
      apply mul_le_mul, exact one_le_two, exact le_refl _, exact bot_le, exact bot_le,
    rw one_mul at ineq, exact gt_of_ge_of_gt ineq hi,
    exact nat.prime.pred_pos hp,
  },
  have triv' : (2*g.nat_degree.succ:ℤ)^(p-1) ≤ (2*g.nat_degree.succ:ℤ)^p,
  { norm_cast,
    refine (@pow_le_pow ℕ _ (2*g.nat_degree.succ) (p-1) p) _ (nat.sub_le p 1),
    exact inf_eq_left.mp rfl, },
  replace triv : (j:ℤ)^(p-1) < (2*g.nat_degree.succ:ℤ)^p := gt_of_ge_of_gt triv' triv,

  have ineq2 : (j:ℤ) ^ (p - 1) * polynomial.eval ↑j (f_bar (∏ (i : ℕ) in finset.range g.nat_degree,(polynomial.X - polynomial.C (↑i + 1)) ^ p)) ≤
              (2*g.nat_degree.succ:ℤ)^p * polynomial.eval ↑j
        (f_bar (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p)),
  { apply mul_le_mul,
    {exact le_of_lt triv},
    {apply le_refl},
    {apply eval_f_bar_nonneg},
    {norm_cast, exact bot_le} },
  replace ineq1 := le_trans ineq1 ineq2,

  replace ineq2 :
    polynomial.eval (j:ℤ) (f_bar (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p)) ≤
    (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))^p))) := eval_f_bar_prod _ _ _,

  have ineq3 : (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))^p))) ≤
    (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))))^p),
  { apply finset.prod_le_prod,
    { intros, exact eval_f_bar_nonneg _ _ },
    { intros, exact eval_f_bar_pow _ _ _ } },

  have ineq4 : (∏ i in finset.range g.nat_degree, polynomial.eval (j:ℤ) (f_bar ((polynomial.X - polynomial.C (↑i+1))))^p) ≤
  (∏ i in finset.range g.nat_degree, (polynomial.eval (j:ℤ) (polynomial.X + polynomial.C (↑i+1)))^p),
  {
    apply finset.prod_le_prod,
    { intros, exact pow_nonneg (eval_f_bar_nonneg _ j) p },
    intros x hx,
    have : (f_bar (polynomial.X - polynomial.C (x + 1:ℤ))) = polynomial.X + polynomial.C (x+1:ℤ),
    {
      ext, simp only [bar_coeff, polynomial.coeff_X, polynomial.coeff_C, polynomial.C_add, polynomial.coeff_add, polynomial.coeff_one, polynomial.C_1, polynomial.coeff_sub],
      split_ifs,
      {rw h_1 at h, linarith},
      {exfalso, linarith},
      {linarith},
      {simp only [add_zero, sub_zero, abs_one]},
      {rw zero_sub, rw abs_neg, simp only [zero_add], rw abs_of_nonneg, norm_cast, exact bot_le},
      {rw zero_sub, rw abs_neg, rw zero_add, apply abs_of_nonneg, norm_cast, simp only [zero_le]},
      {exfalso, exact h_1 (eq.symm h_2) },
      {simp only [add_zero, sub_zero, abs_zero]},
    },
    rw this,
  },

  have eq1 : (∏ i in finset.range g.nat_degree, (polynomial.eval (j:ℤ) (polynomial.X + polynomial.C (↑i+1)))^p) =
    (∏ i in finset.range g.nat_degree, (j+i+1:ℤ)^p),
    apply finset.prod_congr, refl, intros, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_add], apply congr_arg, refl,
  rw eq1 at ineq4,

  have ineq4' : (∏ i in finset.range g.nat_degree, (j+i+1:ℤ)^p) ≤ (∏ i in finset.range g.nat_degree, (2*g.nat_degree.succ:ℤ)^p),
    apply finset.prod_le_prod, intros, norm_cast, exact bot_le, intros, norm_cast, apply nat.pow_le_pow_of_le_left, rw two_mul, simp only [finset.mem_range] at H,
    rw add_assoc, apply add_le_add, exact le_of_lt hi, exact nat.le_succ_of_le H,

  have eq2 : (∏ i in finset.range g.nat_degree, (2*g.nat_degree.succ:ℤ)^p) = (2*g.nat_degree.succ:ℤ)^(p*g.nat_degree),
    rw finset.prod_const, simp only [int.coe_nat_succ, finset.card_range], rw pow_mul,

  rw eq2 at ineq4',
  replace ineq4 := le_trans ineq4 ineq4',

  have ineq5 : (2 * ↑(g.nat_degree.succ)) ^ p *
      (polynomial.eval ↑j
        (f_bar (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p))) ≤
      (2 * ↑(g.nat_degree.succ)) ^ p * ∏ (i : ℕ) in finset.range g.nat_degree,
        polynomial.eval ↑j (f_bar ((polynomial.X - polynomial.C (↑i + 1)) ^ p)),
    apply mul_le_mul, exact le_refl ((2 * ↑((polynomial.nat_degree g).succ)) ^ p), exact ineq2, exact eval_f_bar_nonneg (∏ (i : ℕ) in finset.range g.nat_degree, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j,
    norm_cast, exact bot_le,

  have ineq6 : (2 * ↑(g.nat_degree.succ)) ^ p * ∏ (i : ℕ) in finset.range g.nat_degree,
        polynomial.eval ↑j (f_bar ((polynomial.X - polynomial.C (i + 1:ℤ)) ^ p)) ≤
        (2 * ↑(g.nat_degree.succ)) ^ p * (2 * ↑(g.nat_degree.succ)) ^ (p * g.nat_degree),
    apply mul_le_mul, exact le_refl ((2 * ↑((polynomial.nat_degree g).succ)) ^ p), exact le_trans ineq3 ineq4,
    apply finset.prod_nonneg, intros x H, exact eval_f_bar_nonneg ((polynomial.X - polynomial.C (↑x + 1)) ^ p) j,
    norm_cast, exact bot_le,

  rw <-pow_add at ineq6,
  exact le_trans ineq1 (le_trans ineq5 ineq6),
end

/--
`set_of_abs_coeff g` returns the set {|g0|, |g1|,...,|gn|} where g = g0+g1*X+...+gn*X^n
-/
def set_of_abs_coeff (g : ℤ[X]) : finset ℤ := finset.image (λ i : ℕ, abs (g.coeff i)) g.support
/--
`set_of_1_abs_coeff g` returns the set {1, |g0|, |g1|,...,|gn|} where g = g0+g1*X+...+gn*X^n
-/
def set_of_1_abs_coeff (g : ℤ[X]) : finset ℤ := insert 1 (set_of_abs_coeff g)

theorem set_of_1_abs_coeff_nonempty (g : ℤ[X]) : finset.nonempty (set_of_1_abs_coeff g) :=
begin
  rw set_of_1_abs_coeff, use 1, simp only [true_or, eq_self_iff_true, finset.mem_insert],
end

/--
`max_abs_coeff_1 g` is the maximum of the set {1, |g0|, |g1|,...,|gn|} where g = g0+g1*X+...+gn*X^n
-/
def max_abs_coeff_1 (g : ℤ[X]) := finset.max' (set_of_1_abs_coeff g) (set_of_1_abs_coeff_nonempty g)
lemma max_abs_coeff_1_ge_1 (g : ℤ[X]) : 1 ≤ max_abs_coeff_1 g :=
begin
  rw max_abs_coeff_1, apply finset.le_max', rw set_of_1_abs_coeff, simp only [true_or, eq_self_iff_true, finset.mem_insert],
end

lemma zero_le_max_abs_coeff_1 (g : ℤ[X]) : 0 ≤ max_abs_coeff_1 g :=
zero_le_one.trans $ max_abs_coeff_1_ge_1 g

private lemma abs_J_ineq1'_coe (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  (∑ i in finset.range g.nat_degree.succ,
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * (f_eval_on_ℝ (f_bar (f_p p g.nat_degree)) (i:ℝ))) =
 ((∑ i in finset.range g.nat_degree.succ,
  (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p g.nat_degree)):ℝ)))) :=
begin
  apply finset.sum_congr, refl, intros,
  rw coe_f_eval,
end

lemma abs_J_ineq1'' (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  abs (J g p) ≤
  ((∑ i in finset.range g.nat_degree.succ,
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p g.nat_degree)):ℝ)))) :=
begin
  rw <-abs_J_ineq1'_coe, exact abs_J_ineq1' g p, exact hp,
end

lemma sum_ineq_1 (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  ((∑ i in finset.range g.nat_degree.succ,
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p g.nat_degree)):ℝ)))) ≤
  (g.nat_degree.succ:ℝ) *
      (↑(max_abs_coeff_1 g) * (↑(g.nat_degree) + 1) * ((g.nat_degree:ℝ) + 1).exp *
         (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) :=
begin
  have ineq1 :
  (∑ i in finset.range g.nat_degree.succ,
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * ((@polynomial.eval ℤ _ (i:ℤ) (f_bar (f_p p g.nat_degree)):ℝ))) ≤
  (∑ i in finset.range g.nat_degree.succ, (max_abs_coeff_1 g:ℝ) * (g.nat_degree.succ : ℝ) * (g.nat_degree.succ:ℝ).exp * ((2 * ↑(g.nat_degree.succ)) ^ (p + p * g.nat_degree))),
  {
    apply finset.sum_le_sum, intros x H, simp only [finset.mem_range] at H,
    by_cases hx : (x ∈ g.support),
    {
      apply mul_le_mul,
      { apply mul_le_mul,
        { norm_cast,
          apply mul_le_mul,
          { rw max_abs_coeff_1, apply finset.le_max', rw set_of_1_abs_coeff,
            simp only [finset.mem_insert], right, rw set_of_abs_coeff, rw finset.mem_image,
            exact ⟨x, hx, rfl⟩ },
          { norm_cast, exact le_of_lt H },
          { norm_cast, exact bot_le },
          { exact zero_le_max_abs_coeff_1 g } },
        {rw real.exp_le_exp, norm_cast, exact le_of_lt H},
        { exact (real.exp_pos _).le },
        { norm_cast, apply mul_nonneg,
          { exact zero_le_max_abs_coeff_1 g },
          { norm_cast, exact bot_le } } },
      { norm_cast,
        have est := f_p_bar_est g p hp x, simp only [int.coe_nat_succ, finset.mem_range] at est,
        replace est := est H,
        simp only [int.coe_nat_zero, int.coe_nat_pow, int.coe_nat_succ, zero_add, int.coe_nat_mul],
        exact est },
      { norm_cast, exact eval_f_bar_nonneg (f_p p (polynomial.nat_degree g)) x },
      apply mul_nonneg,
      { apply mul_nonneg,
        { norm_cast, exact zero_le_max_abs_coeff_1 g },
        { norm_cast, exact bot_le } },
      { exact (real.exp_pos _).le },
    },
    have hx' : g.coeff x = 0,
    { rwa ←polynomial.not_mem_support_iff },
    rw hx', simp only [int.cast_zero, zero_mul, abs_zero, nat.cast_succ],
    apply mul_nonneg,
    { apply mul_nonneg,
      { apply mul_nonneg,
        { norm_cast, exact zero_le_max_abs_coeff_1 g },
        { norm_cast, exact bot_le } },
      { exact (real.exp_pos _).le } },
    { apply pow_nonneg,
      refine mul_nonneg zero_le_two _,
      norm_cast, exact bot_le },
  },
  rw finset.sum_const at ineq1, conv_rhs at ineq1 {simp only [nat.cast_succ, finset.card_range],}, rw nsmul_eq_mul at ineq1,
  exact ineq1,
end

lemma self_le_pow_nat (n m : ℕ) (hm : 1 ≤ m) : n ≤ n ^ m :=
begin
  cases n,
  { simp only [zero_le] },
  { conv_lhs {rw ←pow_one n.succ},
    apply nat.pow_le_pow_of_le_right n.succ_pos hm },
end

lemma sum_ineq_2 (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  (g.nat_degree.succ:ℝ) * (↑(max_abs_coeff_1 g) * (↑(g.nat_degree) + 1) * ((g.nat_degree:ℝ) + 1).exp *
         (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) ≤
  (g.nat_degree.succ:ℝ) ^ p * (↑(max_abs_coeff_1 g) ^ p * (↑(g.nat_degree) + 1) ^ p * ((g.nat_degree:ℝ) + 1).exp ^ p *
         (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) :=
begin
  have hp' : p ≥ 1 := hp.one_lt.le,
  apply mul_le_mul,
    norm_cast, apply self_le_pow_nat, assumption,
    apply mul_le_mul,
    apply mul_le_mul, apply mul_le_mul, norm_cast,
    have triv : max_abs_coeff_1 g = (max_abs_coeff_1 g) ^ 1, simp only [pow_one], conv_lhs {rw triv}, apply pow_le_pow, exact max_abs_coeff_1_ge_1 g,
    assumption, norm_cast, apply self_le_pow_nat, assumption, norm_cast, exact bot_le, norm_cast, apply pow_nonneg, exact zero_le_max_abs_coeff_1 g,
    have triv : (g.nat_degree + 1:ℝ).exp = (g.nat_degree + 1:ℝ).exp ^ 1, simp only [pow_one], conv_lhs {rw triv}, apply pow_le_pow,
    by_contra rid, simp only [not_le] at rid,
    have ineq := (real.exp_lt_one_iff.1 rid), norm_cast at ineq, linarith, assumption,
    have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq,
    apply mul_nonneg,  norm_cast, apply pow_nonneg, exact zero_le_max_abs_coeff_1 g,
    norm_cast, exact bot_le,
    exact le_refl ((2 * (↑(polynomial.nat_degree g) + 1)) ^ (p + p * polynomial.nat_degree g)),
    norm_cast, exact bot_le, apply mul_nonneg, apply mul_nonneg, norm_cast, apply pow_nonneg, exact zero_le_max_abs_coeff_1 g,
    norm_cast, exact bot_le, apply pow_nonneg, have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq,
    apply mul_nonneg, apply mul_nonneg, apply mul_nonneg, norm_cast, exact zero_le_max_abs_coeff_1 g,
    norm_cast, exact bot_le, have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq, norm_cast, exact bot_le,
    norm_cast, exact bot_le,
end

/--
For an integer polynomial g = g0 + g1*X + ... + gn * X^n, we define
M = n * ((max_abs_coeff_1 g) * (n+1) * e^(n+1) * (2 * (n+1)) ^ (1 + n))

We use M to get an upperbound for |J(g,p)|
-/
def M (g : ℤ[X]) : ℝ := g.nat_degree.succ * ((max_abs_coeff_1 g) * (g.nat_degree + 1) * ((g.nat_degree:ℝ) + 1).exp * (2 * (g.nat_degree + 1)) ^ (1 + g.nat_degree))

theorem abs_J_upper_bound (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) : abs (J g p) ≤ (M g)^p :=
begin
  have ineq1 := abs_J_ineq1'' g p hp,
  have ineq2 := sum_ineq_1 g p hp,
  have ineq3 := sum_ineq_2 g p hp,
  have ineq4 := le_trans (le_trans ineq1 ineq2) ineq3,
  rw [M, mul_pow, mul_pow, mul_pow, mul_pow, <-pow_mul, add_mul, one_mul],
  have eq1 : g.nat_degree * p = p * g.nat_degree, rw mul_comm, rw eq1, exact ineq4,
end


lemma sum_sub_sum1 (m : ℕ) (f : ℕ -> ℂ) : (∑ i in finset.range m.succ, f i) - (∑ i in finset.range m, f i) = f m :=
begin
  rw [finset.sum_range_succ, add_sub_cancel'],
end

lemma fact_grows_fast' (M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N < n -> M ^ (n+1) < (n.factorial) :=
begin
by_cases h:  (M = 0),
{ use 1, intros n hn, rw [h, zero_pow n.succ_pos], exact nat.factorial_pos n },
{ have H := complex.is_cau_exp (M:ℂ),
  have triv : (1/M:ℝ) > 0,
  {apply one_div_pos.2, norm_cast, exact bot_lt_iff_ne_bot.mpr h},
  have H2 := is_cau_seq.cauchy₂ H triv,
  choose i hi using H2, use i, intros n hn,
  have H3 := hi n.succ (nat.le_succ_of_le hn.le) n hn.le,
  rw finset.sum_range_succ at H3,
  simp only [one_div, complex.abs_cast_nat, complex.abs_div, add_sub_cancel] at H3,
  norm_num at H3, rw div_lt_iff at H3,
  replace triv2 : (M:ℝ) > 0,
  {norm_num, exact bot_lt_iff_ne_bot.mpr h},
  have H4 := (mul_lt_mul_right triv2).2 H3,
  replace triv2 : (M:ℝ)^n * (M:ℝ) = (M:ℝ)^(n+1), rw pow_add, simp only [pow_one], rw triv2 at H4,
  replace triv2 : (↑M)⁻¹ * ↑(n.factorial) * ↑M = (n.factorial:ℝ),
  { rw mul_comm, rw <-mul_assoc,
    have triv3 : (M:ℝ) * (↑M)⁻¹ = 1, {rw mul_comm, apply inv_mul_cancel, norm_num, assumption},
    rw triv3, simp only [one_mul] },
  rw triv2 at H4, norm_cast at H4, assumption, norm_cast, exact nat.factorial_pos n, }
end

lemma fact_grows_fast (M : ℝ) (hM : 0 ≤ M) : ∃ N : ℕ, ∀ n : ℕ, N < n -> M^(n+1) < (n.factorial : ℝ) :=
begin
  obtain ⟨M', hM'⟩ := exists_nat_gt M,
  have triv := fact_grows_fast' M',
  choose N hN using triv, use N, intros n hn,
  replace hN := hN n hn,
  have ineq : (M':ℝ) ^ (n + 1) > M ^ (n+1) := pow_lt_pow_of_lt_left hM' hM (nat.succ_pos n),
  apply lt_trans ineq,
  norm_cast, assumption,
end


theorem coup_de_grace (M : ℝ) (hM : 0 ≤ M) (z : ℤ) : ∃ p : nat.primes, z < (p.val:ℤ) ∧ M^p.val < ((p.val-1).factorial:ℝ) :=
begin
  have grow_rate := fact_grows_fast M hM,
  choose N hN using grow_rate,
  have p_exists := nat.exists_infinite_primes (max (N+2) (z.nat_abs+1)),
  choose p Hp using p_exists, use (⟨p, Hp.right⟩ : nat.primes), simp only [max_le_iff, gt_iff_lt] at Hp ⊢,
  split,
    have triv : z ≤ (z.nat_abs:ℤ), rw <-int.abs_eq_nat_abs, exact le_max_left z (-z),
    have hp := Hp.left.right,
    replace hp : (z.nat_abs + 1:ℤ) ≤ p, norm_cast, assumption,
    have triv2 : (z.nat_abs : ℤ) < (z.nat_abs:ℤ) + 1, exact lt_add_one ↑(int.nat_abs z), exact gt_of_gt_of_ge hp triv,

    have triv := hN (p-1) _,
    have eq1 : (p - 1 + 1) = p, {apply nat.sub_add_cancel, exact le_of_lt Hp.right.one_lt,},
    rw eq1 at triv, assumption,
    have triv := Hp.left.left,
    replace triv : N + 1 < p , exact triv, exact nat.lt_pred_iff.mpr triv,
end

theorem non_empty_supp (f : ℤ[X]) (hf : f ≠ 0) : f.support.nonempty :=
begin
  simp_rw [finset.nonempty, polynomial.mem_support_iff],
  contrapose! hf, ext, simp only [polynomial.coeff_zero], apply hf,
end

/--
`min_degree_term f` is the lowest degree of monomials of f.
If f = 3*X^2 + X^3 then `min_degree_term f` is 2
-/
def min_degree_term (f : ℤ[X]) (hf : f ≠ 0) : ℕ := finset.min' (f.support) (non_empty_supp f hf)
/--
Thus if we divide f by X^m where m is `min_degree_term f`, then the resulting polynomial will have a
nonzero constant term.
-/
def make_const_term_nonzero (f : ℤ[X]) (hf : f ≠ 0) : ℤ[X] :=
⟨{ support := finset.image (λ i : ℕ, i-(min_degree_term f hf)) f.support,
  to_fun := (λ n, (f.coeff (n+(min_degree_term f hf)))),
  mem_support_to_fun := begin
    intro n,
    rw [←polynomial.mem_support_iff, finset.mem_image],
    split,
    { rintro ⟨a, ha, rfl⟩,
      rwa nat.sub_add_cancel,
      rw min_degree_term, exact finset.min'_le _ _ ha },

    { intro hn,
      exact ⟨n + min_degree_term f hf, hn, nat.add_sub_cancel _ _⟩ },
  end,
}⟩

theorem coeff_after_change (f : ℤ[X]) (hf : f ≠ 0) (n : ℕ) :
  (make_const_term_nonzero f hf).coeff n = (f.coeff (n+(min_degree_term f hf))) :=
by simp [make_const_term_nonzero]

theorem coeff_zero_after_change (f : ℤ[X]) (hf : f ≠ 0) : (make_const_term_nonzero f hf).coeff 0 ≠ 0 :=
begin
  rw [coeff_after_change, zero_add, ←polynomial.mem_support_iff, min_degree_term],
  exact f.support.min'_mem (non_empty_supp f hf),
end

theorem supp_after_change (f : ℤ[X]) (hf : f ≠ 0) :
  (make_const_term_nonzero f hf).support = finset.image (λ i : ℕ, i-(min_degree_term f hf)) f.support :=
by simp [make_const_term_nonzero]

theorem aeval_ (f : ℤ[X]) (r : ℝ) : @polynomial.aeval ℤ ℝ _ _ _ r f = ∑ i in f.support, (f.coeff i : ℝ) * r ^ i :=
begin
  rw [polynomial.aeval_def, polynomial.eval₂, polynomial.sum],
  apply congr_arg, ext, simp only [ring_hom.eq_int_cast],
end

theorem non_zero_after_change (f : ℤ[X]) (hf : f ≠ 0) : (make_const_term_nonzero f hf) ≠ 0 :=
begin
  intro rid, rw polynomial.ext_iff at rid, simp only [polynomial.coeff_zero] at rid,
  replace rid := rid 0,
  exact coeff_zero_after_change f hf rid,
end

theorem coeff_sum (f : ℕ -> (ℤ[X])) (s : finset ℕ) (n : ℕ) : (∑ i in s, f i).coeff n = (∑ i in s, (f i).coeff n) :=
begin
    apply finset.induction_on s, simp only [finset.sum_empty, polynomial.coeff_zero],
    intros a s ha H, rw finset.sum_insert, rw finset.sum_insert, rw polynomial.coeff_add, rw H, assumption, assumption,
end

theorem as_sum' (f : ℤ[X]) : f = ∑ i in f.support, (polynomial.C (f.coeff i)) * (polynomial.X^i) :=
begin
    ext, rw coeff_sum,
    have triv : ∑ (i : ℕ) in f.support, (polynomial.C (f.coeff i) * polynomial.X ^ i).coeff n =
        ∑ (i : ℕ) in f.support, (f.coeff i) * ((polynomial.X ^ i).coeff n),
    {apply congr_arg, ext, simp only [polynomial.coeff_C_mul]},
    rw triv,
    replace triv : ∑ (i : ℕ) in f.support, f.coeff i * (polynomial.X ^ i).coeff n =
        ∑ (i : ℕ) in f.support, (ite (n = i) (f.coeff i) 0),
    {apply congr_arg, simp only [mul_boole, polynomial.coeff_X_pow]},
    rw triv, rw finset.sum_ite, simp only [add_zero, finset.sum_const_zero], rw finset.filter_eq,
    split_ifs,
    {simp only [finset.sum_singleton]},
    {simp only [finset.sum_empty, ←polynomial.not_mem_support_iff], exact h},
end

theorem transform_eq (f : ℤ[X]) (hf : f ≠ 0) : f = (make_const_term_nonzero f hf) * (polynomial.X) ^ (min_degree_term f hf) :=
begin
  set i : Π (a : ℕ), a ∈ f.support → ℕ := λ a _, a - (min_degree_term f hf) with i_eq,
  have hi : ∀ (a : ℕ) (ha : a ∈ f.support), i a ha ∈ (make_const_term_nonzero f hf).support,
  {
    intros a ha, rw i_eq,
    have triv : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha = a - min_degree_term f hf := rfl,
    rw triv, rw supp_after_change, rw finset.mem_image, use a, split, exact ha, refl,
  },
  have assump1 : (∀ (a : ℕ) (ha : a ∈ f.support),
     (λ (i : ℕ), (polynomial.C (f.coeff i)) * (polynomial.X) ^ i) a =
       (λ (i : ℕ), (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i + min_degree_term f hf)) (i a ha)),
  {
    intros a ha,
    have triv1 : (λ (i : ℕ), (polynomial.C (f.coeff i)) * (polynomial.X) ^ i) a = (polynomial.C (f.coeff a)) * (polynomial.X) ^ a := rfl,
    rw triv1,
    have triv2 : (λ (i : ℕ), (polynomial.C ((make_const_term_nonzero f hf).coeff i)) * (polynomial.X) ^ (i + min_degree_term f hf)) (i a ha)
        = (polynomial.C ((make_const_term_nonzero f hf).coeff (i a ha))) * (polynomial.X) ^ (i a ha + min_degree_term f hf) := rfl,
    rw triv2, rw i_eq,
    have triv3 : ((λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a ha) = a - min_degree_term f hf := rfl,
    rw triv3, rw coeff_after_change, rw nat.sub_add_cancel, rw min_degree_term, exact f.support.min'_le a ha,
  },
  have assump2 : (∀ (a₁ a₂ : ℕ) (ha₁ : a₁ ∈ f.support) (ha₂ : a₂ ∈ f.support),
     i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂),
  {
    intros a1 a2 ha1 ha2 H, rw i_eq at H,
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a1 ha1 = a1 - min_degree_term f hf, exact rfl, rw triv1 at H,
    have triv2 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a2 ha2 = a2 - min_degree_term f hf, exact rfl, rw triv2 at H,
    have triv3 := (@add_left_inj ℕ _ (min_degree_term f hf) (a1 - min_degree_term f hf) (a2 - min_degree_term f hf)).2 H,
    rw nat.sub_add_cancel at triv3, rw nat.sub_add_cancel at triv3, exact triv3, rw min_degree_term, exact f.support.min'_le a2 ha2, exact f.support.min'_le a1 ha1,
  },
  have assump3 : ∀ (b : ℕ),
     b ∈ (make_const_term_nonzero f hf).support → (∃ (a : ℕ) (ha : a ∈ f.support), b = i a ha),
    intros b hb, rw supp_after_change at hb, rw finset.mem_image at hb, rw i_eq, choose a Ha using hb, use a, use Ha.1,
    have triv1 : (λ (a : ℕ) (ha : a ∈ f.support), a - min_degree_term f hf) a _ = a - min_degree_term f hf, exact rfl, exact Ha.1, rw triv1, exact eq.symm Ha.2,
  have H := finset.sum_bij i hi assump1 assump2 assump3,
  have eq1 := as_sum' f,
  have eq2 := as_sum' (make_const_term_nonzero f hf), rw eq2,
  simp only [] at H ⊢, rw finset.sum_mul,

  have eq3 : ∑ (x : ℕ) in (make_const_term_nonzero f hf).support,
      polynomial.C ((make_const_term_nonzero f hf).coeff x) * polynomial.X ^ (x + min_degree_term f hf) =
    ∑ (x : ℕ) in (make_const_term_nonzero f hf).support,
      polynomial.C ((make_const_term_nonzero f hf).coeff x) * polynomial.X ^ x * polynomial.X ^ min_degree_term f hf,
    apply finset.sum_congr, exact rfl, intros, rw pow_add, ring,
  rw [<-eq3, <-H], exact eq1,
end

theorem non_zero_root_same (f : ℤ[X]) (hf : f ≠ 0) (r : ℝ) (r_nonzero : r ≠ 0) (root_r : @polynomial.aeval ℤ ℝ _ _ _ r f = 0) :
  (@polynomial.aeval ℤ ℝ _ _ _ r) (make_const_term_nonzero f hf) = 0 :=
begin
  have eq1 := transform_eq f hf, rw eq1 at root_r, simp only [polynomial.aeval_X, alg_hom.map_pow, alg_hom.map_mul, mul_eq_zero] at root_r,
  cases root_r, exact root_r, replace root_r := pow_eq_zero root_r, exfalso, exact r_nonzero root_r,
end

theorem nat_degree_decrease (f:ℤ[X]) (hf : f ≠ 0) : (make_const_term_nonzero f hf).nat_degree ≤ f.nat_degree :=
begin
  have transform_eq := transform_eq f hf,
  have eq1 := @polynomial.nat_degree_mul ℤ _ _ (make_const_term_nonzero f hf) (polynomial.X ^ min_degree_term f hf) _ _,
  have triv : (make_const_term_nonzero f hf * polynomial.X ^ min_degree_term f hf).nat_degree = f.nat_degree,
    apply congr_arg, exact eq.symm transform_eq,
  rw triv at eq1, exact nat.le.intro (eq.symm eq1),
  intro rid, have contra := polynomial.ext_iff.1 rid, simp only [polynomial.coeff_zero] at contra, replace contra := contra 0,
  exact coeff_zero_after_change f hf contra,
  intro contra, replace contra := polynomial.ext_iff.1 (pow_eq_zero contra) 1, simp only [polynomial.coeff_X_one, one_ne_zero, polynomial.coeff_zero] at contra, exact contra,
end

notation `transcendental` x := ¬(is_algebraic ℤ x)
theorem e_transcendental : transcendental e :=
begin
-- main part
  intro e_algebraic,
  rw is_algebraic at e_algebraic,
  choose g' g'_def using e_algebraic,
  have g'_nonzero := g'_def.1,
  have e_root_g' := g'_def.2,
  generalize g_def : make_const_term_nonzero g' g'_nonzero = g,
  have coeff_zero_nonzero : (g.coeff 0) ≠ 0,
    rw <-g_def, apply coeff_zero_after_change,
  have e_root_g : (@polynomial.aeval ℤ ℝ _ _ _ e) g = 0,
    rw <-g_def,
    apply non_zero_root_same, rw e, exact (1:ℝ).exp_ne_zero, exact e_root_g',
  have coup_de_grace := coup_de_grace (M g) _ (max g.nat_degree (abs (g.coeff 0))),
  choose p Hp using coup_de_grace,
  have abs_J_upper_bound := abs_J_upper_bound g p.val p.property,
  simp only [gt_iff_lt, max_lt_iff, int.coe_nat_lt] at Hp,
  have abs_J_lower_bound := abs_J_lower_bound g e_root_g coeff_zero_nonzero p.val p.property _,
  have rid := le_trans abs_J_lower_bound abs_J_upper_bound,
  have rid2 := Hp.right, replace rid2 : ¬ ((M g ^ p) ≥ ((p.val - 1).factorial:ℝ)) := not_le.mpr rid2,
  exact rid2 rid,

-- assumptions I used in preveious part and lemmas
  split,
  exact Hp.1.1,
  have triv := Hp.left.right, rw int.abs_eq_nat_abs at triv, simp only [int.coe_nat_lt] at triv, assumption,

  rw M,
  apply mul_nonneg,
  {norm_cast, exact bot_le},
  apply mul_nonneg,
  { apply mul_nonneg,
    { norm_cast, apply mul_nonneg,
      {exact zero_le_max_abs_coeff_1 g},
      {norm_cast, exact bot_le} },
    { have triv : (g.nat_degree + 1 : ℝ).exp > 0 := (g.nat_degree + 1:ℝ).exp_pos,
      exact le_of_lt triv } },
  { apply pow_nonneg, apply mul_nonneg, { exact zero_le_two }, {norm_cast, exact bot_le}, }
end

theorem e_pow_transcendental (n : ℕ) (hn : 1 ≤ n) : transcendental (e^n) :=
begin
  intro alg,
  rcases alg with ⟨p, p_nonzero, hp⟩,
  have alg_e : is_algebraic ℤ e,
  {
    use ∑ i in finset.range (p.nat_degree + 1), polynomial.C (p.coeff i) * (polynomial.X ^ (i * n)),
    split,

    intro rid, rw polynomial.ext_iff at rid,
    replace p_nonzero := (not_iff_not.2 (@polynomial.ext_iff ℤ _ p 0)).1 p_nonzero,
    simp only [not_forall, polynomial.coeff_zero] at p_nonzero,
    choose k hk using p_nonzero,
    replace rid := rid (k * n),
    simp only [polynomial.mul_coeff_zero, polynomial.finset_sum_coeff, polynomial.coeff_zero] at rid,
    simp_rw [polynomial.coeff_C_mul_X_pow] at rid,
    rw finset.sum_eq_single k at rid,
    simp only [mul_one, if_true, true_or, eq_self_iff_true, nat.zero_eq_mul] at rid,
    exact hk rid,

    intros j hj1 hj2, split_ifs,
    replace h := (nat.mul_left_inj _).1 h,
    exfalso,
    exact hj2 (eq.symm h), exact hn, refl,

    intros hk, simp only [not_lt, finset.mem_range] at hk,
    simp only [if_true, eq_self_iff_true],
    apply polynomial.coeff_eq_zero_of_nat_degree_lt,
    linarith,


    have H := polynomial.as_sum_range p,
    rw H at hp, rw aeval_sum' at hp ⊢, rw <-hp,
    apply finset.sum_congr rfl,
    intros i hi,
    simp only [polynomial.aeval_X, polynomial.aeval_C, alg_hom.map_pow, alg_hom.map_mul],
    simp only [algebra_map_int_eq,
 int.cast_eq_zero,
 pow_mul',
 ring_hom.eq_int_cast,
 mul_eq_mul_left_iff,
 true_or,
 eq_self_iff_true,
 polynomial.aeval_monomial],
  },

  exact e_transcendental alg_e,
end

theorem zero_algebraic : is_algebraic ℤ (0 : ℝ) :=
begin
  use polynomial.X,
  split, intro rid, rw polynomial.ext_iff at rid,
  simp only [polynomial.coeff_zero] at rid,
  replace rid := rid 1,
  rw polynomial.coeff_X at rid,
  simp only [if_true, eq_self_iff_true, one_ne_zero] at rid, exact rid,
  simp only [polynomial.aeval_X],
end

theorem transcendental_irrational {x : ℝ} (trans_x : transcendental x) : irrational' x :=
begin
  by_cases (x = 0),
  rw h at trans_x, exfalso, exact trans_x zero_algebraic,


  by_contra rid,
  unfold irrational' at rid,
  simp only [gt_iff_lt, not_forall, ne.def, not_imp, not_not] at rid,
  rcases rid with ⟨a, b, hb, H⟩,
  set p : (ℤ[X]) := polynomial.C b * polynomial.X - polynomial.C a with hp,
  have x_alg : is_algebraic ℤ x,
  {
    use p, split, intro rid,
    rw polynomial.ext_iff at rid,
    replace rid := rid 0,
    simp only [zero_sub, polynomial.coeff_X_zero, polynomial.mul_coeff_zero, polynomial.coeff_sub, neg_eq_zero, polynomial.coeff_zero, mul_zero] at rid,
    rw polynomial.coeff_C at rid,
    simp only [if_true, eq_self_iff_true] at rid,
    rw rid at H,
    simp only [int.cast_zero, euclidean_domain.zero_div, sub_zero] at H,
    exact h H,

    simp only [polynomial.aeval_X, alg_hom.map_sub, alg_hom.map_mul],
    rw polynomial.aeval_C, rw polynomial.aeval_C,
    simp only [ring_hom.eq_int_cast],
    rw sub_eq_zero at H ⊢,
    rw eq_div_iff at H,
    rwa mul_comm, norm_cast at ⊢ hb,
    intro rid2, linarith,
  },
  exact trans_x x_alg,
end

theorem e_irrational : irrational' e := transcendental_irrational e_transcendental

theorem e_pow_n_irrational (n : ℕ) (hn : 1 ≤ n) : irrational' (e ^ n) := transcendental_irrational (e_pow_transcendental n hn)


-- #lint
