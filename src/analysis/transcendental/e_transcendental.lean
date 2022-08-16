import ring_theory.algebraic
import analysis.transcendental.e_transcendental_lemmas
import analysis.transcendental.basic
import data.polynomial.derivative
import data.real.irrational

noncomputable theory
open small_lemmas e_transcendental_lemmas
open_locale big_operators
open_locale classical
open_locale polynomial

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
  rw [f_p, polynomial.nat_degree_mul, polynomial.nat_degree_X_pow, polynomial.nat_degree_prod],
  simp only [polynomial.nat_degree_pow, polynomial.nat_degree_X_sub_C, finset.sum_const,
    finset.card_range, smul_eq_mul, mul_one],
  rw [add_comm, ←nat.add_sub_assoc hp.one_lt.le, add_one_mul],
  { exact λ i hi, pow_ne_zero _ (polynomial.X_sub_C_ne_zero _), },
  { exact pow_ne_zero _ polynomial.X_ne_zero },
  { rw finset.prod_ne_zero_iff,
    exact λ i hi, pow_ne_zero _ (polynomial.X_sub_C_ne_zero _), },
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
private lemma J_eq1 (g : ℤ[X]) (p : ℕ) :
  (J g p) = ∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p g.nat_degree) i) :=
begin
  rw J, apply congr_arg, ext, rw II_eq_I,
end


private lemma J_eq2' (g : ℤ[X]) (p : ℕ) (k : ℕ) :
  (g.coeff k:ℝ) * (I (f_p p g.nat_degree) k) =
   (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) 0)))
  - (g.coeff k:ℝ) * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) (k:ℝ))) :=
begin
  rw <-mul_sub, rw I, simp [deriv_n],
end

private lemma J_eq2 (g : ℤ[X]) (p : ℕ) :
  (∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p g.nat_degree) i)) =
   (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) 0)))
  -(∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) (k:ℝ))))) :=
begin
  rw <-finset.sum_sub_distrib, apply congr_arg, ext i, rw J_eq2',
end

private lemma J_eq3 (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0) (p : ℕ) :
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
              (p : ℕ) :
  (J g p) = - ∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
                (∑ k in finset.range g.nat_degree.succ,
                  (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) (k:ℝ))) :=
begin
  rw [J_eq1, J_eq2, J_eq3 _ e_root_g, finset.sum_comm], simp only [zero_sub, neg_inj],
  apply congr_arg, ext, rw finset.mul_sum,
end

lemma coe_J (g : ℤ[X]) (p : ℕ) :
    ∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
      (∑ k in finset.range g.nat_degree.succ,
        (g.coeff k : ℝ) * (f_eval_on_ℝ (deriv_n (f_p p g.nat_degree) j) (k:ℝ))) =
    int.cast_ring_hom ℝ (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
            (∑ k in finset.range g.nat_degree.succ,
              (g.coeff k) * (polynomial.eval (k:ℤ) (deriv_n (f_p p g.nat_degree) j)))) :=
begin
  rw ring_hom.map_sum, apply finset.sum_congr, exact rfl,
  intros i hi, rw ring_hom.map_sum, apply finset.sum_congr, refl,
  intros j hj, rw ring_hom.map_mul, simp only [ring_hom.eq_int_cast], rw f_eval_on_ℝ_nat, simp only [ring_hom.eq_int_cast],
end

theorem J_eq'' (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0)
              (p : ℕ) :
  (J g p) =  - int.cast_ring_hom ℝ (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
            (∑ k in finset.range g.nat_degree.succ,
              (g.coeff k) * (polynomial.eval (k:ℤ) (deriv_n (f_p p g.nat_degree) j)))) :=
begin
  rw J_eq' _ e_root_g, rw neg_eq_iff_neg_eq, rw neg_neg, rw <-coe_J,
end

lemma deriv_f_p_k_eq_zero_k_eq_0_when_j_lt_p_sub_one (p : ℕ) (n j : ℕ) (hj : j < p - 1):
  polynomial.eval 0 (deriv_n (f_p p n) j) = 0 :=
begin
  rw [f_p, deriv_n, polynomial.iterate_derivative_mul, polynomial.eval_finset_sum],
  apply finset.sum_eq_zero, intros i hi, rw polynomial.eval_smul,
  simp only [nat.succ_pos', finset.mem_range] at hi,
  rw [smul_eq_zero], right,
  have ineq : j - i < p - 1 := gt_of_gt_of_ge hj (nat.sub_le j i),
  rw [polynomial.eval_mul, mul_eq_zero], left,
  rw [polynomial.iterate_derivative_X_pow_eq_C_mul, polynomial.eval_mul],
  simp only [polynomial.eval_X, polynomial.eval_C, int.coe_nat_zero, polynomial.eval_pow, mul_eq_zero], right, apply zero_pow,
  exact nat.sub_pos_of_lt ineq,
end

lemma fact_eq_prod (n : ℕ) : (n.factorial:ℤ) = ∏ i in finset.range n, (i+1:ℤ) :=
begin
  rw ←finset.prod_range_add_one_eq_factorial,
  simp only [nat.cast_prod, eq_self_iff_true, nat.cast_add, nat.cast_one],
end

lemma fact_eq_prod'' (n : ℕ) : (n.factorial:ℤ) = ↑∏ i in finset.range n, (n-i) :=
begin
  rw [←finset.prod_range_reflect, ←finset.prod_range_add_one_eq_factorial],
  apply congr_arg _,
  apply finset.prod_congr rfl (λ i hi, _),
  rw [nat.sub_sub, nat.sub_sub_self, add_comm],
  rwa [nat.one_add_le_iff, ←finset.mem_range],
end

lemma fact_eq_prod' (n : ℕ) : (n.factorial:ℤ) = ∏ i in finset.range n, (n-i:ℤ) :=
begin
  -- TODO use fact_eq_prod''
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
  rw [f_p, deriv_n, polynomial.iterate_derivative_mul, polynomial.eval_finset_sum],
  rw finset.sum_eq_single 0,
  { simp only [nat.choose_self, int.cast_add, one_mul, int.coe_nat_zero, polynomial.eval_mul,
      int.coe_nat_succ, zero_add, nat.factorial, function.iterate_zero_apply, int.cast_coe_nat,
      ring_hom.eq_int_cast, nat.choose_zero_right, polynomial.iterate_derivative_X_pow_eq_smul,
      polynomial.eval_prod, polynomial.eval_X, mul_one, algebra.id.smul_eq_mul, zero_sub,
      nat.sub_self, polynomial.eval_one, polynomial.eval_pow, int.cast_one, polynomial.eval_smul,
      polynomial.eval_nat_cast, nat.sub_zero, polynomial.eval_add, neg_add_rev, polynomial.eval_sub,
      pow_zero, one_smul],
    rw mul_assoc,
    congr' 1,
    { rw [fact_eq_prod', nat.cast_prod],
      apply finset.prod_congr rfl (λ i hi, _),
      rw [finset.mem_range] at hi,
      exact nat.cast_sub hi.le },
    rw fact_eq_prod, rw pow_mul, rw <-mul_pow, simp_rw <-neg_add,

    have rhs : ((-1:ℤ) ^ n * ∏ (i : ℕ) in finset.range n, (↑i + 1)) = (∏ (i : ℕ) in finset.range n, (-1) * (↑i + 1)),
    {rw finset.prod_mul_distrib, rw finset.prod_const, rw [finset.card_range]},
    rw rhs, rw finset.prod_pow, congr' 1, apply finset.prod_congr rfl, rintro x -,
    rw neg_one_mul, rw add_comm },

  { intros i hi1 hi2,
    have : 0 < p - 1 - (p - 1 - i),
    { apply nat.sub_pos_of_lt, apply nat.sub_lt,
      { apply nat.sub_pos_of_lt, exact nat.prime.one_lt hp },
      { exact nat.pos_of_ne_zero hi2 } },
    simp only [nat.cast_prod, int.cast_coe_nat, polynomial.eval_X, int.cast_prod, int.cast_add,
      ring_hom.eq_int_cast, polynomial.iterate_derivative_X_pow_eq_smul, zero_mul,
      polynomial.eval_pow, nsmul_eq_mul, eq_self_iff_true, int.cast_one, polynomial.eval_mul,
      polynomial.eval_nat_cast, finset.prod_congr, mul_zero, zsmul_eq_mul, zero_pow this], },
  { intro rid, exfalso, simp only [nat.succ_pos', not_true, finset.mem_range] at rid, exact rid },
end

theorem f_p_n_succ (p : ℕ) (n : ℕ) : (f_p p n.succ) = (f_p p n) * (polynomial.X- polynomial.C (n+1:ℤ))^p :=
begin
  rw f_p, rw f_p, rw finset.prod_range_succ, ring,
end

lemma deriv_f_p_when_j_lt_p (p : ℕ) (n : ℕ) : ∀ x : ℕ, ∀ j : ℕ, j < p ->
  0 < x -> x < n.succ -> polynomial.eval (x:ℤ) (deriv_n (f_p p n) j) = 0 :=
begin
  simp_rw [deriv_n],
  induction n with n IH,
  { intros x j hj hx1 hx2,
    linarith },
  { intros x j hj hx1 hx2,
    rw [f_p_n_succ, polynomial.iterate_derivative_mul, polynomial.eval_finset_sum],
    apply finset.sum_eq_zero, intros y hy, simp only [finset.mem_range] at hy,
    rw [polynomial.eval_smul, polynomial.eval_mul],
    replace hx2 : x < n.succ ∨ x = n.succ, exact nat.lt_succ_iff_lt_or_eq.mp hx2,
    cases hx2,
    { rw IH x (j-y) (gt_of_gt_of_ge hj (nat.sub_le j y)) hx1 hx2,
      rw [zero_mul, smul_zero] },
    { rw smul_eq_zero, right,
      rw [hx2, polynomial.iterate_derivative_X_sub_pow, polynomial.eval_mul, polynomial.eval_pow],
      simp only [polynomial.eval_X, polynomial.eval_C, int.coe_nat_succ, polynomial.eval_sub, sub_self, mul_eq_zero],
      right, right, apply zero_pow (nat.sub_pos_of_lt (gt_of_ge_of_gt hj hy))
    },
  },
end

theorem deriv_f_p_k_eq_zero_when_j_lt_p_sub_one (p : ℕ) (n j : ℕ) (hj : j < p - 1) (k : ℕ) (hk : k ∈ finset.range n.succ):
  polynomial.eval (k:ℤ) (deriv_n (f_p p n) j) = 0 :=
begin
  cases k, exact deriv_f_p_k_eq_zero_k_eq_0_when_j_lt_p_sub_one p n j hj,
  apply deriv_f_p_when_j_lt_p p n k.succ j (nat.lt_of_lt_pred hj) (nat.succ_pos k) (finset.mem_range.mp hk),
end

private lemma k_eq_0_case_when_j_ge_p (p : ℕ) (hp : nat.prime p) (n:ℕ) :
  ∀ j : ℕ, p ≤ j -> (p.factorial:ℤ) ∣ polynomial.eval 0 (deriv_n (f_p p n) j) :=
begin
  rw f_p, intros j j_ge_p, rw [deriv_n, polynomial.iterate_derivative_mul, polynomial.eval_finset_sum],
  apply finset.dvd_sum,
  intros x hx,
  simp only [polynomial.eval_C, polynomial.C_add, polynomial.C_1, polynomial.eval_mul, nat.factorial],
  obtain h|h := eq_or_ne (j - x) (p - 1),
  {
    rw h, rw polynomial.iterate_derivative_X_pow_eq_C_mul,
    simp only [nat.cast_prod,
 int.cast_coe_nat,
 int.cast_prod,
 mul_one,
 ring_hom.eq_int_cast,
 polynomial.eval_prod,
 nat.sub_self,
 nsmul_eq_mul,
 polynomial.eval_mul,
 polynomial.C_eq_nat_cast,
 polynomial.eval_nat_cast,
 finset.prod_congr,
 pow_zero],
    suffices : (p:ℤ) ∣ polynomial.eval 0 (deriv_n (∏ (x : ℕ) in finset.range n, (polynomial.X - (↑x + 1)) ^ p) x),
    { obtain ⟨c, hc⟩ := this,
      rw [←deriv_n, hc],
      convert dvd_mul_right _ (c * (j.choose x)) using 1,
      rw [←nat.mul_factorial_pred hp.pos, int.coe_nat_mul, fact_eq_prod''],
      rw nat.cast_prod,
      ring },
    cases x,
    { simp only [nat.sub_zero] at h, rw h at j_ge_p,
      have this := @nat.sub_one_sub_lt p 0 (nat.prime.pos hp), simp only [nat.sub_zero] at this, linarith },

    { rw finset.prod_pow, apply polynomial.dvd_iterate_derivative_pow _ _ _ _ x.succ_pos },
  },
  obtain h|h := h.lt_or_lt,
  { rw [polynomial.iterate_derivative_X_pow_eq_C_mul (p - 1) (j - x), polynomial.eval_smul],
    simp only [nat.cast_prod,
 int.cast_coe_nat,
 polynomial.eval_X,
 int.cast_prod,
 ring_hom.eq_int_cast,
 polynomial.eval_pow,
 nsmul_eq_mul,
 polynomial.eval_mul,
 polynomial.C_eq_nat_cast,
 finset.prod_congr],
    rw (zero_pow (nat.sub_pos_of_lt h)),
    simp only [zero_mul, mul_zero, dvd_zero] },
  { rw [polynomial.iterate_derivative_eq_zero ((polynomial.nat_degree_X_pow_le _).trans_lt h)],
    simp only [zero_mul, mul_zero, polynomial.eval_zero, dvd_zero, smul_zero] },
end

private lemma p_fact_dvd_prod_part (n : ℕ) :  ∀ j : ℕ, ∀ k : ℕ, ∀ p : ℕ, p > 0 ->
  k > 0 -> k < n.succ ->
  (p.factorial:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (∏ i in finset.range n, (polynomial.X - polynomial.C (↑i + 1)) ^ p) j) :=
begin
  simp only [deriv_n],
  intros j,
  apply nat.case_strong_induction_on j,
  { intros k p hp hk1 hk2,
    convert dvd_zero _,
    obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero (ne_of_gt hk1),
    simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_one,
      function.iterate_zero_apply, polynomial.eval_prod, finset.prod_eq_zero_iff],
    use k,
    split,
    { rw nat.succ_lt_succ_iff at hk2, rwa [finset.mem_range] },
    { simp only [nat.succ_eq_add_one, add_sub_add_left_eq_sub, polynomial.eval_X,
        polynomial.eval_one, polynomial.eval_pow, zero_pow hp, polynomial.eval_nat_cast,
        nat.cast_add, polynomial.eval_add, nat.cast_one, polynomial.eval_sub, sub_self], } },


  intros j IH k p hp hk1 hk2,
  rw [function.iterate_succ_apply, finset.prod_pow, polynomial.derivative_pow,
    polynomial.iterate_derivative_mul, polynomial.eval_finset_sum],
  apply finset.dvd_sum,
  intros x hx,
  obtain rfl|h := (nat.succ_le_iff.mpr hp).eq_or_lt,
  { rw [nat.factorial_one, int.coe_nat_one], exact one_dvd _, },

  replace IH := IH (j-x) (nat.sub_le j x) k (p-1) (nat.sub_pos_of_lt h) hk1 hk2,
  rw [polynomial.eval_smul, nsmul_eq_mul],
  apply dvd_mul_of_dvd_right,
  rw [polynomial.eval_mul],
  apply dvd_mul_of_dvd_left,
  rw [polynomial.iterate_derivative_nat_cast_mul, polynomial.eval_mul, polynomial.eval_nat_cast],
  rw ←nat.mul_factorial_pred (pos_of_gt h),
  simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_one, int.coe_nat_mul],
  apply mul_dvd_mul, refl,
  simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_one] at IH ⊢,
  rw finset.prod_pow at IH, exact IH,
end

private lemma k_ge_1_case_when_j_ge_p (p : ℕ) (hp : nat.prime p) (n:ℕ) :
  ∀ j : ℕ, p ≤ j ->
    ∀ k : ℕ, k < n.succ -> k > 0 -> (p.factorial:ℤ) ∣ polynomial.eval (k:ℤ) (deriv_n (f_p p n) j) :=
begin
  intros j hj k hk1 hk2,
  rw [f_p, deriv_n, polynomial.iterate_derivative_mul, polynomial.eval_finset_sum],
  apply finset.dvd_sum,
  intros x hx,
  rw [polynomial.eval_smul, polynomial.eval_mul, nsmul_eq_mul],
  apply dvd_mul_of_dvd_right,
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


private lemma p_le (p m : ℕ) (hp : nat.prime p) : p ≤ ((m + 1) * p - 1).succ :=
begin
  apply nat.le_succ_of_pred_le,
  induction m with m IH,
  { simp only [one_mul, nat.pred_eq_sub_one] },
  rw nat.succ_eq_add_one, rw add_mul, simp only [one_mul],
  apply le_trans IH,
  have triv : m.succ * p + p - 1 = m.succ * p - 1 + p,
  { rw nat.sub_add_comm, apply nat.mul_pos, exact nat.succ_pos m, exact nat.prime.pos hp },
  rw triv, apply nat.le_add_right,
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

lemma finset.union_singleton {α : Type*} [decidable_eq α] {s : finset α} {a : α} :
  s ∪ {a} = insert a s :=
finset.union_comm _ _

theorem J_eq_final (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0) (p : ℕ) (hp : nat.prime p) :
  ∃ M : ℤ, (J g p) = int.cast_ring_hom ℝ ((-(g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.factorial) ^ p))) + (p.factorial:ℤ) * M) :=
begin
  have : p ≤ (f_p p g.nat_degree).nat_degree.succ,
  { rw deg_f_p _ hp,
    apply p_le _ _  hp },

  obtain ⟨c, eq3⟩ := J_partial_sum_rest g p hp,
  use -c,
  rw [J_eq'' g e_root_g p, ←ring_hom.map_neg, ←finset.sum_range_add_sum_Ico _ this, eq3,
    ←finset.sum_range_add_sum_Ico _ p.pred_le, nat.pred_eq_sub_one,
    J_partial_sum_from_one_to_p_sub_one g, zero_add, nat.Ico_pred_singleton hp.pos,
    finset.sum_singleton, J_partial_sum_from_p_sub_one_to_p g p hp, neg_add,
    neg_mul_eq_mul_neg ↑(p.factorial)],
end

theorem abs_J_lower_bound (g : ℤ[X]) (e_root_g : @polynomial.aeval ℤ ℝ _ _ _ e g = 0)
  (coeff_nonzero : (g.coeff 0) ≠ 0) (p : ℕ) (hp : nat.prime p)
  (hp2 : g.nat_degree < p  ∧ (g.coeff 0).nat_abs < p) :
  ((p-1).factorial:ℝ) ≤ (abs (J g p)) :=
begin
  obtain ⟨c, eq1⟩ := J_eq_final g e_root_g p hp,
  rw [eq1, ring_hom.eq_int_cast, ←int.cast_coe_nat, ←int.cast_abs, int.cast_le,
    ←nat.mul_factorial_pred hp.pos, int.coe_nat_mul],

  suffices : 1 ≤ abs (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) + ↑p * c),
  { convert le_mul_of_one_le_left (abs_nonneg ((p - 1).factorial : ℤ)) this,
    { rw int.coe_nat_abs },
    { rw [←abs_mul, int.coe_nat_pow],
      apply congr_arg,
      ring } },

  apply int.one_le_abs,
  intro rid,
  have rid2 : (p:ℤ) ∣ g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) + ↑p * c,
  rw rid, exact dvd_zero ↑p,

  rw [←dvd_add_iff_left (dvd_mul_right (p : ℤ) c), int.coe_nat_dvd_left, int.nat_abs_mul,
    int.nat_abs_mul, int.nat_abs_pow, int.nat_abs_neg, int.nat_abs_one, one_pow, one_mul,
    int.nat_abs_neg, hp.dvd_mul, int.nat_abs_of_nat] at rid2,
  cases rid2,
  { have ineq1 : (g.coeff 0).nat_abs > 0 := int.nat_abs_pos_of_ne_zero coeff_nonzero,
    exact hp2.2.not_le (nat.le_of_dvd ineq1 rid2) },
  { have H := nat.prime.dvd_of_dvd_pow hp rid2,
    rw [hp.dvd_factorial] at H,
    exact hp2.1.not_le H },
end

theorem eval_f_bar_mul (f g : ℤ[X]) (k : ℕ) : polynomial.eval (k:ℤ) (f_bar (f * g)) ≤ (polynomial.eval (k:ℤ) (f_bar f)) * (polynomial.eval (k:ℤ) (f_bar g)) :=
begin
  by_cases (f=0 ∨ g=0),
  { cases h, rw h, simp only [f_bar_0, zero_mul, polynomial.eval_zero], rw h, simp only [f_bar_0, mul_zero, polynomial.eval_zero] },
  replace h := not_or_distrib.1 h,
  rw [polynomial.as_sum_range (f_bar (f*g)), polynomial.eval_finset_sum, bar_same_deg,
    ←polynomial.eval_mul, polynomial.as_sum_range ((f_bar f)*(f_bar g))],
  have deg_eq : (f_bar f * f_bar g).nat_degree = f.nat_degree + g.nat_degree,
  { rw polynomial.nat_degree_mul, rw bar_same_deg, rw bar_same_deg, intro rid, exact h.1 (f_bar_eq_0 f rid), intro rid, exact h.2 (f_bar_eq_0 g rid) },
  rw deg_eq,
  replace deg_eq : (f * g).nat_degree = f.nat_degree + g.nat_degree,
  { rw polynomial.nat_degree_mul, intro rid, exact h.1 rid, intro rid, exact h.2 rid },
  rw [deg_eq, polynomial.eval_finset_sum], apply finset.sum_le_sum,
  intros x hx, simp only [polynomial.eval_X, polynomial.eval_C, polynomial.eval_pow, polynomial.eval_mul], rw coeff_f_bar_mul, rw polynomial.coeff_mul,
  cases k,
  { cases x,
    { simp only [mul_one, finset.nat.antidiagonal_zero, finset.sum_singleton, pow_zero],
      rw bar_coeff, rw bar_coeff, rw abs_mul },
    { simp only [int.coe_nat_zero, polynomial.eval_monomial, linear_map.map_sum, mul_zero,
        zero_pow (nat.succ_pos x), polynomial.eval_finset_sum],
      exact finset.sum_nonneg (λ i hi, le_rfl), } },

   { simp only [polynomial.eval_monomial, bar_coeff, ←abs_mul],
    refine mul_le_mul_of_nonneg_right (finset.abs_sum_le_sum_abs _ _) _,
    { apply pow_nonneg, norm_cast, exact bot_le } }
end

lemma f_bar_1 : f_bar 1 = 1 :=
begin
  ext, simp only [bar_coeff, polynomial.coeff_one, apply_ite abs, abs_zero, abs_one],
end


lemma eval_f_bar_nonneg (f : ℤ[X]) (i:ℕ) : 0 ≤ polynomial.eval (i:ℤ) (f_bar f) :=
begin
  rw [f_bar_eq, polynomial.eval_finset_sum],
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

private lemma f_bar_X_pow {n : ℕ} : f_bar (polynomial.X ^ n) = polynomial.X^n :=
begin
  ext, simp only [bar_coeff, polynomial.coeff_X_pow, apply_ite abs, abs_zero, abs_one],
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
  { norm_cast, apply self_le_pow_nat, assumption },
  { apply mul_le_mul,
    { apply mul_le_mul,
      { apply mul_le_mul,
        { norm_cast,
          have triv : max_abs_coeff_1 g = (max_abs_coeff_1 g) ^ 1,
          {simp only [pow_one]},
          conv_lhs {rw triv}, apply pow_le_pow, exact max_abs_coeff_1_ge_1 g, assumption },
        {norm_cast, apply self_le_pow_nat, assumption},
        {norm_cast, exact bot_le},
        {norm_cast, apply pow_nonneg, exact zero_le_max_abs_coeff_1 g} },
      { have triv : (g.nat_degree + 1:ℝ).exp = (g.nat_degree + 1:ℝ).exp ^ 1,
        { simp only [pow_one] },
        conv_lhs {rw triv}, apply pow_le_pow _ hp', by_contra rid, simp only [not_le] at rid,
        have ineq := (real.exp_lt_one_iff.1 rid), norm_cast at ineq, linarith },
      { have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq },
      { apply mul_nonneg,
        {norm_cast, apply pow_nonneg, exact zero_le_max_abs_coeff_1 g} ,
        { norm_cast, exact bot_le}} },
    {exact le_refl ((2 * (↑(polynomial.nat_degree g) + 1)) ^ (p + p * polynomial.nat_degree g))},
    {norm_cast, exact bot_le},
    { apply mul_nonneg,
      { apply mul_nonneg, {norm_cast, apply pow_nonneg, exact zero_le_max_abs_coeff_1 g},
        {norm_cast, exact bot_le} },
      {apply pow_nonneg, have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq} } },
  { apply mul_nonneg,
    { apply mul_nonneg,
      { apply mul_nonneg,
        {norm_cast, exact zero_le_max_abs_coeff_1 g},
        {norm_cast, exact bot_le} },
      {have ineq := real.exp_pos (↑(g.nat_degree) + 1), exact le_of_lt ineq} },
    {norm_cast, exact bot_le} },
  {norm_cast, exact bot_le},
end

/--
For an integer polynomial g = g0 + g1*X + ... + gn * X^n, we define
M = n * ((max_abs_coeff_1 g) * (n+1) * e^(n+1) * (2 * (n+1)) ^ (1 + n))

We use M to get an upperbound for |J(g,p)|
-/
def M (g : ℤ[X]) : ℝ := g.nat_degree.succ * ((max_abs_coeff_1 g) * (g.nat_degree + 1) * ((g.nat_degree:ℝ) + 1).exp * (2 * (g.nat_degree + 1)) ^ (1 + g.nat_degree))

lemma M_nonneg (g : ℤ[X]) : 0 ≤ M g :=
begin
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

theorem abs_J_upper_bound (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) : abs (J g p) ≤ (M g)^p :=
begin
  refine (abs_J_ineq1' g p).trans _,
  rw abs_J_ineq1'_coe g p hp,
  refine (sum_ineq_1 g p hp).trans _,
  rw M,
  have ineq4 := sum_ineq_2 g p hp,
  apply ineq4.trans_eq,
  have : p + p * g.nat_degree = (1 + g.nat_degree) * p, ring,
  rw [this, pow_mul],
  simp only [←mul_pow],
end

lemma fact_grows_fast' (M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N < n -> M ^ (n+1) < (n.factorial) :=
begin
obtain rfl|h := M.eq_zero_or_pos,
{ use 1, intros n hn, rw [zero_pow n.succ_pos], exact nat.factorial_pos n },
{ have H := complex.is_cau_exp (M:ℂ),
  have triv : (1/M:ℝ) > 0,
  {apply one_div_pos.2, norm_cast, exact h},
  obtain ⟨i, hi⟩ := is_cau_seq.cauchy₂ H triv,
  use i, intros n hn,
  have H3 := hi n.succ (nat.le_succ_of_le hn.le) n hn.le,
  dsimp only at H3,
  rwa [nat.succ_eq_add_one, finset.sum_range_add_sub_sum_range, finset.sum_range_one, add_zero,
    complex.abs_div, div_lt_div_iff, ←nat.cast_pow, complex.abs_cast_nat, complex.abs_cast_nat,
    one_mul, ←nat.cast_mul, ←pow_succ', nat.cast_lt] at H3,
  { rw [complex.abs_pos, nat.cast_ne_zero],
    exact nat.factorial_ne_zero _ },
  { rwa nat.cast_pos } },
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


theorem coup_de_grace (M : ℝ) (hM : 0 ≤ M) (z : ℤ) :
  ∃ p : ℕ, nat.prime p ∧ z < (p:ℤ) ∧ M^p < ((p - 1).factorial:ℝ) :=
begin
  obtain ⟨N, hN⟩ := fact_grows_fast M hM,
  obtain ⟨p, Hp, pp⟩ := nat.exists_infinite_primes (max (N+2) (z.nat_abs+1)),
  refine ⟨p, pp, _, _⟩,
  { calc z ≤ z.nat_abs : int.le_nat_abs
    ... < z.nat_abs + 1 : int.lt_succ _
    ... ≤ ↑(max (N + 2) (z.nat_abs + 1)) : by exact_mod_cast le_max_right _ _
    ... ≤ p : int.coe_nat_le.mpr Hp },
  { convert hN (p - 1) _,
    { exact (nat.sub_add_cancel pp.one_lt.le).symm },
    { apply lt_tsub_of_add_lt_right ,
      rw ←nat.succ_le_iff,
      exact le_trans (le_max_left _ _) Hp } }
end

lemma polynomial.exists_coeff_ne_zero {R : Type*} [semiring R] {p : R[X]} (hp : p ≠ 0) :
  ∃ n, p.coeff n ≠ 0 :=
begin
  contrapose! hp,
  simpa [polynomial.ext_iff],
end

theorem non_empty_supp (f : ℤ[X]) (hf : f ≠ 0) : f.support.nonempty :=
begin
  simp_rw [finset.nonempty, polynomial.mem_support_iff],
  exact polynomial.exists_coeff_ne_zero hf,
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

theorem transform_eq (f : ℤ[X]) (hf : f ≠ 0) : f = (make_const_term_nonzero f hf) * (polynomial.X) ^ (min_degree_term f hf) :=
begin
  ext,
  rw [polynomial.coeff_mul_X_pow', coeff_after_change],
  split_ifs,
  { rw nat.sub_add_cancel h },
  { rw ←polynomial.not_mem_support_iff,
    contrapose! h,
    rw min_degree_term,
    exact f.support.min'_le _ h },
end

theorem non_zero_root_same (f : ℤ[X]) (hf : f ≠ 0) (r : ℝ) (r_nonzero : r ≠ 0) (root_r : @polynomial.aeval ℤ ℝ _ _ _ r f = 0) :
  (@polynomial.aeval ℤ ℝ _ _ _ r) (make_const_term_nonzero f hf) = 0 :=
begin
  have eq1 := transform_eq f hf, rw eq1 at root_r, simp only [polynomial.aeval_X, alg_hom.map_pow, alg_hom.map_mul, mul_eq_zero] at root_r,
  cases root_r, exact root_r, replace root_r := pow_eq_zero root_r, exfalso, exact r_nonzero root_r,
end

theorem e_transcendental : transcendental ℤ e :=
begin
  intro e_algebraic,
  rw is_algebraic at e_algebraic,
  obtain ⟨g', g'_nonzero, e_root_g'⟩ := e_algebraic,
  generalize g_def : make_const_term_nonzero g' g'_nonzero = g,
  have coeff_zero_nonzero : (g.coeff 0) ≠ 0,
  { rw <-g_def, apply coeff_zero_after_change },
  have e_root_g : (@polynomial.aeval ℤ ℝ _ _ _ e) g = 0,
  { rw <-g_def,
    exact non_zero_root_same _ _ _  (1:ℝ).exp_ne_zero e_root_g' },
  obtain ⟨p, pp, Hp1, Hp2⟩ := coup_de_grace (M g) (M_nonneg g) (max g.nat_degree (abs (g.coeff 0))),
  apply lt_irrefl (M g ^ p),
  simp only [gt_iff_lt, max_lt_iff, int.coe_nat_lt, int.abs_eq_nat_abs] at Hp1,
  calc M g ^ p < ((p - 1).factorial : ℝ) : Hp2
  ... ≤ |J g p| : abs_J_lower_bound g e_root_g coeff_zero_nonzero p pp Hp1
  ... ≤ M g ^ p : abs_J_upper_bound g p pp,
end

theorem e_pow_transcendental (n : ℕ) (hn : 1 ≤ n) : transcendental ℤ (e^n) :=
e_transcendental.pow hn

theorem transcendental_irrational {x : ℝ} (trans_x : transcendental ℤ x) : irrational x :=
transcendental.irrational $ (transcendental_iff_transcendental_over_ℚ x).mp trans_x

theorem e_irrational : irrational e := transcendental_irrational e_transcendental

theorem e_pow_n_irrational (n : ℕ) (hn : 1 ≤ n) : irrational (e ^ n) := transcendental_irrational (e_pow_transcendental n hn)
