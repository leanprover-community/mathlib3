/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.algebraic
import analysis.transcendental.e_transcendental_lemmas
import analysis.transcendental.basic
import data.polynomial.derivative
import data.real.irrational

/-!
TODO
-/

noncomputable theory
open e_transcendental_lemmas polynomial
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
def f_p (p : ℕ) (n : ℕ): ℤ[X] := X ^ (p - 1) * (∏ i in finset.range n, (X - (C (i+1:ℤ)))^p)

lemma deg_f_p (p : ℕ) (hp : 1 ≤ p) (n : ℕ) : (f_p p n).nat_degree + 1 = (n + 1) * p :=
begin
  rw [f_p, nat_degree_mul, nat_degree_X_pow, nat_degree_prod],
  simp only [nat_degree_pow, nat_degree_X_sub_C, finset.sum_const,
    finset.card_range, smul_eq_mul, mul_one],
  rw [add_comm (p - 1), add_assoc, nat.sub_add_cancel hp, add_one_mul],
  { exact λ i hi, pow_ne_zero _ (X_sub_C_ne_zero _), },
  { exact pow_ne_zero _ X_ne_zero },
  { rw finset.prod_ne_zero_iff,
    exact λ i hi, pow_ne_zero _ (X_sub_C_ne_zero _), },
end

/--
Definition
For a prime number $p$ and a polynomial $g$
$$J_p(g):= \sum_{i=0}^d g_i I(f_{p,d},i)$$ where $d$ is the degree of $g$.
-/
def J (g : ℤ[X]) (p : ℕ) : ℝ :=
  ∑ i in finset.range g.nat_degree.succ, (g.coeff i : ℝ) * (II (f_p p g.nat_degree) i)

/--
Auxiliary definition used in proving an equality for `J` (`J_eq_final`)
-/
def H (g : ℤ[X]) (p j : ℕ) : ℤ :=
  ∑ i in finset.range g.nat_degree.succ, g.coeff i *
    (derivative^[j] (f_p p g.nat_degree)).eval i
/--
Theorem
$$J_{p}(g) =
  \sum_{i=0}^d g_i\left(
    e^i\sum_{j=0}^{(n+1)p-1} f_{p,d}^{(j)}(0)-\sum_{j=0}^{(n+1)p-1}f_{p,d}^{(j)}(i)
  \right)$
-/
private lemma J_eq1 (g : ℤ[X]) (p : ℕ) :
  J g p = ∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p g.nat_degree) i) :=
begin
  rw J, apply congr_arg, ext, rw II_eq_I,
end

private lemma J_eq2' (g : ℤ[X]) (p : ℕ) (k : ℕ) :
  (g.coeff k:ℝ) * (I (f_p p g.nat_degree) k) =
  (g.coeff k:ℝ) * ((k:ℝ).exp *
    (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
      (aeval (0 : ℝ) (derivative^[j] (f_p p g.nat_degree))))) -
  (g.coeff k:ℝ) * (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
    (aeval (k : ℝ) (derivative^[j] (f_p p g.nat_degree)))) :=
begin
  rw ←mul_sub, rw I,
end

private lemma J_eq2 (g : ℤ[X]) (p : ℕ) :
  (∑ i in finset.range g.nat_degree.succ, (g.coeff i:ℝ) * (I (f_p p g.nat_degree) i)) =
  (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp *
    (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
      (aeval (0 : ℝ) (derivative^[j] (f_p p g.nat_degree))))) -
  (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) *
    (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
      (aeval (k : ℝ) (derivative^[j] (f_p p g.nat_degree)))))) :=
begin
  rw ←finset.sum_sub_distrib, apply congr_arg, ext i, rw J_eq2',
end

private lemma J_eq3 (g : ℤ[X]) (e_root_g : aeval e g = 0) (p : ℕ) :
  (∑ k in finset.range g.nat_degree.succ, (g.coeff k:ℝ) * ((k:ℝ).exp *
    (∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ,
      (aeval (0 : ℝ) (derivative^[j] (f_p p g.nat_degree)))))) = 0 :=
begin
  simp_rw ←mul_assoc,
  rw ←finset.sum_mul,
  convert zero_mul _,
  rw [aeval_def, eval₂, sum_over_range] at e_root_g,
  { convert e_root_g using 1,
    apply finset.sum_congr rfl (λ a ha, _),
    simp [e, ←real.exp_nat_mul] },
  { simp },
end

theorem J_eq' (g : ℤ[X]) (e_root_g : aeval e g = 0) (p : ℕ) :
  J g p = - ∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, H g p j :=
begin
  rw [J_eq1, J_eq2, J_eq3 _ e_root_g, zero_sub],
  simp_rw [finset.mul_sum, H],
  rw [finset.sum_comm],
  simp_rw [int.cast_sum, int.cast_mul, aeval_nat_cast', algebra_map_int_eq, eq_int_cast],
end

theorem J_eq'' (g : ℤ[X]) (e_root_g : aeval e g = 0) (p : ℕ) :
  J g p = -↑(∑ j in finset.range (f_p p g.nat_degree).nat_degree.succ, H g p j) :=
(J_eq' _ e_root_g _).trans $ congr_arg _ $ (int.cast_sum _ _).symm

lemma deriv_f_p_k_eq_zero_k_eq_0_when_j_lt_p_sub_one (p : ℕ) (n j : ℕ) (hj : j < p - 1) :
  eval 0 (derivative^[j] (f_p p n)) = 0 :=
begin
  rw [f_p, iterate_derivative_mul, eval_finset_sum],
  refine finset.sum_eq_zero (λ i hi, _),
  rw [finset.mem_range] at hi,
  rw [eval_smul, smul_eq_zero],
  right,
  have ineq : j - i < p - 1 := gt_of_gt_of_ge hj (nat.sub_le j i),
  rw [eval_mul, mul_eq_zero], left,
  rw [iterate_derivative_X_pow_eq_C_mul, eval_mul],
  apply mul_eq_zero_of_right,
  rw [eval_pow, eval_X],
  apply zero_pow,
  exact nat.sub_pos_of_lt ineq,
end

lemma finset.prod_neg
  {α β : Type*} [comm_ring α] (s : finset β) (f : β → α) :
    ∏ x in s, -f x = (-1) ^ s.card * ∏ x in s, f x :=
by simp_rw [←finset.prod_const, ←finset.prod_mul_distrib, neg_one_mul]

lemma nat.sub_sub_comm (a b c : ℕ) : a - b - c = a - c - b :=
by rw [nat.sub_sub, add_comm, ←nat.sub_sub]

theorem deriv_f_p_zero_when_j_eq_p_sub_one (p : ℕ) (hp : 1 < p) (n : ℕ) :
  eval 0 (derivative^[p - 1] (f_p p n)) = (p-1).factorial * (-1)^(n*p)*(n.factorial)^p :=
begin
  rw [f_p, iterate_derivative_mul, eval_finset_sum],
  rw finset.sum_eq_single 0,
  { rw [mul_assoc, nat.choose_zero_right, one_smul, eval_mul],
    congr' 1,
    { rw [tsub_zero, iterate_derivative_X_pow_eq_smul,
        tsub_self, pow_zero, eval_smul, eval_one,
        int.smul_one_eq_coe, int.cast_coe_nat, nat.desc_factorial_self] },
    { rw [function.iterate_zero_apply, finset.prod_pow, eval_pow,
        eval_prod],
      simp_rw [eval_sub, eval_X, eval_C, zero_sub],
      rw [finset.prod_neg, finset.card_range, mul_pow, pow_mul,
        ←finset.prod_range_add_one_eq_factorial, nat.cast_prod],
      simp_rw [nat.cast_add, nat.cast_one] } },

  { intros i hi1 hi2,
    have : 0 < p - 1 - (p - 1 - i),
    { apply nat.sub_pos_of_lt, apply nat.sub_lt,
      { apply nat.sub_pos_of_lt hp },
      { exact nat.pos_of_ne_zero hi2 } },
    simp only [nat.cast_prod, int.cast_coe_nat, eval_X, int.cast_prod, int.cast_add,
      eq_int_cast, iterate_derivative_X_pow_eq_smul, zero_mul,
      eval_pow, nsmul_eq_mul, eq_self_iff_true, int.cast_one, eval_mul,
      eval_nat_cast, finset.prod_congr, mul_zero, zsmul_eq_mul, zero_pow this], },
  { intro rid, exfalso, simp only [nat.succ_pos', not_true, finset.mem_range] at rid, exact rid },
end

lemma deriv_f_p_when_j_lt_p (p : ℕ) (n : ℕ) : ∀ x : ℕ, ∀ j : ℕ, j < p →
  0 < x → x < n.succ → eval (x:ℤ) (derivative^[j] (f_p p n)) = 0 :=
begin
  induction n with n IH,
  { intros x j hj hx1 hx2,
    linarith },
  { intros x j hj hx1 hx2,
    rw [f_p, finset.prod_range_succ, ←mul_assoc, iterate_derivative_mul,
      eval_finset_sum, ←f_p],
    refine finset.sum_eq_zero (λ y hy, _),
    simp only [finset.mem_range] at hy,
    rw [eval_smul],
    obtain hx2|rfl := nat.lt_succ_iff_lt_or_eq.mp hx2,
    { have := IH x (j-y) (gt_of_gt_of_ge hj (nat.sub_le j y)) hx1 hx2,
      rw [eval_mul, this, zero_mul, smul_zero] },
    { rw [iterate_derivative_X_sub_pow, eval_mul, eval_mul,
        eval_pow],
      simp only [eval_X, eval_C, int.coe_nat_succ, eval_sub,
        sub_self, zero_pow (nat.sub_pos_of_lt (gt_of_ge_of_gt hj hy)),
        mul_zero, smul_zero, eq_self_iff_true] } },
end

theorem deriv_f_p_k_eq_zero_when_j_lt_p_sub_one
  (p : ℕ) (n j : ℕ) (hj : j < p - 1) (k : ℕ) (hk : k ∈ finset.range n.succ) :
  eval (k : ℤ) (derivative^[j] (f_p p n)) = 0 :=
begin
  cases k,
  { exact deriv_f_p_k_eq_zero_k_eq_0_when_j_lt_p_sub_one p n j hj },
  { exact deriv_f_p_when_j_lt_p p n k.succ j (nat.lt_of_lt_pred hj) (nat.succ_pos k)
      (finset.mem_range.mp hk) },
end

private lemma k_eq_0_case_when_j_ge_p (p : ℕ) (hp : nat.prime p) (n j : ℕ) (j_ge_p : p ≤ j) :
  (p.factorial : ℤ) ∣ eval 0 (derivative^[j] (f_p p n)) :=
begin
  rw [f_p, iterate_derivative_mul, eval_finset_sum],
  apply finset.dvd_sum,
  intros x hx,
  simp only [eval_C, C_add, C_1, eval_mul, nat.factorial],
  obtain h|h|h := lt_trichotomy (j - x) (p - 1),
  { rw [iterate_derivative_X_pow_eq_C_mul (p - 1) (j - x), eval_smul,
      eval_mul, eval_mul_X_pow, zero_pow (nat.sub_pos_of_lt h), mul_zero,
      zero_mul, smul_zero],
    exact dvd_zero _ },
  { rw [h, iterate_derivative_X_pow_eq_C_mul],
    simp only [nat.cast_prod, int.cast_coe_nat, int.cast_prod, mul_one, eq_int_cast,
      eval_prod, nat.sub_self, nsmul_eq_mul, eval_mul,
      C_eq_nat_cast, eval_nat_cast, finset.prod_congr, pow_zero],
    suffices : (p:ℤ) ∣ eval 0
      (derivative^[x] (∏ (x : ℕ) in finset.range n, (X - (↑x + 1)) ^ p)),
    { obtain ⟨c, hc⟩ := this,
      rw [hc],
      convert dvd_mul_right _ (c * (j.choose x)) using 1,
      rw [←nat.mul_factorial_pred hp.pos, int.coe_nat_mul, nat.desc_factorial_self],
      ring },
    have : x ≠ 0,
    { rintro rfl,
      rw nat.sub_zero at h,
      rw h at j_ge_p,
      exact j_ge_p.not_lt (nat.sub_lt_of_pos_le _ _ one_pos hp.one_lt.le) },
    rw finset.prod_pow,
    exact dvd_iterate_derivative_pow _ _ _ this },
  { rw [iterate_derivative_eq_zero ((nat_degree_X_pow_le _).trans_lt h)],
    simp only [zero_mul, mul_zero, eval_zero, dvd_zero, smul_zero] },
end

private lemma p_fact_dvd_prod_part (n : ℕ) :  ∀ j : ℕ, ∀ k : ℕ, ∀ p : ℕ, p > 0 →
  k > 0 → k < n.succ →
  (p.factorial:ℤ) ∣ eval (k:ℤ) (derivative^[j] (∏ i in finset.range n, (X - C (↑i + 1)) ^ p)) :=
begin
  intros j,
  apply nat.case_strong_induction_on j,
  { intros k p hp hk1 hk2,
    convert dvd_zero _,
    obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero (ne_of_gt hk1),
    simp only [int.cast_coe_nat, int.cast_add, eq_int_cast, int.cast_one,
      function.iterate_zero_apply, eval_prod, finset.prod_eq_zero_iff],
    use k,
    split,
    { rw nat.succ_lt_succ_iff at hk2, rwa [finset.mem_range] },
    { simp only [nat.succ_eq_add_one, add_sub_add_left_eq_sub, eval_X,
        eval_one, eval_pow, zero_pow hp, eval_nat_cast,
        nat.cast_add, eval_add, nat.cast_one, eval_sub, sub_self], } },


  intros j IH k p hp hk1 hk2,
  rw [function.iterate_succ_apply, finset.prod_pow, derivative_pow,
    iterate_derivative_mul, eval_finset_sum],
  apply finset.dvd_sum,
  intros x hx,
  obtain rfl|h := (nat.succ_le_iff.mpr hp).eq_or_lt,
  { rw [nat.factorial_one, int.coe_nat_one], exact one_dvd _, },

  replace IH := IH (j-x) (nat.sub_le j x) k (p-1) (nat.sub_pos_of_lt h) hk1 hk2,
  rw [eval_smul, nsmul_eq_mul],
  apply dvd_mul_of_dvd_right,
  rw [eval_mul],
  apply dvd_mul_of_dvd_left,
  rw [iterate_derivative_nat_cast_mul, eval_mul, eval_nat_cast],
  rw ←nat.mul_factorial_pred (pos_of_gt h),
  simp only [int.cast_coe_nat, int.cast_add, int.cast_one, int.coe_nat_mul, ←finset.prod_pow],
  exact mul_dvd_mul_left _ IH,
end

private lemma k_ge_1_case_when_j_ge_p (p : ℕ) (hp : nat.prime p) (n j : ℕ) (hj : p ≤ j) (k : ℕ)
  (hk1 : k < n.succ) (hk2 : k > 0) :
  (p.factorial:ℤ) ∣ eval (k:ℤ) (derivative^[j] (f_p p n)) :=
begin
  rw [f_p, iterate_derivative_mul, eval_finset_sum],
  apply finset.dvd_sum,
  intros x hx,
  rw [eval_smul, eval_mul, nsmul_eq_mul],
  apply dvd_mul_of_dvd_right,
  apply dvd_mul_of_dvd_right,
  apply p_fact_dvd_prod_part n _ _ _ (nat.prime.pos hp) hk2 hk1,
end

theorem when_j_ge_p_k (p : ℕ) (hp : nat.prime p) (n j : ℕ) (j_ge_p : p ≤ j) (k : ℕ)
  (hk : k ∈ finset.range n.succ) :
  (p.factorial:ℤ) ∣ eval (k:ℤ) (derivative^[j] (f_p p n)) :=
begin
  simp only [finset.mem_range] at hk,
  cases k,
  { exact k_eq_0_case_when_j_ge_p p hp n j j_ge_p },
  { exact k_ge_1_case_when_j_ge_p p hp n j j_ge_p k.succ hk (nat.succ_pos k) },
end

theorem J_partial_sum_from_one_to_p_sub_one (g : ℤ[X]) (p : ℕ) :
  ∑ (j : ℕ) in finset.range (p - 1), H g p j = 0 :=
begin
  refine finset.sum_eq_zero (λ x hx, _),
  rw finset.mem_range at hx,
  rw H,
  refine finset.sum_eq_zero (λ i hi, _),
  exact mul_eq_zero_of_right _ (deriv_f_p_k_eq_zero_when_j_lt_p_sub_one _ _ _ hx _ hi),
end

theorem J_partial_sum_from_p_sub_one_to_p (g : ℤ[X]) (p : ℕ) (hp : 1 < p) :
  H g p (p - 1) =
  g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) * ↑(g.nat_degree.factorial) ^ p) :=
begin
  rw [H, finset.sum_eq_single 0],

  { simp only [int.coe_nat_zero],
    rw deriv_f_p_zero_when_j_eq_p_sub_one p hp g.nat_degree, },

  { intros i hi1 hi2, rw mul_eq_zero, right,
    apply deriv_f_p_when_j_lt_p p g.nat_degree,
    { apply nat.sub_lt (pos_of_gt hp), exact nat.one_pos },
    { exact nat.pos_of_ne_zero hi2 },
    { exact finset.mem_range.mp hi1 } },

  { intro rid, apply (rid _).elim, simp only [nat.succ_pos', not_true, finset.mem_range] },
end

theorem J_partial_sum_rest (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  (p.factorial:ℤ) ∣
    ∑ (j : ℕ) in finset.Ico p (f_p p g.nat_degree).nat_degree.succ, H g p j :=
begin
  apply finset.dvd_sum, intros x hx, apply finset.dvd_sum, intros y hy,
  apply dvd_mul_of_dvd_right,
  apply when_j_ge_p_k _ hp _ _ _ _ hy,
  simp only [finset.mem_Ico] at hx, exact hx.1,
end

lemma finset.union_singleton {α : Type*} [decidable_eq α] {s : finset α} {a : α} :
  s ∪ {a} = insert a s :=
finset.union_comm _ _

theorem J_eq_split (g : ℤ[X]) (p : ℕ) (hroot : aeval e g = 0) (hp : nat.prime p) :
  J g p = -↑(
    ∑ j in finset.range (p - 1), H g p j +
    H g p (p - 1) +
    ∑ j in finset.Ico (p) (f_p p g.nat_degree).nat_degree.succ, H g p j) :=
begin
  have : p ≤ (f_p p g.nat_degree).nat_degree + 1,
  { rw deg_f_p _ hp.one_lt.le,
    exact nat.le_mul_of_pos_left (nat.succ_pos _) },
  rw [←finset.sum_range_succ, nat.sub_add_cancel hp.one_lt.le, finset.sum_range_add_sum_Ico _ this,
    J_eq'' _ hroot],
end

theorem J_eq_final (g : ℤ[X]) (e_root_g : aeval e g = 0) (p : ℕ) (hp : nat.prime p) :
  ∃ M : ℤ, (J g p) = ↑(
    (-(g.coeff 0 * (↑((p - 1).factorial) * (-1) ^ (g.nat_degree * p) *
        ↑(g.nat_degree.factorial) ^ p))) +
    (p.factorial:ℤ) * M) :=
begin
  rw J_eq_split _ _ e_root_g hp,
  obtain ⟨c, eq3⟩ := J_partial_sum_rest g p hp,
  use -c,
  rw [eq3, J_partial_sum_from_one_to_p_sub_one g, J_partial_sum_from_p_sub_one_to_p g p hp.one_lt,
    ←int.cast_neg, zero_add, ←neg_mul_eq_mul_neg, neg_add],
end

theorem abs_J_lower_bound (g : ℤ[X]) (e_root_g : aeval e g = 0)
  (coeff_nonzero : (g.coeff 0) ≠ 0) (p : ℕ) (hp : nat.prime p)
  (hp2 : g.nat_degree < p  ∧ (g.coeff 0).nat_abs < p) :
  ((p-1).factorial:ℝ) ≤ (abs (J g p)) :=
begin
  obtain ⟨c, eq1⟩ := J_eq_final g e_root_g p hp,
  rw [eq1, ←int.cast_coe_nat, ←int.cast_abs, int.cast_le,
    ←nat.mul_factorial_pred hp.pos, int.coe_nat_mul],

  suffices :
    1 ≤ abs (g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) + ↑p * c),
  { convert le_mul_of_one_le_left (abs_nonneg ((p - 1).factorial : ℤ)) this,
    { rw int.coe_nat_abs },
    { rw [←abs_mul, int.coe_nat_pow],
      apply congr_arg,
      ring } },

  apply int.one_le_abs,
  intro rid,
  have rid2 :
    (p:ℤ) ∣ g.coeff 0 * ((-1) ^ (g.nat_degree * p) * -↑(g.nat_degree.factorial ^ p)) + ↑p * c,
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

theorem abs_J_ineq1' (g : ℤ[X]) (p : ℕ) :
  abs (J g p) ≤ ∑ i in finset.range g.nat_degree.succ,
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * (aeval (i : ℝ) (f_bar (f_p p g.nat_degree))) :=
begin
  refine (finset.abs_sum_le_sum_abs _ _).trans _,
  refine finset.sum_le_sum (λ x hx, _),
  rw [abs_mul, mul_assoc, mul_assoc],
  refine mul_le_mul_of_nonneg_left _ (abs_nonneg _),
  rw [←mul_assoc],
  exact abs_II_le2 (f_p p g.nat_degree) (x:ℝ) x.cast_nonneg,
end

lemma f_p_bar_est (g : ℤ[X]) (p : ℕ) (j : ℕ) (hi : j < g.nat_degree.succ) :
  eval (j:ℤ) (f_bar (f_p p g.nat_degree)) ≤
    (2 * g.nat_degree.succ : ℤ) ^ (p + p * g.nat_degree) :=
begin
  rw [pow_add, pow_mul, finset.pow_eq_prod_const _ g.nat_degree],
  refine (eval_f_bar_mul _ _ _).trans (mul_le_mul _ _ _ _),
  { simp only [f_bar_X_pow, eval_X, eval_pow],
    norm_cast,
    calc j ^ (p - 1)
        ≤ (2 * g.nat_degree.succ) ^ (p - 1)
          : nat.pow_le_pow_of_le_left (hi.le.trans (nat.le_mul_of_pos_left two_pos)) _
    ... ≤ (2 * g.nat_degree.succ) ^ p
          : nat.pow_le_pow_of_le_right (mul_pos two_pos (nat.succ_pos _)) p.pred_le },
  { apply (eval_f_bar_prod _ _ _).trans,
    refine finset.prod_le_prod (λ _ _, eval_f_bar_nonneg _ _) (λ x hx, _),
    rw [finset.mem_range] at hx,
    refine (eval_f_bar_pow _ _ _).trans _,
    rw f_bar_X_sub_C,
    swap, exact_mod_cast bot_le,

    simp only [eval_X, eval_C, eval_add],
    norm_cast,
    apply nat.pow_le_pow_of_le_left,
    rw two_mul,
    exact add_le_add hi.le (nat.le_succ_of_le hx) },
  { exact (eval_f_bar_nonneg _ _) },
  { exact_mod_cast bot_le }
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
  rw max_abs_coeff_1, apply finset.le_max', rw set_of_1_abs_coeff,
  simp only [true_or, eq_self_iff_true, finset.mem_insert],
end

lemma zero_le_max_abs_coeff_1 (g : ℤ[X]) : 0 ≤ max_abs_coeff_1 g :=
zero_le_one.trans $ max_abs_coeff_1_ge_1 g

lemma sum_ineq_1 (g : ℤ[X]) (p : ℕ) :
  ((∑ i in finset.range g.nat_degree.succ,
    (abs (g.coeff i:ℝ)) * (i : ℝ) * (i:ℝ).exp * aeval (i : ℝ) (f_bar (f_p p g.nat_degree)))) ≤
  (g.nat_degree.succ:ℝ) *
      (↑(max_abs_coeff_1 g) * (↑(g.nat_degree) + 1) * ((g.nat_degree:ℝ) + 1).exp *
         (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) :=
begin
  refine (finset.sum_le_card_nsmul (finset.range g.nat_degree.succ) _
    ((max_abs_coeff_1 g:ℝ) * (g.nat_degree.succ : ℝ) * (g.nat_degree.succ:ℝ).exp *
      ((2 * ↑(g.nat_degree.succ)) ^ (p + p * g.nat_degree))) (λ x H, _)).trans_eq _,
  { simp only [finset.mem_range] at H,
    rw [aeval_nat_cast', eq_int_cast],
    by_cases hx : x ∈ g.support,
    { apply mul_le_mul,
      { apply mul_le_mul,
        { norm_cast,
          apply mul_le_mul,
          { rw max_abs_coeff_1, apply finset.le_max', rw set_of_1_abs_coeff,
            apply finset.mem_insert_of_mem,
            rw [set_of_abs_coeff, finset.mem_image],
            exact ⟨x, hx, rfl⟩ },
          { norm_cast, exact le_of_lt H },
          { norm_cast, exact bot_le },
          { exact zero_le_max_abs_coeff_1 g } },
        { rw real.exp_le_exp, norm_cast, exact le_of_lt H },
        { exact (real.exp_pos _).le },
        { norm_cast, apply mul_nonneg,
          { exact zero_le_max_abs_coeff_1 g },
          { norm_cast, exact bot_le } } },
      { exact_mod_cast f_p_bar_est g p x H },
      { norm_cast, exact eval_f_bar_nonneg (f_p p (nat_degree g)) x },
      apply mul_nonneg,
      { apply mul_nonneg,
        { norm_cast, exact zero_le_max_abs_coeff_1 g },
        { norm_cast, exact bot_le } },
      { exact (real.exp_pos _).le } },
    have hx' : g.coeff x = 0,
    { rwa ←not_mem_support_iff },
    simp only [hx', int.cast_zero, zero_mul, abs_zero, nat.cast_succ],
    apply mul_nonneg,
    { apply mul_nonneg,
      { apply mul_nonneg,
        { norm_cast, exact zero_le_max_abs_coeff_1 g },
        { norm_cast, exact bot_le } },
      { exact (real.exp_pos _).le } },
    { apply pow_nonneg,
      refine mul_nonneg zero_le_two _,
      norm_cast, exact bot_le } },
  { rw [nsmul_eq_mul, finset.card_range, ←nat.cast_succ] },
end

lemma self_le_pow_nat (n m : ℕ) (hm : 1 ≤ m) : n ≤ n ^ m :=
begin
  cases n,
  { simp only [zero_le] },
  { exact le_self_pow n.succ_pos hm },
end

lemma sum_ineq_2 (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) :
  (g.nat_degree.succ : ℝ) *
  (↑(max_abs_coeff_1 g) * (↑(g.nat_degree) + 1) * ((g.nat_degree:ℝ) + 1).exp *
    (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) ≤
  (g.nat_degree.succ : ℝ) ^ p *
  (↑(max_abs_coeff_1 g) ^ p * (↑(g.nat_degree) + 1) ^ p * ((g.nat_degree:ℝ) + 1).exp ^ p *
    (2 * (↑(g.nat_degree) + 1)) ^ (p + p * g.nat_degree)) :=
begin
  have hp' := hp.one_lt.le,
  apply mul_le_mul,
  { norm_cast, apply self_le_pow_nat _ _ hp' },
  { apply mul_le_mul_of_nonneg_right,
    { apply mul_le_mul,
      { apply mul_le_mul,
        { norm_cast,
          have triv : max_abs_coeff_1 g = (max_abs_coeff_1 g) ^ 1,
          { simp only [pow_one] },
          conv_lhs {rw triv}, apply pow_le_pow (max_abs_coeff_1_ge_1 g) hp' },
        { norm_cast, apply self_le_pow_nat _ _ hp', },
        { norm_cast, exact bot_le },
        { norm_cast, apply pow_nonneg (zero_le_max_abs_coeff_1 g) _ } },
      { have triv : (g.nat_degree + 1:ℝ).exp = (g.nat_degree + 1:ℝ).exp ^ 1,
        { simp only [pow_one] },
        conv_lhs {rw triv}, apply pow_le_pow (real.one_le_exp _) hp', exact_mod_cast bot_le },
      { exact (real.exp_pos _).le },
      { apply mul_nonneg,
        { norm_cast, apply pow_nonneg, exact zero_le_max_abs_coeff_1 g } ,
        { norm_cast, exact bot_le}} },
    { norm_cast, exact bot_le } },
  { apply mul_nonneg,
    { apply mul_nonneg,
      { apply mul_nonneg,
        { norm_cast, exact zero_le_max_abs_coeff_1 g },
        { norm_cast, exact bot_le } },
      { exact (real.exp_pos _).le } },
    { norm_cast, exact bot_le } },
  { norm_cast, exact bot_le },
end

/--
For an integer polynomial g = g0 + g1*X + ... + gn * X^n, we define
M = n * ((max_abs_coeff_1 g) * (n+1) * e^(n+1) * (2 * (n+1)) ^ (1 + n))

We use M to get an upperbound for |J(g,p)|
-/
def M (g : ℤ[X]) : ℝ :=
  g.nat_degree.succ *
  ((max_abs_coeff_1 g) * (g.nat_degree + 1) *
    ((g.nat_degree:ℝ) + 1).exp * (2 * (g.nat_degree + 1)) ^ (1 + g.nat_degree))

lemma M_nonneg (g : ℤ[X]) : 0 ≤ M g :=
begin
  rw M,
  apply mul_nonneg,
  { norm_cast, exact bot_le },
  apply mul_nonneg,
  { apply mul_nonneg,
    { norm_cast, apply mul_nonneg,
      { exact zero_le_max_abs_coeff_1 g },
      { norm_cast, exact bot_le } },
    { have triv : (g.nat_degree + 1 : ℝ).exp > 0 := (g.nat_degree + 1:ℝ).exp_pos,
      exact le_of_lt triv } },
  { apply pow_nonneg,
    apply mul_nonneg,
    { exact zero_le_two },
    { norm_cast, exact bot_le }, }
end

theorem abs_J_upper_bound (g : ℤ[X]) (p : ℕ) (hp : nat.prime p) : abs (J g p) ≤ (M g)^p :=
begin
  rw M,
  refine (abs_J_ineq1' g p).trans _,
  refine (sum_ineq_1 g p).trans _,
  refine (sum_ineq_2 g p hp).trans_eq _,
  simp only [mul_pow],
  simp_rw [←pow_mul', mul_add, mul_one],
end

lemma fact_grows_fast' (M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N < n → M ^ (n+1) < (n.factorial) :=
begin
  obtain rfl|h := M.eq_zero_or_pos,
  { use 1, intros n hn, rw [zero_pow n.succ_pos], exact nat.factorial_pos n },
  { have H := complex.is_cau_exp (M:ℂ),
    have triv : (1/M:ℝ) > 0,
    { apply one_div_pos.2, norm_cast, exact h },
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

lemma fact_grows_fast (M : ℝ) (hM : 0 ≤ M) :
  ∃ N : ℕ, ∀ n : ℕ, N < n → M ^ (n + 1) < (n.factorial : ℝ) :=
begin
  obtain ⟨M', hM'⟩ := exists_nat_gt M,
  obtain ⟨N, hN⟩ := fact_grows_fast' M',
  refine ⟨N, λ n hn, _⟩,
  apply (pow_lt_pow_of_lt_left hM' hM n.succ_pos).trans,
  exact_mod_cast hN n hn,
end


theorem coup_de_grace (M : ℝ) (hM : 0 ≤ M) (z : ℤ) :
  ∃ p : ℕ, nat.prime p ∧ z < (p : ℤ) ∧ M ^ p < ((p - 1).factorial : ℝ) :=
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

lemma exists_coeff_ne_zero {R : Type*} [semiring R] {p : R[X]} (hp : p ≠ 0) :
  ∃ n, p.coeff n ≠ 0 :=
begin
  contrapose! hp,
  simpa [ext_iff],
end

theorem non_empty_supp (f : ℤ[X]) (hf : f ≠ 0) : f.support.nonempty :=
begin
  simp_rw [finset.nonempty, mem_support_iff],
  exact exists_coeff_ne_zero hf,
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
    rw [←mem_support_iff, finset.mem_image],
    split,
    { rintro ⟨a, ha, rfl⟩,
      rwa nat.sub_add_cancel,
      rw min_degree_term, exact finset.min'_le _ _ ha },

    { intro hn,
      exact ⟨n + min_degree_term f hf, hn, nat.add_sub_cancel _ _⟩ },
  end }⟩

theorem coeff_after_change (f : ℤ[X]) (hf : f ≠ 0) (n : ℕ) :
  (make_const_term_nonzero f hf).coeff n = (f.coeff (n+(min_degree_term f hf))) :=
by simp [make_const_term_nonzero]

theorem coeff_zero_after_change (f : ℤ[X]) (hf : f ≠ 0) :
  (make_const_term_nonzero f hf).coeff 0 ≠ 0 :=
begin
  rw [coeff_after_change, zero_add, ←mem_support_iff, min_degree_term],
  exact f.support.min'_mem (non_empty_supp f hf),
end

theorem transform_eq (f : ℤ[X]) (hf : f ≠ 0) :
  f = make_const_term_nonzero f hf * X ^ min_degree_term f hf :=
begin
  ext,
  rw [coeff_mul_X_pow', coeff_after_change],
  split_ifs,
  { rw nat.sub_add_cancel h },
  { rw ←not_mem_support_iff,
    contrapose! h,
    rw min_degree_term,
    exact f.support.min'_le _ h },
end

theorem non_zero_root_same
  (f : ℤ[X]) (hf : f ≠ 0) (r : ℝ) (r_nonzero : r ≠ 0) (root_r : aeval r f = 0) :
  aeval r (make_const_term_nonzero f hf) = 0 :=
begin
  rw [transform_eq f hf, map_mul, map_pow, aeval_X] at root_r,
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero _ r_nonzero) root_r,
end

theorem e_transcendental : transcendental ℤ e :=
begin
  intro e_algebraic,
  rw is_algebraic at e_algebraic,
  obtain ⟨g', g'_nonzero, e_root_g'⟩ := e_algebraic,
  generalize g_def : make_const_term_nonzero g' g'_nonzero = g,
  have coeff_zero_nonzero : (g.coeff 0) ≠ 0,
  { rw ←g_def, apply coeff_zero_after_change },
  have e_root_g : aeval e g = 0,
  { rw ←g_def,
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

theorem e_pow_n_irrational (n : ℕ) (hn : 1 ≤ n) : irrational (e ^ n) :=
transcendental_irrational (e_pow_transcendental n hn)
