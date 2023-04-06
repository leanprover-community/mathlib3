/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import algebra.hom.iterate
import data.polynomial.eval

/-!
# The derivative map on polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions
 * `polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.

-/

noncomputable theory

open finset
open_locale big_operators classical polynomial

namespace polynomial
universes u v w y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

section derivative

section semiring
variables [semiring R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative : R[X] →ₗ[R] R[X] :=
{ to_fun := λ p, p.sum (λ n a, C (a * n) * X^(n-1)),
  map_add' := λ p q, by rw sum_add_index;
    simp only [add_mul, forall_const, ring_hom.map_add,
      eq_self_iff_true, zero_mul, ring_hom.map_zero],
  map_smul' := λ a p, by dsimp; rw sum_smul_index;
    simp only [mul_sum, ← C_mul', mul_assoc, coeff_C_mul, ring_hom.map_mul, forall_const,
      zero_mul, ring_hom.map_zero, sum] }

lemma derivative_apply (p : R[X]) :
  derivative p = p.sum (λn a, C (a * n) * X^(n - 1)) := rfl

lemma coeff_derivative (p : R[X]) (n : ℕ) :
  coeff (derivative p) n = coeff p (n + 1) * (n + 1) :=
begin
  rw [derivative_apply],
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul],
  rw [sum, finset.sum_eq_single (n + 1)],
  simp only [nat.add_succ_sub_one, add_zero, mul_one, if_true, eq_self_iff_true], norm_cast,
  { assume b, cases b,
    { intros, rw [nat.cast_zero, mul_zero, zero_mul], },
    { intros _ H, rw [nat.succ_sub_one b, if_neg (mt (congr_arg nat.succ) H.symm), mul_zero] } },
  { rw [if_pos (add_tsub_cancel_right n 1).symm, mul_one, nat.cast_add, nat.cast_one,
      mem_support_iff],
    intro h, push_neg at h, simp [h], },
end

@[simp]
lemma derivative_zero : derivative (0 : R[X]) = 0 :=
derivative.map_zero

@[simp]
lemma iterate_derivative_zero {k : ℕ} : derivative^[k] (0 : R[X]) = 0 :=
begin
  induction k with k ih,
  { simp, },
  { simp [ih], },
end

@[simp]
lemma derivative_monomial (a : R) (n : ℕ) : derivative (monomial n a) = monomial (n - 1) (a * n) :=
by { rw [derivative_apply, sum_monomial_index, C_mul_X_pow_eq_monomial], simp }

lemma derivative_C_mul_X (a : R) : derivative (C a * X) = C a :=
by simpa only [C_mul_X_eq_monomial, derivative_monomial, nat.cast_one, mul_one]

lemma derivative_C_mul_X_pow (a : R) (n : ℕ) : derivative (C a * X ^ n) = C (a * n) * X ^ (n - 1) :=
by rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, derivative_monomial]

lemma derivative_C_mul_X_sq (a : R) : derivative (C a * X ^ 2) = C (a * 2) * X :=
by rw [derivative_C_mul_X_pow, nat.cast_two, pow_one]

@[simp] lemma derivative_X_pow (n : ℕ) : derivative (X ^ n : R[X]) = C ↑n * X ^ (n - 1) :=
by convert derivative_C_mul_X_pow (1 : R) n; simp

@[simp] lemma derivative_X_sq : derivative (X ^ 2 : R[X]) = C 2 * X :=
by rw [derivative_X_pow, nat.cast_two, pow_one]

@[simp] lemma derivative_C {a : R} : derivative (C a) = 0 :=
by simp [derivative_apply]

lemma derivative_of_nat_degree_zero {p : R[X]} (hp : p.nat_degree = 0) : p.derivative = 0 :=
by rw [eq_C_of_nat_degree_eq_zero hp, derivative_C]

@[simp] lemma derivative_X : derivative (X : R[X]) = 1 :=
(derivative_monomial _ _).trans $ by simp

@[simp] lemma derivative_one : derivative (1 : R[X]) = 0 :=
derivative_C

@[simp] lemma derivative_bit0 {a : R[X]} : derivative (bit0 a) = bit0 (derivative a) :=
by simp [bit0]

@[simp] lemma derivative_bit1 {a : R[X]} : derivative (bit1 a) = bit0 (derivative a) :=
by simp [bit1]

@[simp] lemma derivative_add {f g : R[X]} : derivative (f + g) = derivative f + derivative g :=
derivative.map_add f g

@[simp] lemma derivative_X_add_C (c : R) : (X + C c).derivative = 1 :=
by rw [derivative_add, derivative_X, derivative_C, add_zero]

@[simp] lemma iterate_derivative_add {f g : R[X]} {k : ℕ} :
  derivative^[k] (f + g) = (derivative^[k] f) + (derivative^[k] g) :=
derivative.to_add_monoid_hom.iterate_map_add _ _ _

@[simp] lemma derivative_sum {s : finset ι} {f : ι → R[X]} :
  derivative (∑ b in s, f b) = ∑ b in s, derivative (f b) :=
derivative.map_sum

@[simp] lemma derivative_smul {S : Type*} [monoid S]
  [distrib_mul_action S R] [is_scalar_tower S R R]
  (s : S) (p : R[X]) : derivative (s • p) = s • derivative p :=
derivative.map_smul_of_tower s p

@[simp] lemma iterate_derivative_smul {S : Type*} [monoid S]
  [distrib_mul_action S R] [is_scalar_tower S R R]
  (s : S) (p : R[X]) (k : ℕ) :
  derivative^[k] (s • p) = s • (derivative^[k] p) :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp [ih], },
end

@[simp]
lemma iterate_derivative_C_mul (a : R) (p : R[X]) (k : ℕ) :
  derivative^[k] (C a * p) = C a * (derivative^[k] p) :=
by simp_rw [← smul_eq_C_mul, iterate_derivative_smul]

theorem of_mem_support_derivative {p : R[X]} {n : ℕ} (h : n ∈ p.derivative.support) :
  n + 1 ∈ p.support :=
mem_support_iff.2 $ λ (h1 : p.coeff (n+1) = 0), mem_support_iff.1 h $
show p.derivative.coeff n = 0, by rw [coeff_derivative, h1, zero_mul]

theorem degree_derivative_lt {p : R[X]} (hp : p ≠ 0) : p.derivative.degree < p.degree :=
(finset.sup_lt_iff $ bot_lt_iff_ne_bot.2 $ mt degree_eq_bot.1 hp).2 $ λ n hp, lt_of_lt_of_le
(with_bot.some_lt_some.2 n.lt_succ_self) $ finset.le_sup $ of_mem_support_derivative hp

theorem degree_derivative_le {p : R[X]} : p.derivative.degree ≤ p.degree :=
if H : p = 0 then le_of_eq $ by rw [H, derivative_zero] else (degree_derivative_lt H).le

theorem nat_degree_derivative_lt {p : R[X]} (hp : p.nat_degree ≠ 0) :
  p.derivative.nat_degree < p.nat_degree :=
begin
  cases eq_or_ne p.derivative 0 with hp' hp',
  { rw [hp', polynomial.nat_degree_zero],
    exact hp.bot_lt },
  { rw nat_degree_lt_nat_degree_iff hp',
    exact degree_derivative_lt (λ h, hp (h.symm ▸ nat_degree_zero)) }
end

lemma nat_degree_derivative_le (p : R[X]) : p.derivative.nat_degree ≤ p.nat_degree - 1 :=
begin
  by_cases p0 : p.nat_degree = 0,
  { simp [p0, derivative_of_nat_degree_zero] },
  { exact nat.le_pred_of_lt (nat_degree_derivative_lt p0) }
end

@[simp] lemma derivative_nat_cast {n : ℕ} : derivative (n : R[X]) = 0 :=
begin
  rw ← map_nat_cast C n,
  exact derivative_C,
end

lemma iterate_derivative_eq_zero {p : R[X]} {x : ℕ} (hx : p.nat_degree < x) :
  polynomial.derivative^[x] p = 0 :=
begin
  induction h : p.nat_degree using nat.strong_induction_on with _ ih generalizing p x,
  subst h,
  obtain ⟨t, rfl⟩ := nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne',
  rw [function.iterate_succ_apply],
  by_cases hp : p.nat_degree = 0,
  { rw [derivative_of_nat_degree_zero hp, iterate_derivative_zero] },
  have := nat_degree_derivative_lt hp,
  exact ih _ this (this.trans_le $ nat.le_of_lt_succ hx) rfl
end

@[simp] lemma iterate_derivative_C {k} (h : 0 < k) : (derivative^[k] (C a : R[X])) = 0 :=
iterate_derivative_eq_zero $ (nat_degree_C _).trans_lt h

@[simp] lemma iterate_derivative_one {k} (h : 0 < k) : (derivative^[k] (1 : R[X])) = 0 :=
iterate_derivative_C h

@[simp] lemma iterate_derivative_X {k} (h : 1 < k) : (derivative^[k] (X : R[X])) = 0 :=
iterate_derivative_eq_zero $ nat_degree_X_le.trans_lt h

theorem nat_degree_eq_zero_of_derivative_eq_zero [no_zero_smul_divisors ℕ R] {f : R[X]}
  (h : f.derivative = 0) : f.nat_degree = 0 :=
begin
  rcases eq_or_ne f 0 with rfl | hf,
  { exact nat_degree_zero },
  rw nat_degree_eq_zero_iff_degree_le_zero,
  by_contra' f_nat_degree_pos,
  rw [←nat_degree_pos_iff_degree_pos] at f_nat_degree_pos,
  let m := f.nat_degree - 1,
  have hm : m + 1 = f.nat_degree := tsub_add_cancel_of_le f_nat_degree_pos,
  have h2 := coeff_derivative f m,
  rw polynomial.ext_iff at h,
  rw [h m, coeff_zero, ← nat.cast_add_one, ← nsmul_eq_mul', eq_comm, smul_eq_zero] at h2,
  replace h2 := h2.resolve_left m.succ_ne_zero,
  rw [hm, ←leading_coeff, leading_coeff_eq_zero] at h2,
  exact hf h2
end

theorem eq_C_of_derivative_eq_zero [no_zero_smul_divisors ℕ R] {f : R[X]} (h : f.derivative = 0) :
  f = C (f.coeff 0) :=
eq_C_of_nat_degree_eq_zero $ nat_degree_eq_zero_of_derivative_eq_zero h

@[simp] lemma derivative_mul {f g : R[X]} :
  derivative (f * g) = derivative f * g + f * derivative g :=
calc derivative (f * g) = f.sum (λ n a, g.sum (λ m b, (n + m) • (C (a * b) * X ^ ((n + m) - 1)))) :
  begin
    rw mul_eq_sum_sum,
    transitivity, exact derivative_sum,
    transitivity, { apply finset.sum_congr rfl, assume x hx, exact derivative_sum },
    apply finset.sum_congr rfl, assume n hn, apply finset.sum_congr rfl, assume m hm,
    transitivity,
    { exact congr_arg _ C_mul_X_pow_eq_monomial.symm },
    dsimp, rw [← smul_mul_assoc, smul_C, nsmul_eq_mul'], exact derivative_C_mul_X_pow _ _
  end
  ... = f.sum (λn a, g.sum (λm b,
      (n • (C a * X^(n - 1))) * (C b * X^m) + (C a * X^n) * (m • (C b * X^(m - 1))))) :
    sum_congr rfl $ assume n hn, sum_congr rfl $ assume m hm,
      by cases n; cases m; simp_rw [add_smul, mul_smul_comm, smul_mul_assoc,
        X_pow_mul_assoc, ← mul_assoc, ← C_mul, mul_assoc, ← pow_add];
        simp only [nat.add_succ, nat.succ_add, nat.succ_sub_one, zero_smul, add_comm]
  ... = derivative f * g + f * derivative g :
    begin
      conv { to_rhs, congr,
        { rw [← sum_C_mul_X_pow_eq g] },
        { rw [← sum_C_mul_X_pow_eq f] } },
      simp only [sum, sum_add_distrib, finset.mul_sum, finset.sum_mul, derivative_apply],
      simp_rw [← smul_mul_assoc, smul_C, nsmul_eq_mul'],
    end

lemma derivative_eval (p : R[X]) (x : R) :
  p.derivative.eval x = p.sum (λ n a, (a * n) * x ^ (n-1)) :=
by simp_rw [derivative_apply, eval_sum, eval_mul_X_pow, eval_C]

@[simp]
theorem derivative_map [semiring S] (p : R[X]) (f : R →+* S) :
  (p.map f).derivative = p.derivative.map f :=
begin
  let n := max p.nat_degree ((map f p).nat_degree),
  rw [derivative_apply, derivative_apply],
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))],
  rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))],
  simp only [polynomial.map_sum, polynomial.map_mul, polynomial.map_C, map_mul, coeff_map,
    map_nat_cast, polynomial.map_nat_cast, polynomial.map_pow, map_X],
  all_goals { intro n, rw [zero_mul, C_0, zero_mul], }
end

@[simp]
theorem iterate_derivative_map [semiring S] (p : R[X]) (f : R →+* S) (k : ℕ):
  polynomial.derivative^[k] (p.map f) = (polynomial.derivative^[k] p).map f :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp only [ih, function.iterate_succ, polynomial.derivative_map, function.comp_app], },
end

lemma derivative_nat_cast_mul {n : ℕ} {f : R[X]} :
  (↑n * f).derivative = n * f.derivative :=
by simp

@[simp] lemma iterate_derivative_nat_cast_mul {n k : ℕ} {f : R[X]} :
  derivative^[k] (n * f) = n * (derivative^[k] f) :=
by induction k with k ih generalizing f; simp*

lemma mem_support_derivative [no_zero_smul_divisors ℕ R]
  (p : R[X]) (n : ℕ) :
  n ∈ (derivative p).support ↔ n + 1 ∈ p.support :=
suffices ¬p.coeff (n + 1) * (n + 1 : ℕ) = 0 ↔ coeff p (n + 1) ≠ 0,
  by simpa only [mem_support_iff, coeff_derivative, ne.def, nat.cast_succ],
by { rw [← nsmul_eq_mul', smul_eq_zero], simp only [nat.succ_ne_zero, false_or] }

@[simp] lemma degree_derivative_eq [no_zero_smul_divisors ℕ R]
  (p : R[X]) (hp : 0 < nat_degree p) :
  degree (derivative p) = (nat_degree p - 1 : ℕ) :=
begin
  have h0 : p ≠ 0,
  { contrapose! hp,
    simp [hp] },
  apply le_antisymm,
  { rw derivative_apply,
    apply le_trans (degree_sum_le _ _) (finset.sup_le (λ n hn, _)),
    apply le_trans (degree_C_mul_X_pow_le _ _) (with_bot.coe_le_coe.2 (tsub_le_tsub_right _ _)),
    apply le_nat_degree_of_mem_supp _ hn },
  { refine le_sup _,
    rw [mem_support_derivative, tsub_add_cancel_of_le, mem_support_iff],
    { show ¬ leading_coeff p = 0,
      rw [leading_coeff_eq_zero],
      assume h, rw [h, nat_degree_zero] at hp,
      exact lt_irrefl 0 (lt_of_le_of_lt (zero_le _) hp), },
    exact hp }
end

lemma coeff_iterate_derivative_as_prod_Ico {k} (p : R[X]) :
  ∀ m : ℕ, (derivative^[k] p).coeff m = (∏ i in Ico m.succ (m + k.succ), i) • (p.coeff (m + k)) :=
begin
  induction k with k ih,
  { simp only [add_zero, forall_const, one_smul, Ico_self, eq_self_iff_true,
      function.iterate_zero_apply, prod_empty] },
  { intro m, rw [function.iterate_succ_apply', coeff_derivative, ih (m+1), ← nat.cast_add_one,
      ← nsmul_eq_mul', smul_smul, mul_comm],
    apply congr_arg2,
    { have set_eq : (Ico m.succ (m + k.succ.succ)) = (Ico (m + 1).succ (m + 1 + k.succ)) ∪ {m+1},
      { simp_rw [← nat.Ico_succ_singleton, union_comm, nat.succ_eq_add_one, add_comm (k + 1),
          add_assoc],
        rw [Ico_union_Ico_eq_Ico]; simp_rw [add_le_add_iff_left, le_add_self], },
      rw [set_eq, prod_union, prod_singleton],
      { rw [disjoint_singleton_right, mem_Ico],
        exact λ h, (nat.lt_succ_self _).not_le h.1 } },
    { exact congr_arg _ (nat.succ_add m k) } },
end

lemma coeff_iterate_derivative_as_prod_range {k} (p : R[X]) :
  ∀ m : ℕ, (derivative^[k] p).coeff m = (∏ i in range k, (m + k - i)) • p.coeff (m + k) :=
begin
  induction k with k ih,
  { simp },
  intro m,
  calc (derivative^[k + 1] p).coeff m
      = (∏ i in range k, (m + k.succ - i)) • p.coeff (m + k.succ) * (m + 1) :
    by rw [function.iterate_succ_apply', coeff_derivative, ih m.succ, nat.succ_add, nat.add_succ]
  ... = ((∏ i in range k, (m + k.succ - i)) * (m + 1)) • p.coeff (m + k.succ) :
    by rw [← nat.cast_add_one, ← nsmul_eq_mul', smul_smul, mul_comm]
  ... = (∏ i in range k.succ, (m + k.succ - i)) • p.coeff (m + k.succ) :
    by rw [prod_range_succ, add_tsub_assoc_of_le k.le_succ, nat.succ_sub le_rfl, tsub_self]
end

lemma iterate_derivative_mul {n} (p q : R[X]) :
  derivative^[n] (p * q) =
  ∑ k in range n.succ,
    n.choose k • ((derivative^[n - k] p) * (derivative^[k] q)) :=
begin
  induction n with n IH,
  { simp },

  calc derivative^[n + 1] (p * q)
      = (∑ (k : ℕ) in range n.succ,
          (n.choose k) • ((derivative^[n - k] p) * (derivative^[k] q))).derivative :
    by rw [function.iterate_succ_apply', IH]
  ... = ∑ (k : ℕ) in range n.succ,
          (n.choose k) • ((derivative^[n - k + 1] p) * (derivative^[k] q)) +
        ∑ (k : ℕ) in range n.succ,
          (n.choose k) • ((derivative^[n - k] p) * (derivative^[k + 1] q)) :
    by simp_rw [derivative_sum, derivative_smul, derivative_mul, function.iterate_succ_apply',
      smul_add, sum_add_distrib]
  ... = (∑ (k : ℕ) in range n.succ,
            (n.choose k.succ) • ((derivative^[n - k] p) * (derivative^[k + 1] q)) +
          1 • ((derivative^[n + 1] p) * (derivative^[0] q))) +
        ∑ (k : ℕ) in range n.succ,
          (n.choose k) • ((derivative^[n - k] p) * (derivative^[k + 1] q)) : _
  ... = ∑ (k : ℕ) in range n.succ,
          (n.choose k) • ((derivative^[n - k] p) * (derivative^[k + 1] q)) +
        ∑ (k : ℕ) in range n.succ,
            (n.choose k.succ) • ((derivative^[n - k] p) * (derivative^[k + 1] q)) +
        1 • ((derivative^[n + 1] p) * (derivative^[0] q)) :
    by rw [add_comm, add_assoc]
  ... = ∑ (i : ℕ) in range n.succ,
          ((n+1).choose (i+1)) • ((derivative^[n + 1 - (i + 1)] p) * (derivative^[i + 1] q)) +
        1 • ((derivative^[n + 1] p) * (derivative^[0] q)) :
    by simp_rw [nat.choose_succ_succ, nat.succ_sub_succ, add_smul, sum_add_distrib]
  ... = ∑ (k : ℕ) in range n.succ.succ,
          (n.succ.choose k) • (derivative^[n.succ - k] p * (derivative^[k] q)) :
    by rw [sum_range_succ' _ n.succ, nat.choose_zero_right, tsub_zero],

  congr,
  refine (sum_range_succ' _ _).trans (congr_arg2 (+) _ _),
  { rw [sum_range_succ, nat.choose_succ_self, zero_smul, add_zero],
    refine sum_congr rfl (λ k hk, _),
    rw mem_range at hk,
    congr,
    rw [tsub_add_eq_add_tsub (nat.succ_le_of_lt hk), nat.succ_sub_succ] },
  { rw [nat.choose_zero_right, tsub_zero] },
end

end semiring

section comm_semiring
variables [comm_semiring R]

theorem derivative_pow_succ (p : R[X]) (n : ℕ) :
  (p ^ (n + 1)).derivative = C ↑(n + 1) * (p ^ n) * p.derivative :=
nat.rec_on n (by rw [pow_one, nat.cast_one, C_1, one_mul, pow_zero, one_mul]) $ λ n ih,
by rw [pow_succ', derivative_mul, ih, nat.add_one, mul_right_comm, nat.cast_add n.succ, C_add,
       add_mul, add_mul, pow_succ', ← mul_assoc, nat.cast_one, C_1, one_mul]

theorem derivative_pow (p : R[X]) (n : ℕ) :
  (p ^ n).derivative = C ↑n * (p ^ (n - 1)) * p.derivative :=
nat.cases_on n (by rw [pow_zero, derivative_one, nat.cast_zero, C_0, zero_mul, zero_mul]) $ λ n,
by rw [p.derivative_pow_succ n, n.succ_sub_one, n.cast_succ]

theorem derivative_sq (p : R[X]) : (p ^ 2).derivative = C 2 * p * p.derivative :=
by rw [derivative_pow_succ, nat.cast_two, pow_one]

theorem dvd_iterate_derivative_pow (f : R[X]) (n : ℕ) {m : ℕ} (c : R) (hm : m ≠ 0) :
  (n : R) ∣ eval c (derivative^[m] (f ^ n)) :=
begin
  obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero hm,
  rw [function.iterate_succ_apply, derivative_pow, mul_assoc, C_eq_nat_cast,
      iterate_derivative_nat_cast_mul, eval_mul, eval_nat_cast],
  exact dvd_mul_right _ _,
end

lemma iterate_derivative_X_pow_eq_nat_cast_mul (n k : ℕ) :
  (derivative^[k] (X ^ n : R[X])) = ↑(nat.desc_factorial n k) * X ^ (n - k) :=
begin
  induction k with k ih,
  { rw [function.iterate_zero_apply, tsub_zero, nat.desc_factorial_zero, nat.cast_one, one_mul] },
  { rw [function.iterate_succ_apply', ih, derivative_nat_cast_mul, derivative_X_pow, C_eq_nat_cast,
      nat.succ_eq_add_one, nat.desc_factorial_succ, nat.sub_sub, nat.cast_mul, ←mul_assoc,
      mul_comm ↑(nat.desc_factorial _ _)] },
end

lemma iterate_derivative_X_pow_eq_C_mul (n k : ℕ) :
  (derivative^[k] (X ^ n : R[X])) = C ↑(nat.desc_factorial n k) * X ^ (n - k) :=
by rw [iterate_derivative_X_pow_eq_nat_cast_mul n k, C_eq_nat_cast]

lemma iterate_derivative_X_pow_eq_smul (n : ℕ) (k : ℕ) :
  (derivative^[k] (X ^ n : R[X])) = (nat.desc_factorial n k : R) • X ^ (n - k) :=
by rw [iterate_derivative_X_pow_eq_C_mul n k, smul_eq_C_mul]

lemma derivative_X_add_C_pow (c : R) (m : ℕ) :
  ((X + C c) ^ m).derivative = C ↑m * (X + C c) ^ (m - 1) :=
by rw [derivative_pow, derivative_X_add_C, mul_one]

lemma derivative_X_add_C_sq (c : R) : ((X + C c) ^ 2).derivative = C 2 * (X + C c) :=
by rw [derivative_sq, derivative_X_add_C, mul_one]

lemma iterate_derivative_X_add_pow (n k : ℕ) (c : R) : derivative^[k] ((X + C c) ^ n) =
  ↑(∏ i in finset.range k, (n - i)) * (X + C c) ^ (n - k) :=
begin
  induction k with k IH,
  { rw [function.iterate_zero_apply, finset.range_zero, finset.prod_empty, nat.cast_one, one_mul,
      tsub_zero] },
  { simp only [function.iterate_succ_apply', IH, derivative_mul, zero_mul, derivative_nat_cast,
      zero_add, finset.prod_range_succ, C_eq_nat_cast, nat.sub_sub, ←mul_assoc,
      derivative_X_add_C_pow, nat.succ_eq_add_one, nat.cast_mul] },
end

lemma derivative_comp (p q : R[X]) : (p.comp q).derivative = q.derivative * p.derivative.comp q :=
begin
  apply polynomial.induction_on' p,
  { intros p₁ p₂ h₁ h₂, simp [h₁, h₂, mul_add], },
  { intros n r,
    simp only [derivative_pow, derivative_mul, monomial_comp, derivative_monomial, derivative_C,
      zero_mul, C_eq_nat_cast, zero_add, ring_hom.map_mul],
    -- is there a tactic for this? (a multiplicative `abel`):
    rw [mul_comm (derivative q)],
    simp only [mul_assoc], }
end

/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C (p q : R[X]) :
  (p.eval₂ C q).derivative = p.derivative.eval₂ C q * q.derivative :=
polynomial.induction_on p
  (λ r, by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
  (λ p₁ p₂ ih₁ ih₂, by rw [eval₂_add, derivative_add, ih₁, ih₂, derivative_add, eval₂_add, add_mul])
  (λ n r ih, by rw [pow_succ', ← mul_assoc, eval₂_mul, eval₂_X, derivative_mul, ih,
      @derivative_mul _ _ _ X, derivative_X, mul_one, eval₂_add, @eval₂_mul _ _ _ _ X, eval₂_X,
      add_mul, mul_right_comm])

theorem derivative_prod {s : multiset ι} {f : ι → R[X]} :
  (multiset.map f s).prod.derivative =
  (multiset.map (λ i, (multiset.map f (s.erase i)).prod * (f i).derivative) s).sum :=
begin
  refine multiset.induction_on s (by simp) (λ i s h, _),
  rw [multiset.map_cons, multiset.prod_cons, derivative_mul, multiset.map_cons _ i s,
    multiset.sum_cons, multiset.erase_cons_head, mul_comm (f i).derivative],
  congr,
  rw [h, ← add_monoid_hom.coe_mul_left, (add_monoid_hom.mul_left (f i)).map_multiset_sum _,
    add_monoid_hom.coe_mul_left],
  simp only [function.comp_app, multiset.map_map],
  refine congr_arg _ (multiset.map_congr rfl (λ j hj, _)),
  rw [← mul_assoc, ← multiset.prod_cons, ← multiset.map_cons],
  by_cases hij : i = j,
  { simp [hij, ← multiset.prod_cons, ← multiset.map_cons, multiset.cons_erase hj] },
  { simp [hij] }
end

end comm_semiring

section ring

variables [ring R]

@[simp] lemma derivative_neg (f : R[X]) : derivative (-f) = - derivative f :=
linear_map.map_neg derivative f

@[simp] lemma iterate_derivative_neg {f : R[X]} {k : ℕ} :
  derivative^[k] (-f) = - (derivative^[k] f) :=
(@derivative R _).to_add_monoid_hom.iterate_map_neg _ _

@[simp] lemma derivative_sub {f g : R[X]} : derivative (f - g) = derivative f - derivative g :=
linear_map.map_sub derivative f g

@[simp] lemma derivative_X_sub_C (c : R) : (X - C c).derivative = 1 :=
by rw [derivative_sub, derivative_X, derivative_C, sub_zero]

@[simp] lemma iterate_derivative_sub {k : ℕ} {f g : R[X]} :
  derivative^[k] (f - g) = (derivative^[k] f) - (derivative^[k] g) :=
by induction k with k ih generalizing f g; simp*

@[simp] lemma derivative_int_cast {n : ℤ} : derivative (n : R[X]) = 0 :=
begin
  rw ← C_eq_int_cast n,
  exact derivative_C,
end

lemma derivative_int_cast_mul {n : ℤ} {f : R[X]} :
  (↑n * f).derivative = n * f.derivative :=
by simp

@[simp] lemma iterate_derivative_int_cast_mul {n : ℤ} {k : ℕ} {f : R[X]} :
  derivative^[k] (↑n * f) = n * (derivative^[k] f) :=
by induction k with k ih generalizing f; simp*

end ring

section comm_ring
variables [comm_ring R]

lemma derivative_comp_one_sub_X (p : R[X]) :
  (p.comp (1 - X)).derivative = -p.derivative.comp (1 - X) :=
by simp [derivative_comp]

@[simp]
lemma iterate_derivative_comp_one_sub_X (p : R[X]) (k : ℕ) :
  derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (derivative^[k] p).comp (1 - X) :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp [ih p.derivative, iterate_derivative_neg, derivative_comp, pow_succ], },
end

lemma eval_multiset_prod_X_sub_C_derivative {S : multiset R} {r : R} (hr : r ∈ S) :
  eval r (multiset.map (λ a, X - C a) S).prod.derivative =
  (multiset.map (λ a, r - a) (S.erase r)).prod :=
begin
  nth_rewrite 0 [← multiset.cons_erase hr],
  simpa using (eval_ring_hom r).map_multiset_prod (multiset.map (λ a, X - C a) (S.erase r)),
end

lemma derivative_X_sub_C_pow (c : R) (m : ℕ) :
  ((X - C c) ^ m).derivative = C ↑m * (X - C c) ^ (m - 1) :=
by rw [derivative_pow, derivative_X_sub_C, mul_one]

lemma derivative_X_sub_C_sq (c : R) : ((X - C c) ^ 2).derivative = C 2 * (X - C c) :=
by rw [derivative_sq, derivative_X_sub_C, mul_one]

lemma iterate_derivative_X_sub_pow (n k : ℕ) (c : R) :
  (derivative^[k] ((X - C c) ^ n)) = (↑(∏ i in finset.range k, (n - i))) * (X - C c) ^ (n - k) :=
by simp_rw [sub_eq_add_neg, ←C_neg, iterate_derivative_X_add_pow]

end comm_ring

end derivative

end polynomial
