/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.eval

/-!
# The derivative map on polynomials

## Main definitions
 * `polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.

-/

noncomputable theory

open finset
open_locale big_operators classical

namespace polynomial
universes u v w y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

section derivative

section semiring
variables [semiring R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative : polynomial R →ₗ[R] polynomial R :=
{ to_fun := λ p, p.sum (λ n a, C (a * n) * X^(n-1)),
  map_add' := λ p q, by rw sum_add_index;
    simp only [add_mul, forall_const, ring_hom.map_add,
      eq_self_iff_true, zero_mul, ring_hom.map_zero],
  map_smul' := λ a p, by dsimp; rw sum_smul_index;
    simp only [mul_sum, ← C_mul', mul_assoc, coeff_C_mul, ring_hom.map_mul, forall_const,
      zero_mul, ring_hom.map_zero, sum] }

lemma derivative_apply (p : polynomial R) :
  derivative p = p.sum (λn a, C (a * n) * X^(n - 1)) := rfl

lemma coeff_derivative (p : polynomial R) (n : ℕ) :
  coeff (derivative p) n = coeff p (n + 1) * (n + 1) :=
begin
  rw [derivative_apply],
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul],
  rw [sum, finset.sum_eq_single (n + 1)],
  simp only [nat.add_succ_sub_one, add_zero, mul_one, if_true, eq_self_iff_true], norm_cast,
  { assume b, cases b,
    { intros, rw [nat.cast_zero, mul_zero, zero_mul], },
    { intros _ H, rw [nat.succ_sub_one b, if_neg (mt (congr_arg nat.succ) H.symm), mul_zero] } },
  { rw [if_pos (nat.add_sub_cancel _ _).symm, mul_one, nat.cast_add, nat.cast_one, mem_support_iff],
    intro h, push_neg at h, simp [h], },
end

@[simp]
lemma derivative_zero : derivative (0 : polynomial R) = 0 :=
derivative.map_zero

@[simp]
lemma iterate_derivative_zero {k : ℕ} : derivative^[k] (0 : polynomial R) = 0 :=
begin
  induction k with k ih,
  { simp, },
  { simp [ih], },
end

@[simp]
lemma derivative_monomial (a : R) (n : ℕ) : derivative (monomial n a) = monomial (n - 1) (a * n) :=
by { rw [derivative_apply, sum_monomial_index, C_mul_X_pow_eq_monomial], simp }

lemma derivative_C_mul_X_pow (a : R) (n : ℕ) : derivative (C a * X ^ n) = C (a * n) * X^(n - 1) :=
by rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, derivative_monomial]

@[simp] lemma derivative_X_pow (n : ℕ) :
  derivative (X ^ n : polynomial R) = (n : polynomial R) * X ^ (n - 1) :=
by convert derivative_C_mul_X_pow (1 : R) n; simp

@[simp] lemma derivative_C {a : R} : derivative (C a) = 0 :=
by simp [derivative_apply]

@[simp] lemma derivative_X : derivative (X : polynomial R) = 1 :=
(derivative_monomial _ _).trans $ by simp

@[simp] lemma derivative_one : derivative (1 : polynomial R) = 0 :=
derivative_C

@[simp] lemma derivative_bit0 {a : polynomial R} : derivative (bit0 a) = bit0 (derivative a) :=
by simp [bit0]

@[simp] lemma derivative_bit1 {a : polynomial R} : derivative (bit1 a) = bit0 (derivative a) :=
by simp [bit1]

@[simp] lemma derivative_add {f g : polynomial R} :
  derivative (f + g) = derivative f + derivative g :=
derivative.map_add f g

@[simp] lemma iterate_derivative_add {f g : polynomial R} {k : ℕ} :
  derivative^[k] (f + g) = (derivative^[k] f) + (derivative^[k] g) :=
derivative.to_add_monoid_hom.iterate_map_add _ _ _

@[simp] lemma derivative_neg {R : Type*} [ring R] (f : polynomial R) :
  derivative (-f) = - derivative f :=
linear_map.map_neg derivative f

@[simp] lemma iterate_derivative_neg {R : Type*} [ring R] {f : polynomial R} {k : ℕ} :
  derivative^[k] (-f) = - (derivative^[k] f) :=
(@derivative R _).to_add_monoid_hom.iterate_map_neg _ _

@[simp] lemma derivative_sub {R : Type*} [ring R] {f g : polynomial R} :
  derivative (f - g) = derivative f - derivative g :=
linear_map.map_sub derivative f g

@[simp] lemma iterate_derivative_sub {R : Type*} [ring R] {k : ℕ} {f g : polynomial R} :
  derivative^[k] (f - g) = (derivative^[k] f) - (derivative^[k] g) :=
begin
  induction k with k ih generalizing f g,
  { simp [nat.iterate], },
  { simp [nat.iterate, ih], }
end

@[simp] lemma derivative_sum {s : finset ι} {f : ι → polynomial R} :
  derivative (∑ b in s, f b) = ∑ b in s, derivative (f b) :=
derivative.map_sum

@[simp] lemma derivative_smul (r : R) (p : polynomial R) : derivative (r • p) = r • derivative p :=
derivative.map_smul _ _

@[simp] lemma iterate_derivative_smul (r : R) (p : polynomial R) (k : ℕ) :
  derivative^[k] (r • p) = r • (derivative^[k] p) :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp [ih], },
end

/-- We can't use `derivative_mul` here because
we want to prove this statement also for noncommutative rings.-/
@[simp]
lemma derivative_C_mul (a : R) (p : polynomial R) : derivative (C a * p) = C a * derivative p :=
by convert derivative_smul a p; apply C_mul'

@[simp]
lemma iterate_derivative_C_mul (a : R) (p : polynomial R) (k : ℕ) :
  derivative^[k] (C a * p) = C a * (derivative^[k] p) :=
by convert iterate_derivative_smul a p k; apply C_mul'

end semiring

section comm_semiring
variables [comm_semiring R]

lemma derivative_eval (p : polynomial R) (x : R) :
  p.derivative.eval x = p.sum (λ n a, (a * n)*x^(n-1)) :=
by simp only [derivative_apply, eval_sum, eval_pow, eval_C, eval_X, eval_nat_cast, eval_mul]

@[simp] lemma derivative_mul {f g : polynomial R} :
  derivative (f * g) = derivative f * g + f * derivative g :=
calc derivative (f * g) = f.sum (λn a, g.sum (λm b, C ((a * b) * (n + m : ℕ)) * X^((n + m) - 1))) :
  begin
    rw mul_eq_sum_sum,
    transitivity, exact derivative_sum,
    transitivity, { apply finset.sum_congr rfl, assume x hx, exact derivative_sum },
    apply finset.sum_congr rfl, assume n hn, apply finset.sum_congr rfl, assume m hm,
    transitivity,
    { apply congr_arg, exact monomial_eq_C_mul_X },
    exact derivative_C_mul_X_pow _ _
  end
  ... = f.sum (λn a, g.sum (λm b,
      (C (a * n) * X^(n - 1)) * (C b * X^m) + (C a * X^n) * (C (b * m) * X^(m - 1)))) :
    sum_congr rfl $ assume n hn, sum_congr rfl $ assume m hm,
      by simp only [nat.cast_add, mul_add, add_mul, C_add, C_mul];
      cases n; simp only [nat.succ_sub_succ, pow_zero];
      cases m; simp only [nat.cast_zero, C_0, nat.succ_sub_succ, zero_mul, mul_zero, nat.add_succ,
        nat.sub_zero, pow_zero, pow_add, one_mul, pow_succ, mul_comm, mul_left_comm]
  ... = derivative f * g + f * derivative g :
    begin
      conv { to_rhs, congr,
        { rw [← sum_C_mul_X_eq g] },
        { rw [← sum_C_mul_X_eq f] } },
      simp only [sum, sum_add_distrib, finset.mul_sum, finset.sum_mul, derivative_apply]
    end

theorem derivative_pow_succ (p : polynomial R) (n : ℕ) :
  (p ^ (n + 1)).derivative = (n + 1) * (p ^ n) * p.derivative :=
nat.rec_on n (by rw [pow_one, nat.cast_zero, zero_add, one_mul, pow_zero, one_mul]) $ λ n ih,
by rw [pow_succ', derivative_mul, ih, mul_right_comm, ← add_mul,
    add_mul (n.succ : polynomial R), one_mul, pow_succ', mul_assoc, n.cast_succ]

theorem derivative_pow (p : polynomial R) (n : ℕ) :
  (p ^ n).derivative = n * (p ^ (n - 1)) * p.derivative :=
nat.cases_on n (by rw [pow_zero, derivative_one, nat.cast_zero, zero_mul, zero_mul]) $ λ n,
by rw [p.derivative_pow_succ n, n.succ_sub_one, n.cast_succ]

lemma derivative_comp (p q : polynomial R) :
  (p.comp q).derivative = q.derivative * p.derivative.comp q :=
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

@[simp]
theorem derivative_map [comm_semiring S] (p : polynomial R) (f : R →+* S) :
  (p.map f).derivative = p.derivative.map f :=
polynomial.induction_on p
  (λ r, by rw [map_C, derivative_C, derivative_C, map_zero])
  (λ p q ihp ihq, by rw [map_add, derivative_add, ihp, ihq, derivative_add, map_add])
  (λ n r ih, by rw [map_mul, map_C, map_pow, map_X,
      derivative_mul, derivative_pow_succ, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      derivative_mul, derivative_pow_succ, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      map_mul, map_C, map_mul, map_pow, map_add, map_nat_cast, map_one, map_X])

@[simp]
theorem iterate_derivative_map [comm_semiring S] (p : polynomial R) (f : R →+* S) (k : ℕ):
  polynomial.derivative^[k] (p.map f) = (polynomial.derivative^[k] p).map f :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp [ih], },
end

/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C (p q : polynomial R) :
  (p.eval₂ C q).derivative = p.derivative.eval₂ C q * q.derivative :=
polynomial.induction_on p
  (λ r, by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
  (λ p₁ p₂ ih₁ ih₂, by rw [eval₂_add, derivative_add, ih₁, ih₂, derivative_add, eval₂_add, add_mul])
  (λ n r ih, by rw [pow_succ', ← mul_assoc, eval₂_mul, eval₂_X, derivative_mul, ih,
      @derivative_mul _ _ _ X, derivative_X, mul_one, eval₂_add, @eval₂_mul _ _ _ _ X, eval₂_X,
      add_mul, mul_right_comm])

theorem of_mem_support_derivative {p : polynomial R} {n : ℕ} (h : n ∈ p.derivative.support) :
  n + 1 ∈ p.support :=
mem_support_iff.2 $ λ (h1 : p.coeff (n+1) = 0), mem_support_iff.1 h $
show p.derivative.coeff n = 0, by rw [coeff_derivative, h1, zero_mul]

theorem degree_derivative_lt {p : polynomial R} (hp : p ≠ 0) : p.derivative.degree < p.degree :=
(finset.sup_lt_iff $ bot_lt_iff_ne_bot.2 $ mt degree_eq_bot.1 hp).2 $ λ n hp, lt_of_lt_of_le
(with_bot.some_lt_some.2 n.lt_succ_self) $ finset.le_sup $ of_mem_support_derivative hp

theorem nat_degree_derivative_lt {p : polynomial R} (hp : p.derivative ≠ 0) :
  p.derivative.nat_degree < p.nat_degree :=
have hp1 : p ≠ 0, from λ h, hp $ by rw [h, derivative_zero],
with_bot.some_lt_some.1 $
begin
  rw [nat_degree, option.get_or_else_of_ne_none $ mt degree_eq_bot.1 hp, nat_degree,
    option.get_or_else_of_ne_none $ mt degree_eq_bot.1 hp1],
  exact degree_derivative_lt hp1
end

theorem degree_derivative_le {p : polynomial R} : p.derivative.degree ≤ p.degree :=
if H : p = 0 then le_of_eq $ by rw [H, derivative_zero] else le_of_lt $ degree_derivative_lt H

/-- The formal derivative of polynomials, as linear homomorphism. -/
def derivative_lhom (R : Type*) [comm_ring R] : polynomial R →ₗ[R] polynomial R :=
{ to_fun    := derivative,
  map_add'  := λ p q, derivative_add,
  map_smul' := λ r p, derivative_smul r p }

@[simp] lemma derivative_lhom_coe {R : Type*} [comm_ring R] :
  (polynomial.derivative_lhom R : polynomial R → polynomial R) = polynomial.derivative :=
rfl

@[simp] lemma derivative_cast_nat {n : ℕ} : derivative (n : polynomial R) = 0 :=
begin
  rw ← C.map_nat_cast n,
  exact derivative_C,
end

@[simp] lemma iterate_derivative_cast_nat_mul {n k : ℕ} {f : polynomial R} :
  derivative^[k] (n * f) = n * (derivative^[k] f) :=
begin
  induction k with k ih generalizing f,
  { simp [nat.iterate], },
  { simp [nat.iterate, ih], }
end

end comm_semiring

section comm_ring
variables [comm_ring R]

lemma derivative_comp_one_sub_X (p : polynomial R) :
  (p.comp (1-X)).derivative = -p.derivative.comp (1-X) :=
by simp [derivative_comp]

@[simp]
lemma iterate_derivative_comp_one_sub_X (p : polynomial R) (k : ℕ) :
  derivative^[k] (p.comp (1-X)) = (-1)^k * (derivative^[k] p).comp (1-X) :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp [ih p.derivative, iterate_derivative_neg, derivative_comp, pow_succ], },
end

end comm_ring

section domain
variables [integral_domain R]

lemma mem_support_derivative [char_zero R] (p : polynomial R) (n : ℕ) :
  n ∈ (derivative p).support ↔ n + 1 ∈ p.support :=
suffices (¬(coeff p (n + 1) = 0 ∨ ((n + 1:ℕ) : R) = 0)) ↔ coeff p (n + 1) ≠ 0,
  by simpa only [mem_support_iff, coeff_derivative, ne.def, mul_eq_zero],
by { rw [nat.cast_eq_zero], simp only [nat.succ_ne_zero, or_false] }

@[simp] lemma degree_derivative_eq [char_zero R] (p : polynomial R) (hp : 0 < nat_degree p) :
  degree (derivative p) = (nat_degree p - 1 : ℕ) :=
begin
  have h0 : p ≠ 0,
  { contrapose! hp,
    simp [hp] },
  apply le_antisymm,
  { rw derivative_apply,
    apply le_trans (degree_sum_le _ _) (sup_le (λ n hn, _)),
    apply le_trans (degree_C_mul_X_pow_le _ _) (with_bot.coe_le_coe.2 (nat.sub_le_sub_right _ _)),
    apply le_nat_degree_of_mem_supp _ hn },
  { refine le_sup _,
    rw [mem_support_derivative, nat.sub_add_cancel, mem_support_iff],
    { show ¬ leading_coeff p = 0,
      rw [leading_coeff_eq_zero],
      assume h, rw [h, nat_degree_zero] at hp,
      exact lt_irrefl 0 (lt_of_le_of_lt (zero_le _) hp), },
    exact hp }
end

theorem nat_degree_eq_zero_of_derivative_eq_zero
  [char_zero R] {f : polynomial R} (h : f.derivative = 0) :
  f.nat_degree = 0 :=
begin
  by_cases hf : f = 0,
  { exact (congr_arg polynomial.nat_degree hf).trans rfl },
  { rw nat_degree_eq_zero_iff_degree_le_zero,
    by_contra absurd,
    have f_nat_degree_pos : 0 < f.nat_degree,
    { rwa [not_le, ←nat_degree_pos_iff_degree_pos] at absurd },
    let m := f.nat_degree - 1,
    have hm : m + 1 = f.nat_degree := nat.sub_add_cancel f_nat_degree_pos,
    have h2 := coeff_derivative f m,
    rw polynomial.ext_iff at h,
    rw [h m, coeff_zero, zero_eq_mul] at h2,
    cases h2,
    { rw [hm, ←leading_coeff, leading_coeff_eq_zero] at h2,
      exact hf h2, },
    { norm_cast at h2 } }
end

end domain

end derivative
end polynomial
