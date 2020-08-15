/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.eval

/-!
# Theory of univariate polynomials


-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finsupp finset
open_locale big_operators

namespace polynomial
universes u v w y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

section derivative

section semiring
variables [semiring R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative (p : polynomial R) : polynomial R := p.sum (λn a, C (a * n) * X^(n - 1))

lemma coeff_derivative (p : polynomial R) (n : ℕ) :
  coeff (derivative p) n = coeff p (n + 1) * (n + 1) :=
begin
  rw [derivative],
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul],
  rw [finsupp.sum, finset.sum_eq_single (n + 1)],
  simp only [nat.add_succ_sub_one, add_zero, mul_one, if_true, eq_self_iff_true], norm_cast,
  swap, { rw [if_pos (nat.add_sub_cancel _ _).symm, mul_one, nat.cast_add, nat.cast_one, mem_support_iff],
    intro h, push_neg at h, simp [h], },
  { assume b, cases b,
    { intros, rw [nat.cast_zero, mul_zero, zero_mul], },
    { intros _ H, rw [nat.succ_sub_one b, if_neg (mt (congr_arg nat.succ) H.symm), mul_zero] } }
end

@[simp] lemma derivative_zero : derivative (0 : polynomial R) = 0 :=
finsupp.sum_zero_index

lemma derivative_monomial (a : R) (n : ℕ) : derivative (C a * X ^ n) = C (a * n) * X^(n - 1) :=
begin
  rw [← single_eq_C_mul_X, ← single_eq_C_mul_X, derivative, monomial,
    sum_single_index, single_eq_C_mul_X],
  simp only [zero_mul, C_0],
end

@[simp] lemma derivative_C {a : R} : derivative (C a) = 0 :=
suffices derivative (C a * X^0) = C (a * 0:R) * X ^ 0,
  by simpa only [mul_one, zero_mul, C_0, mul_zero, pow_zero],
derivative_monomial a 0

@[simp] lemma derivative_X : derivative (X : polynomial R) = 1 :=
by simpa only [mul_one, one_mul, C_1, pow_one, nat.cast_one, pow_zero]
  using derivative_monomial (1:R) 1

@[simp] lemma derivative_one : derivative (1 : polynomial R) = 0 :=
derivative_C

@[simp] lemma derivative_add {f g : polynomial R} :
  derivative (f + g) = derivative f + derivative g :=
by refine finsupp.sum_add_index _ _; intros;
simp only [add_mul, zero_mul, C_0, C_add, C_mul]

/-- The formal derivative of polynomials, as additive homomorphism. -/
def derivative_hom (R : Type*) [semiring R] : polynomial R →+ polynomial R :=
{ to_fun := derivative,
  map_zero' := derivative_zero,
  map_add' := λ p q, derivative_add }

@[simp] lemma derivative_neg {R : Type*} [ring R] (f : polynomial R) :
  derivative (-f) = -derivative f :=
(derivative_hom R).map_neg f

@[simp] lemma derivative_sub {R : Type*} [ring R] (f g : polynomial R) :
  derivative (f - g) = derivative f - derivative g :=
(derivative_hom R).map_sub f g

instance : is_add_monoid_hom (derivative : polynomial R → polynomial R) :=
(derivative_hom R).is_add_monoid_hom

@[simp] lemma derivative_sum {s : finset ι} {f : ι → polynomial R} :
  derivative (∑ b in s, f b) = ∑ b in s, derivative (f b) :=
(derivative_hom R).map_sum f s

@[simp] lemma derivative_smul (r : R) (p : polynomial R) : derivative (r • p) = r • derivative p :=
by { ext, simp only [coeff_derivative, mul_assoc, coeff_smul], }

end semiring

section comm_semiring
variables [comm_semiring R]

@[simp] lemma derivative_mul {f g : polynomial R} :
  derivative (f * g) = derivative f * g + f * derivative g :=
calc derivative (f * g) = f.sum (λn a, g.sum (λm b, C ((a * b) * (n + m : ℕ)) * X^((n + m) - 1))) :
  begin
    transitivity, exact derivative_sum,
    transitivity, { apply finset.sum_congr rfl, assume x hx, exact derivative_sum },
    apply finset.sum_congr rfl, assume n hn, apply finset.sum_congr rfl, assume m hm,
    transitivity,
    { apply congr_arg, exact single_eq_C_mul_X },
    exact derivative_monomial _ _
  end
  ... = f.sum (λn a, g.sum (λm b,
      (C (a * n) * X^(n - 1)) * (C b * X^m) + (C a * X^n) * (C (b * m) * X^(m - 1)))) :
    sum_congr rfl $ assume n hn, sum_congr rfl $ assume m hm,
      by simp only [nat.cast_add, mul_add, add_mul, C_add, C_mul];
      cases n; simp only [nat.succ_sub_succ, pow_zero];
      cases m; simp only [nat.cast_zero, C_0, nat.succ_sub_succ, zero_mul, mul_zero,
        nat.sub_zero, pow_zero, pow_add, one_mul, pow_succ, mul_comm, mul_left_comm]
  ... = derivative f * g + f * derivative g :
    begin
      conv { to_rhs, congr,
        { rw [← sum_C_mul_X_eq g] },
        { rw [← sum_C_mul_X_eq f] } },
      unfold derivative finsupp.sum,
      simp only [sum_add_distrib, finset.mul_sum, finset.sum_mul]
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

theorem derivative_map [comm_semiring S] (p : polynomial R) (f : R →+* S) :
  (p.map f).derivative = p.derivative.map f :=
polynomial.induction_on p
  (λ r, by rw [map_C, derivative_C, derivative_C, map_zero])
  (λ p q ihp ihq, by rw [map_add, derivative_add, ihp, ihq, derivative_add, map_add])
  (λ n r ih, by rw [map_mul, map_C, map_pow, map_X,
      derivative_mul, derivative_pow_succ, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      derivative_mul, derivative_pow_succ, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      map_mul, map_C, map_mul, map_pow, map_add, map_nat_cast, map_one, map_X])

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
finsupp.mem_support_iff.2 $ λ (h1 : p.coeff (n+1) = 0), finsupp.mem_support_iff.1 h $
show p.derivative.coeff n = 0, by rw [coeff_derivative, h1, zero_mul]

theorem degree_derivative_lt {p : polynomial R} (hp : p ≠ 0) : p.derivative.degree < p.degree :=
(finset.sup_lt_iff $ bot_lt_iff_ne_bot.2 $ mt degree_eq_bot.1 hp).2 $ λ n hp, lt_of_lt_of_le
(with_bot.some_lt_some.2 n.lt_succ_self) $ finset.le_sup $ of_mem_support_derivative hp

theorem nat_degree_derivative_lt {p : polynomial R} (hp : p.derivative ≠ 0) :
  p.derivative.nat_degree < p.nat_degree :=
have hp1 : p ≠ 0, from λ h, hp $ by rw [h, derivative_zero],
with_bot.some_lt_some.1 $ by { rw [nat_degree, option.get_or_else_of_ne_none $ mt degree_eq_bot.1 hp,
  nat_degree, option.get_or_else_of_ne_none $ mt degree_eq_bot.1 hp1], exact degree_derivative_lt hp1 }

theorem degree_derivative_le {p : polynomial R} : p.derivative.degree ≤ p.degree :=
if H : p = 0 then le_of_eq $ by rw [H, derivative_zero] else le_of_lt $ degree_derivative_lt H

/-- The formal derivative of polynomials, as linear homomorphism. -/
def derivative_lhom (R : Type*) [comm_ring R] : polynomial R →ₗ[R] polynomial R :=
{ to_fun    := derivative,
  map_add'  := λ p q, derivative_add,
  map_smul' := λ r p, derivative_smul r p }

end comm_semiring

section domain
variables [integral_domain R]
-- TODO: golf this, dunno how i broke it so bad
lemma mem_support_derivative [char_zero R] (p : polynomial R) (n : ℕ) :
  n ∈ (derivative p).support ↔ n + 1 ∈ p.support :=
begin
rw finsupp.mem_support_iff, split; intro h,
suffices h1 : p.coeff (n+1) ≠ 0, simp; tauto, contrapose! h,
convert coeff_derivative _ _, simp [h],
contrapose! h, simp,
suffices : p.to_fun (n + 1) * (n + 1) = 0, simp only [mul_eq_zero] at this, cases this,
{ exact this }, { norm_cast at this },
erw ← h, symmetry, convert coeff_derivative _ _,
end

@[simp] lemma degree_derivative_eq [char_zero R] (p : polynomial R) (hp : 0 < nat_degree p) :
  degree (derivative p) = (nat_degree p - 1 : ℕ) :=
le_antisymm
  (le_trans (degree_sum_le _ _) $ sup_le $ assume n hn,
    have n ≤ nat_degree p, begin
      rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree],
      { refine le_degree_of_ne_zero _, simpa only [mem_support_iff] using hn },
      { assume h, simpa only [h, support_zero] using hn }
    end,
    le_trans (degree_monomial_le _ _) $ with_bot.coe_le_coe.2 $ nat.sub_le_sub_right this _)
  begin
    refine le_sup _,
    rw [mem_support_derivative, nat.sub_add_cancel, mem_support_iff],
    { show ¬ leading_coeff p = 0,
      rw [leading_coeff_eq_zero],
      assume h, rw [h, nat_degree_zero] at hp,
      exact lt_irrefl 0 (lt_of_le_of_lt (zero_le _) hp), },
    exact hp
  end

end domain

end derivative
end polynomial
