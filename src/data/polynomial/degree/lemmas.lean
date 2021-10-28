/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.eval
import tactic.interval_cases

/-!
# Theory of degrees of polynomials

Some of the main results include
- `nat_degree_comp_le` : The degree of the composition is at most the product of degrees

-/

noncomputable theory
open_locale classical

open finsupp finset

namespace polynomial
universes u v w
variables {R : Type u} {S : Type v} { ι : Type w} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

section degree

lemma nat_degree_comp_le : nat_degree (p.comp q) ≤ nat_degree p * nat_degree q :=
if h0 : p.comp q = 0 then by rw [h0, nat_degree_zero]; exact nat.zero_le _
else with_bot.coe_le_coe.1 $
  calc ↑(nat_degree (p.comp q)) = degree (p.comp q) : (degree_eq_nat_degree h0).symm
  ... = _ : congr_arg degree comp_eq_sum_left
  ... ≤ _ : degree_sum_le _ _
  ... ≤ _ : sup_le (λ n hn,
    calc degree (C (coeff p n) * q ^ n)
        ≤ degree (C (coeff p n)) + degree (q ^ n) : degree_mul_le _ _
    ... ≤ nat_degree (C (coeff p n)) + n • (degree q) :
      add_le_add degree_le_nat_degree (degree_pow_le _ _)
    ... ≤ nat_degree (C (coeff p n)) + n • (nat_degree q) :
      add_le_add_left (nsmul_le_nsmul_of_le_right (@degree_le_nat_degree _ _ q) n) _
    ... = (n * nat_degree q : ℕ) :
     by rw [nat_degree_C, with_bot.coe_zero, zero_add, ← with_bot.coe_nsmul,
       nsmul_eq_mul]; simp
    ... ≤ (nat_degree p * nat_degree q : ℕ) : with_bot.coe_le_coe.2 $
      mul_le_mul_of_nonneg_right
        (le_nat_degree_of_ne_zero (mem_support_iff.1 hn))
        (nat.zero_le _))

lemma degree_pos_of_root {p : polynomial R} (hp : p ≠ 0) (h : is_root p a) : 0 < degree p :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_degree_le_zero hlt,
  rw [is_root, this, eval_C] at h,
  simp only [h, ring_hom.map_zero] at this,
  exact hp this,
end

lemma nat_degree_le_iff_coeff_eq_zero :
  p.nat_degree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 :=
by simp_rw [nat_degree_le_iff_degree_le, degree_le_iff_coeff_zero, with_bot.coe_lt_coe]

lemma nat_degree_C_mul_le (a : R) (f : polynomial R) :
  (C a * f).nat_degree ≤ f.nat_degree :=
calc
  (C a * f).nat_degree ≤ (C a).nat_degree + f.nat_degree : nat_degree_mul_le
  ... = 0 + f.nat_degree : by rw nat_degree_C a
  ... = f.nat_degree : zero_add _

lemma nat_degree_mul_C_le (f : polynomial R) (a : R) :
  (f * C a).nat_degree ≤ f.nat_degree :=
calc
  (f * C a).nat_degree ≤ f.nat_degree + (C a).nat_degree : nat_degree_mul_le
  ... = f.nat_degree + 0 : by rw nat_degree_C a
  ... = f.nat_degree : add_zero _

lemma eq_nat_degree_of_le_mem_support (pn : p.nat_degree ≤ n) (ns : n ∈ p.support) :
  p.nat_degree = n :=
le_antisymm pn (le_nat_degree_of_mem_supp _ ns)

lemma nat_degree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
  (C a * p).nat_degree = p.nat_degree :=
le_antisymm (nat_degree_C_mul_le a p) (calc
  p.nat_degree = (1 * p).nat_degree : by nth_rewrite 0 [← one_mul p]
  ... = (C ai * (C a * p)).nat_degree : by rw [← C_1, ← au, ring_hom.map_mul, ← mul_assoc]
  ... ≤ (C a * p).nat_degree : nat_degree_C_mul_le ai (C a * p))

lemma nat_degree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
  (p * C a).nat_degree = p.nat_degree :=
le_antisymm (nat_degree_mul_C_le p a) (calc
  p.nat_degree = (p * 1).nat_degree : by nth_rewrite 0 [← mul_one p]
  ... = ((p * C a) * C ai).nat_degree : by rw [← C_1, ← au, ring_hom.map_mul, ← mul_assoc]
  ... ≤ (p * C a).nat_degree : nat_degree_mul_C_le (p * C a) ai)

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_mul_C_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
Lemma `nat_degree_mul_C_eq_of_no_zero_divisors` below separates cases, in order to overcome this
hurdle.
-/
lemma nat_degree_mul_C_eq_of_mul_ne_zero (h : p.leading_coeff * a ≠ 0) :
  (p * C a).nat_degree = p.nat_degree :=
begin
  refine eq_nat_degree_of_le_mem_support (nat_degree_mul_C_le p a) _,
  refine mem_support_iff.mpr _,
  rwa coeff_mul_C,
end

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_C_mul_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
Lemma `nat_degree_C_mul_eq_of_no_zero_divisors` below separates cases, in order to overcome this
hurdle.
-/
lemma nat_degree_C_mul_eq_of_mul_ne_zero (h : a * p.leading_coeff ≠ 0) :
  (C a * p).nat_degree = p.nat_degree :=
begin
  refine eq_nat_degree_of_le_mem_support (nat_degree_C_mul_le a p) _,
  refine mem_support_iff.mpr _,
  rwa coeff_C_mul,
end

lemma nat_degree_add_coeff_mul (f g : polynomial R) :
  (f * g).coeff (f.nat_degree + g.nat_degree) = f.coeff f.nat_degree * g.coeff g.nat_degree :=
by simp only [coeff_nat_degree, coeff_mul_degree_add_degree]

lemma nat_degree_lt_coeff_mul (h : p.nat_degree + q.nat_degree < m + n) :
  (p * q).coeff (m + n) = 0 :=
coeff_eq_zero_of_nat_degree_lt (nat_degree_mul_le.trans_lt h)

variables [semiring S]

lemma nat_degree_pos_of_eval₂_root {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  0 < nat_degree p :=
lt_of_not_ge $ λ hlt, begin
  have A : p = C (p.coeff 0) := eq_C_of_nat_degree_le_zero hlt,
  rw [A, eval₂_C] at hz,
  simp only [inj (p.coeff 0) hz, ring_hom.map_zero] at A,
  exact hp A
end

lemma degree_pos_of_eval₂_root {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  0 < degree p :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_eval₂_root hp f hz inj)

@[simp] lemma coe_lt_degree {p : polynomial R} {n : ℕ} :
  ((n : with_bot ℕ) < degree p) ↔ n < nat_degree p :=
begin
  by_cases h : p = 0,
  { simp [h] },
  rw [degree_eq_nat_degree h, with_bot.coe_lt_coe],
end

end degree
end semiring

section no_zero_divisors
variables [semiring R] [no_zero_divisors R] {p q : polynomial R}

lemma nat_degree_mul_C_eq_of_no_zero_divisors (a0 : a ≠ 0) :
  (p * C a).nat_degree = p.nat_degree :=
begin
  by_cases p0 : p = 0,
  { rw [p0, zero_mul] },
  { exact nat_degree_mul_C_eq_of_mul_ne_zero (mul_ne_zero (leading_coeff_ne_zero.mpr p0) a0) }
end

lemma nat_degree_C_mul_eq_of_no_zero_divisors (a0 : a ≠ 0) :
  (C a * p).nat_degree = p.nat_degree :=
begin
  by_cases p0 : p = 0,
  { rw [p0, mul_zero] },
  { exact nat_degree_C_mul_eq_of_mul_ne_zero (mul_ne_zero a0 (leading_coeff_ne_zero.mpr p0)) }
end

end no_zero_divisors

end polynomial
