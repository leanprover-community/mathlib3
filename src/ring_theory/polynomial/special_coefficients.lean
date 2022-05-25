/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

Dear David,

I am sorry to hear that you are struggling.  We can certainly have a chat about how to deal with certain difficulties and how to plan ahead.

I would also encourage you to reach out to Isobel Bowles (isabel.bowles@warwick.ac.uk), who is the departmental contact for well-being issues.

I think that it might be useful to reach out to her soon, since she can probably guide you better right now.

In the meantime, I hope that you can find focus and motivation while concentrating for exams.  As usual, if there is anything that I can do to help, let me know.  And do not worry about reaching out!

Best wishes,
Damiano
-/

import data.polynomial.erase_lead
import data.polynomial.degree.lemmas

/-! # Computing special coefficients of polynomials

This file contains computations of certain, hopefully meaningful, coefficients of polynomials.

For instance, there is a computation of the coefficients "just before" the `leading_coeff`.

Let `R` be a (semi)ring.  We prove a formula for computing the previous-to-last coefficient of a
product of polynomials. -/

open_locale polynomial
namespace polynomial

open polynomial nat
open_locale polynomial

variables {R : Type*} [semiring R] {r : R} {f g h : R[X]} {a b c d : ℕ}

lemma expl (l m n o : R) (fa : f.nat_degree ≤ a) (gb : g.nat_degree ≤ b) :
  ((C l * (X ^ (a + 2) : R[X]) + C m * (X ^ (a + 1)) + f) *
    ((C n * X ^ (b + 2) + C o * X ^ (b + 1) + g))).coeff (a + 2 + b + 2 - 1) =
   l * o + m * n :=
begin
  simp only [mul_add, add_mul, mul_assoc, add_succ_sub_one, coeff_add],
  repeat { rw [X_pow_mul] },
  repeat { rw [mul_assoc _ (X ^ _) (X ^ _), ← pow_add] },
  repeat { rw [coeff_C_mul] },
  repeat { rw [coeff_X_pow] },
  rw [if_neg, if_pos, if_pos, if_neg],
  repeat { rw coeff_eq_zero_of_nat_degree_lt },
  { simp },
  any_goals { refine nat_degree_mul_le.trans_lt _ },
  { rw add_assoc, refine add_lt_add (fa.trans_lt (lt_succ_of_lt _)) (gb.trans_lt _);
    exact (lt_add_one _) },
  repeat { rw [add_assoc a, add_assoc a],
    refine add_lt_add_of_le_of_lt fa ((nat_degree_C_mul_le _ _).trans_lt _),
    refine (nat_degree_X_pow_le _).trans_lt _,
    simp [add_comm] },
  repeat { rw [add_comm, add_comm (_ + b) 1, ← add_assoc],
    refine add_lt_add_of_lt_of_le (((nat_degree_X_pow_le _).trans_lt _)) gb,
    simp [add_comm a] },
  any_goals { simp only [add_comm, add_left_comm, add_assoc, add_right_inj, nat.succ_ne_self,
      not_false_iff, add_left_inj, nat.one_ne_bit0, add_lt_add_iff_left, one_lt_succ_succ] },
end

lemma coeff_mul_nat_degree_add_sub_one_le
  (f0 : f.nat_degree ≠ 0) (g0 : g.nat_degree ≠ 0) (fa : f.nat_degree ≤ a) (gb : g.nat_degree ≤ b) :
  (f * g).coeff (a + b - 1) = f.coeff a * g.coeff (b - 1) + f.coeff (a - 1) * g.coeff b :=
begin

  have := expl (f.coeff a) (f.coeff (a - 1)) (g.coeff b) (g.coeff (b - 1))
    (_ : nat_degree _ ≤ a - 2) (_ : nat_degree _ ≤ b - 2),
  convert this using 2,
  convert expl (f.coeff a) (f.coeff (a - 1)) (g.coeff b) (g.coeff (b - 1)) _ _,
end

lemma coeff_mul_nat_degree_add_sub_one_le
  (f0 : f.nat_degree ≠ 0) (g0 : g.nat_degree ≠ 0) (fa : f.nat_degree ≤ a) (gb : g.nat_degree ≤ b) :
  (f * g).coeff (a + b - 1) = f.coeff a * g.coeff (b - 1) + f.coeff (a - 1) * g.coeff b :=
begin
  refine induction_with_nat_degree_le
    (λ q, (f * q).coeff (a + b - 1) =
      f.coeff a * q.coeff (b - 1) + f.coeff (a - 1) * q.coeff b) b _ _ _ _ gb,
  { simp only [mul_zero, coeff_zero, add_zero] },
  { intros n r r0 nb,
    have b1 : 1 ≤ b := (nat.one_le_iff_ne_zero.mpr g0).trans gb,
    have : b - 1 ≠ b := (nat.pred_lt (nat.one_le_iff_ne_zero.mp b1)).ne,
    rw [← X_pow_mul, ← mul_assoc, coeff_mul_C, coeff_mul_C, coeff_mul_C, ← mul_assoc, ← mul_assoc,
      ← add_mul],
    apply congr_arg (* r),
    by_cases bn : b = n,
    { rw [← bn, coeff_X_pow, if_neg this, coeff_X_pow, if_pos rfl, mul_zero, zero_add, mul_one],
      convert coeff_mul_X_pow _ _ _,
      rw [add_comm, nat.add_sub_assoc, add_comm],
      exact le_trans (nat.add_one_le_iff.mpr (nat.pos_of_ne_zero f0)) fa },
    by_cases a1 : n = b - 1,
    { simp [coeff_X_pow, a1, this.symm, nat.add_sub_assoc b1] },
    { suffices : (f * X ^ n).coeff (a + b - 1) = 0, { simpa [coeff_X_pow, ne.symm a1, bn] },
      refine coeff_eq_zero_of_nat_degree_lt (nat_degree_mul_le.trans_lt _),
      rw nat.add_sub_assoc b1,
      refine add_lt_add_of_le_of_lt fa (nat_degree_pow_le.trans_lt (mul_lt_of_lt_of_le_one _ _)),
      { exact (le_pred_of_lt (nb.lt_of_ne (ne.symm bn))).lt_of_ne a1 },
      { exact nat_degree_X_le } } },
  { exact λ p q fg gn hf hg, by simp [mul_add, hf, hg, add_add_add_comm] }
end

lemma nat_degree_ne_zero_of_mul_X (f0 : f ≠ 0) : (f * X).nat_degree ≠ 0 :=
begin
  contrapose! f0,
  suffices : f * X = 0 * X, from mul_X_injective (by simpa [X_mul]),
  rw [eq_C_of_nat_degree_eq_zero f0, mul_coeff_zero, coeff_X_zero, mul_zero, map_zero, zero_mul],
end

lemma coeff_mul_nat_degree_add_sub_one_le_X (fa : f.nat_degree ≤ a) (gb : g.nat_degree ≤ b) :
  ((f * X) * (g * X)).coeff ((a + 1) + (b + 1) - 1) =
    f.coeff a * (g * X).coeff b + (f * X).coeff a * g.coeff b :=
begin
  by_cases f0 : f = 0,
  { simp [f0] },
  { by_cases g0 : g = 0,
    { simp [g0] },
    { rw coeff_mul_nat_degree_add_sub_one_le,
      { simp },
      repeat { exact nat_degree_ne_zero_of_mul_X ‹_› },
      repeat { exact nat_degree_mul_le.trans (add_le_add ‹_› nat_degree_X_le) } } },
end

lemma coeff_pow_nat_degree_add_sub_one_le {R : Type*} [comm_semiring R] {n : ℕ} (n0 : n ≠ 0)
  {f : R[X]} (f0 : f ≠ 0) (fa : f.nat_degree ≤ a) :
  ((f * X) ^ n).coeff (n * (a + 1) - 1) = f.coeff a ^ (n - 1) * n * (f * X).coeff a :=
begin
  rcases n,
  { refine (n0 rfl).elim },
  { --by_cases fna : (f ^ n).nat_degree = 0,
    --{ rw [pow_succ, eq_C_of_nat_degree_eq_zero fna, coeff_mul_C],
    --  sorry },
    induction n with n hn,
    { simp },
  {
    rw [pow_succ, succ_mul, add_comm],
    replace hn := hn (succ_ne_zero _),
    rw [mul_pow, pow_succ' X, ← mul_assoc (f ^ _)],
    convert coeff_mul_nat_degree_add_sub_one_le_X fa _,
    { simp,
      sorry },
    { refine nat_degree_mul_le.trans (add_le_add (nat_degree_pow_le.trans (by simpa)) _),
      refine nat_degree_pow_le.trans (_),
      refine le_trans _ (mul_one _).le,
      exact mul_le_mul_of_nonneg_left nat_degree_X_le (nat.zero_le _) } } },
end

lemma coeff_pow_nat_degree_add_sub_one_le {R : Type*} [comm_semiring R] {n : ℕ} (n0 : n ≠ 0)
  {f g : R[X]} (f0 : f.nat_degree ≠ 0) (fa : f.nat_degree ≤ a) :
  (f ^ n).coeff (n * a - 1) = f.coeff a ^ (n - 1) * n * f.coeff (a - 1) :=
begin
  rcases n,
  { refine (n0 rfl).elim },
  { --by_cases fna : (f ^ n).nat_degree = 0,
    --{ rw [pow_succ, eq_C_of_nat_degree_eq_zero fna, coeff_mul_C],
    --  sorry },
    induction n with n hn,
    { simp },
  {
    rw [pow_succ, succ_mul, add_comm],
    replace hn := hn (succ_ne_zero _),
    rw [← coeff_mul_X_pow _ n.succ, mul_assoc, ← mul_pow, nat.add_sub_assoc, add_assoc,
      add_comm (_ - _), ← nat.add_sub_assoc, ← mul_one n.succ, mul_assoc, ← mul_add, mul_one,
      one_mul, ← nat.add_sub_assoc],
    rw [coeff_mul_nat_degree_add_sub_one_le f0 _ fa _, hn],
    norm_num,
    rw [mul_add _ (↑n + 1) (1 : R), add_mul, mul_one, ← mul_assoc, ← mul_assoc, ← pow_succ],
    apply congr_arg,
    rw mul_comm (_ ^ _),
    apply congr_arg,
    sorry,

    refine λ hh, fna _,
    convert coeff_mul_nat_degree_add_sub_one_le f0 _ fa _,

  }
     },
end

lemma coeff_pow_nat_degree_add_sub_one_le {n : ℕ} (n0 : n ≠ 0)
  (f0 : f.nat_degree ≠ 0) (fa : f.nat_degree ≤ a) :
  (f ^ n).coeff (n * a - 1) = f.coeff a ^ (n - 1) * n * f.coeff (a - 1) :=
begin
  rcases n with _|_|n,
  { refine (n0 rfl).elim },
  { simp },
  {
    rw [pow_succ, succ_mul, add_comm],
    convert coeff_mul_nat_degree_add_sub_one_le f0 _ fa _,

  }
end
/--  `coeff_mul_nat_degree_add_sub_one` computes the coefficient of the term of degree one less
than the expected `nat_degree` of a product of polynomials.  If

* `f = f₀ * x ^ m + f₁ * x ^ (m - 1) + (...) : R[X]` and
* `g = g₀ * x ^ n + g₁ * x ^ (m - 1) + (...)`,

then the lemmas shows that `f₀ * g₁ + f₁ * g₀` equals `r₁ : R`  in

`f * g = r₀ * x ^ (m + n) + r₁ * x ^ (m + n - 1) + (...)`.   -/
lemma coeff_mul_nat_degree_add_sub_one (f0 : f.nat_degree ≠ 0) (g0 : g.nat_degree ≠ 0) :
  (f * g).coeff (f.nat_degree + g.nat_degree - 1) =
    f.leading_coeff * g.coeff (g.nat_degree - 1) + f.coeff (f.nat_degree - 1) * g.leading_coeff :=
coeff_mul_nat_degree_add_sub_one_le f0 g0 rfl.le rfl.le

/--  `pow_coeff_mul_sub_one` computes the coefficient of the term of degree one less
than the expected `nat_degree` of a power of a polynomial.  If

`p = p₀ * x ^ m + p₁ * x ^ (m - 1) + (...) : R[X]`

then the lemmas shows that `p₀ ^ (n - 1) * n * q₁` equals `r₁ : R`  in

`p ^ n = r₀ * x ^ (n * m) + r₁ * x ^ (n * m - 1) + (...)`. -/
lemma pow_coeff_mul_sub_one {R : Type*} [comm_semiring R] (p : R[X]) {n : ℕ} (n0 : n ≠ 0)
  (p0 : p.nat_degree ≠ 0) :
  (p ^ n).coeff (n * p.nat_degree - 1) =
    p.leading_coeff ^ (n - 1) * n * p.coeff (p.nat_degree - 1) :=
begin
  nontriviality R,
  nth_rewrite 0 ← erase_lead_add_C_mul_X_pow p,
  rw [add_pow, finset_sum_coeff],
  convert finset.sum_eq_single 1 _ _,
  { have : n * p.nat_degree - 1 = (p.nat_degree - 1) + p.nat_degree * (n - 1),
    { rw [add_comm, ← nat.add_sub_assoc (nat.one_le_iff_ne_zero.mpr p0)],
      nth_rewrite 2 ← mul_one p.nat_degree,
      rw [← mul_add, nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr n0), mul_comm] },
    rw [pow_one, mul_pow, nat.choose_one_right, ← pow_mul', mul_comm (_ * _) ↑n, mul_comm _
      p.nat_degree, ← mul_assoc, ← mul_assoc, this, coeff_mul_X_pow, ← C_pow, mul_comm _ (C _),
      coeff_C_mul, mul_assoc, ← C_eq_nat_cast, coeff_C_mul, erase_lead_coeff, if_neg],
    exact (nat.pred_lt p0).ne },
  { intros b hb b1,
    rw finset.mem_range at hb,
    rcases b with (_|_|b),
    { rw [pow_zero, one_mul, nat.sub_zero, nat.choose_zero_right, nat.cast_one, mul_one, mul_pow,
        ← C_pow, coeff_C_mul, ← pow_mul, coeff_X_pow, if_neg, mul_zero],
      exact ((nat.pred_lt (mul_ne_zero n0 p0)).trans_le (mul_comm _ _).le).ne },
    { exact (b1 rfl).elim },
    { refine coeff_eq_zero_of_nat_degree_lt ((nat_degree_mul_le).trans_lt _),
      rw [←C_eq_nat_cast, nat_degree_C, add_zero, mul_pow, ←pow_mul, ←C_pow, mul_comm, mul_assoc],
      refine (nat_degree_C_mul_le _ _).trans_lt ((nat_degree_mul_le).trans_lt _),
      rw nat_degree_X_pow,
      refine nat.lt_pred_iff.mpr (_ : _ + 1 + 1 ≤ n * _),
      have aux := mul_le_mul_of_nonneg_right (nat.lt_succ_iff.mp hb) (zero_le p.nat_degree),
      rw [mul_comm, nat.mul_sub_right_distrib, ← nat.sub_add_comm aux, add_assoc,
        ← nat.sub_add_comm, add_assoc],
      transitivity n * p.nat_degree +
        ((p.nat_degree - 1) * (b.succ.succ) + (1 + 1)) - b.succ.succ * p.nat_degree,
      { refine nat.sub_le_sub_right (nat.add_le_add_left (nat.add_le_add_right _ _) _) _,
        refine nat_degree_pow_le.trans _,
        simp only [mul_comm, erase_lead_nat_degree_le, mul_le_mul_left, nat.succ_pos'] },
      transitivity n * p.nat_degree + p.nat_degree * b.succ.succ - b.succ.succ * p.nat_degree,
      { refine nat.sub_le_sub_right (add_le_add_left _ _) _,
        nth_rewrite 1 ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero p0),
        refine (add_le_add rfl.le _).trans (nat.succ_mul _ _).ge,
        exact (nat.succ_le_succ (nat.succ_le_succ (zero_le _))) },
      { rw [mul_comm b.succ.succ],
        exact le_of_eq (tsub_eq_of_eq_add rfl) },
      exact le_trans aux (nat.le_add_right _ _) } },
  { simp {contextual := tt} }
end

end polynomial
