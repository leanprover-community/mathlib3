/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.erase_lead
import data.polynomial.degree.lemmas

/-! # Computing special coefficients of polynomials

This file contains computations of certain, hopefully meaningful, coefficients of polynomials.

For instance, there is a computation of the coefficients "just before" the `leading_coeff`.
-/

open_locale polynomial
namespace polynomial

variables {R : Type*}

section semiring
variables [semiring R] {p q : R[X]}

lemma coeff_erase_lead_nat_degree_pred (p0 : p.nat_degree ≠ 0) :
  p.erase_lead.coeff (p.nat_degree - 1) = p.coeff (p.nat_degree - 1) :=
begin
  convert (@erase_lead_coeff R _ p (p.nat_degree - 1)),
  rw if_neg,
  exact (nat.pred_lt p0).ne,
end

lemma coeff_mul_sub_one_new (hp : p.nat_degree ≠ 0) (hq : q.nat_degree ≠ 0) :
  (p * q).coeff (p.nat_degree + q.nat_degree - 1) =
    p.leading_coeff * q.coeff (q.nat_degree - 1) + p.coeff (p.nat_degree - 1) * q.leading_coeff :=
begin
  -- express the polynomial `p` in the form `p = a X ^ n + (p-lower order terms)`
  nth_rewrite 0 ← p.erase_lead_add_C_mul_X_pow,
  -- express the polynomial `q` in the form `q = a X ^ m + (q-lower order terms)`
  nth_rewrite 0 ← q.erase_lead_add_C_mul_X_pow,
  rw [mul_add, add_mul, add_mul, coeff_add],
  -- after partial expansion, the two summands match on each side
  congr,
  rw [nat.add_sub_assoc (nat.one_le_iff_ne_zero.mpr hq), coeff_add],
  { -- one of the contribution is zero, since its degree is wrong
    convert zero_add _,
    -- show that the contribution is really zero
    { refine coeff_eq_zero_of_nat_degree_lt _,
      refine nat_degree_mul_le.trans_lt _,
      refine add_lt_add_of_lt_of_le _ (erase_lead_nat_degree_le _),
      exact (erase_lead_nat_degree_le _).trans_lt (nat.pred_lt hp) },
    -- show that the other contribution matches one of the summands in the statement
    { rw [mul_assoc, coeff_C_mul, X_pow_mul, add_comm, coeff_mul_X_pow,
        coeff_erase_lead_nat_degree_pred hq] } },
  { rw coeff_add,
    -- one of the contribution is zero, since its degree is wrong
    convert add_zero _,
    -- show that the first contribution matches one of the summands in the statement
    { rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow,
        add_comm],
      exact if_neg (nat.pred_lt ((nat.add_pos_left (nat.pos_of_ne_zero hq) _).ne')).ne },
    -- show that the second contribution is really zero
    { rw [← X_pow_mul, ← mul_assoc, coeff_mul_C, add_comm, nat.add_sub_assoc, add_comm,
        coeff_mul_X_pow, erase_lead_coeff, if_neg],
      { exact (nat.pred_lt hp).ne },
      { exact nat.add_one_le_iff.mpr (nat.pos_of_ne_zero hp) } } }
end

end semiring

section comm_semiring
variables [comm_semiring R] {p q : R[X]} {n : ℕ}

lemma pow_coeff_mul_sub_one (n0 : n ≠ 0) (p0 : p.nat_degree ≠ 0) :
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

end comm_semiring

end polynomial
