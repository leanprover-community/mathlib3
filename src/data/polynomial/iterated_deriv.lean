/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.polynomial.derivative
import logic.function.iterate
import tactic.ring tactic.linarith

/-!
# Theory of iterated derivative
We define and prove some lemmas about iterated (formal) derivative for polynomials over a semiring.
-/

noncomputable theory

open finset nat polynomial
open_locale big_operators

namespace polynomial
universes u
variable {R : Type u}

section semiring

variables [semiring R] (f p q: polynomial R) (n k : ℕ)

/-- `iterated_deriv f n` is the `n`-th formal derivative of the polynomial `f` -/
def iterated_deriv : polynomial R := derivative ^[n] f

@[simp] lemma iterated_deriv_zero : iterated_deriv f 0 = f := rfl

lemma iterated_deriv_succ : iterated_deriv f (n + 1) = (iterated_deriv f n).derivative :=
by rw [iterated_deriv, iterated_deriv, function.iterate_succ']

@[simp] lemma iterated_deriv_zero_left : iterated_deriv (0 : polynomial R) n = 0 :=
begin
  induction n with n hn,
  { exact iterated_deriv_zero_right _ },
  { rw [iterated_deriv_succ, hn, derivative_zero] },
end

@[simp] lemma iterated_deriv_add : iterated_deriv (p + q) n = iterated_deriv p n + iterated_deriv q n :=
begin
  induction n with n ih,
  { simp only [iterated_deriv_zero_right], },
  { rw [iterated_deriv_succ, ih, polynomial.derivative_add, iterated_deriv_succ, iterated_deriv_succ] }
end

end semiring

section comm_ring
variable [comm_ring R]
variables (f p q: polynomial R) (n k : ℕ)

lemma iterated_deriv_coeff_as_prod_Ico :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = (∏ i in Ico m.succ (m + k.succ), i) * (f.coeff (m+k)) :=
begin
  induction k with k ih,
  { simp only [add_zero, forall_const, one_mul, Ico.self_eq_empty, eq_self_iff_true,
      iterated_deriv_zero_right, prod_empty] },
  { intro m, rw [iterated_deriv_succ, coeff_derivative, ih (m+1), mul_assoc],
    conv_lhs { congr, skip, rw mul_comm }, rw ←mul_assoc,
    apply congr_arg2,
    { have set_eq : (Ico m.succ (m + k.succ.succ)) = (Ico (m + 1).succ (m + 1 + k.succ)) ∪ {m+1},
      { ext, split,
        { intro h,
          simp only [mem_union, Ico.mem, mem_singleton] at h ⊢,
          rw succ_add m (succ k),
          by_cases H : (a = m + 1),
          { right, exact H },
          { left, split,
            { rw succ_le_iff, rw lt_iff_le_and_ne,
              split,
              { exact h.1 },
              { symmetry, exact H }},
            { exact h.2 }}},
        { intro h,
          simp only [mem_union, Ico.mem, mem_singleton] at h ⊢,
          cases h,
          { split,
            { refine le_trans _ h.1,
              apply succ_le_succ,
              exact le_succ m },
            { rw succ_add m (succ k) at h, exact h.2 }},
          { rw h, split,
            { refl },
            {rw add_lt_add_iff_left, apply succ_lt_succ, exact succ_pos k }}}},
      rw set_eq, rw prod_union,
      apply congr_arg2,
      { refl },
      { simp only [prod_singleton], norm_cast },
      { simp only [succ_pos', disjoint_singleton, and_true, lt_add_iff_pos_right, not_le, Ico.mem],
        exact lt_add_one (m + 1),}
    },
    { apply congr_arg, exact succ_add m k, }
  }
end

lemma iterated_deriv_coeff_as_prod_range :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = f.coeff (m + k) * (∏ i in finset.range k, ↑(m + k - i)) :=
begin
  induction k with k ih,
  { simp },

  intro m,
  calc (f.iterated_deriv k.succ).coeff m
      = f.coeff (m + k.succ) * (∏ i in finset.range k, ↑(m + k.succ - i)) * (m + 1) :
    by rw [iterated_deriv_succ, coeff_derivative, ih m.succ, succ_add, add_succ]
  ... = f.coeff (m + k.succ) * (↑(m + 1) * (∏ (i : ℕ) in range k, ↑(m + k.succ - i))) :
    by { push_cast, ring }
  ... = f.coeff (m + k.succ) * (∏ (i : ℕ) in range k.succ, ↑(m + k.succ - i)) :
    by { rw [prod_range_succ, nat.add_sub_assoc (le_succ k), nat.succ_sub le_rfl, nat.sub_self] }
end


lemma zero_of_iterated_deriv_nat_degree_succ : (iterated_deriv f (f.nat_degree + 1)) = 0 :=
begin
  ext,
  rw iterated_deriv_coeff_as_prod_range,
  simp only [cast_one, cast_add, coeff_zero],
  rw mul_eq_zero, right,
  apply polynomial.coeff_eq_zero_of_nat_degree_lt, linarith,
end


lemma iterated_deriv_mul :
  iterated_deriv (p * q) n =
  ∑ k in range n.succ,
    (C (n.choose k : R)) * (iterated_deriv p (n-k)) * (iterated_deriv q k) :=
begin
  induction n with n IH,
  { simp },

  calc (p * q).iterated_deriv n.succ
      = (∑ (k : ℕ) in range n.succ,
           C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv k).derivative :
    by rw [iterated_deriv_succ, IH]
  ... = ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k + 1) * q.iterated_deriv k +
        ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) :
    by simp_rw [derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add,
                iterated_deriv_succ, sum_add_distrib]
  ... = (∑ (k : ℕ) in range n.succ,
            C ↑(n.choose k.succ) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) +
          C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0) +
        ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) : _
  ... = ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) +
        ∑ (k : ℕ) in range n.succ,
            C ↑(n.choose k.succ) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) +
        C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0 :
    by ring
  ... = ∑ (i : ℕ) in range n.succ,
          C ↑(n.succ.choose (i + 1)) * p.iterated_deriv (n + 1 - (i + 1)) * q.iterated_deriv (i + 1) +
        C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0 :
    by simp_rw [choose_succ_succ, succ_sub_succ, cast_add, C.map_add, add_mul, sum_add_distrib]
  ... = ∑ (k : ℕ) in range n.succ.succ,
          C ↑(n.succ.choose k) * p.iterated_deriv (n.succ - k) * q.iterated_deriv k :
    by rw [sum_range_succ' _ n.succ, choose_zero_right, nat.sub_zero],

  congr,
  refine (sum_range_succ' _ _).trans (congr_arg2 (+) _ _),
  { rw [sum_range_succ, nat.choose_succ_self, cast_zero, C.map_zero, zero_mul, zero_mul, zero_add],
    refine sum_congr rfl (λ k hk, _),
    rw mem_range at hk,
    congr,
    rw [← nat.sub_add_comm (nat.succ_le_of_lt hk), nat.succ_sub_succ] },
  { rw [choose_zero_right, nat.sub_zero] },
end

end integral_domain

end polynomial
