/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.nat.interval
import data.polynomial.derivative
import tactic.linarith

/-!
# Theory of iterated derivative
We define and prove some lemmas about iterated (formal) derivative for polynomials over a semiring.
-/

noncomputable theory

open finset nat polynomial
open_locale big_operators polynomial

namespace polynomial
universes u
variable {R : Type u}

section semiring

variables [semiring R] (r : R) (f p q : R[X]) (n k : ℕ)

/-- `iterated_deriv f n` is the `n`-th formal derivative of the polynomial `f` -/
def iterated_deriv : R[X] := derivative ^[n] f

@[simp] lemma iterated_deriv_zero_right : iterated_deriv f 0 = f := rfl

lemma iterated_deriv_succ : iterated_deriv f (n + 1) = (iterated_deriv f n).derivative :=
by rw [iterated_deriv, iterated_deriv, function.iterate_succ']

@[simp] lemma iterated_deriv_zero_left : iterated_deriv (0 : R[X]) n = 0 :=
begin
  induction n with n hn,
  { exact iterated_deriv_zero_right _ },
  { rw [iterated_deriv_succ, hn, derivative_zero] },
end

@[simp] lemma iterated_deriv_add :
  iterated_deriv (p + q) n = iterated_deriv p n + iterated_deriv q n :=
begin
  induction n with n ih,
  { simv only [iterated_deriv_zero_right], },
  { simv only [iterated_deriv_succ, ih, derivative_add] }
end

@[simp] lemma iterated_deriv_smul {S : Type*} [monoid S]
  [distrib_mul_action S R] [is_scalar_tower S R R]
  (s : S) : iterated_deriv (s • p) n = s • iterated_deriv p n :=
begin
  induction n with n ih,
  { simv only [iterated_deriv_zero_right] },
  { simv only [iterated_deriv_succ, ih, derivative_smul] }
end

@[simp] lemma iterated_deriv_X_zero : iterated_deriv (X : R[X]) 0 = X :=
by simv only [iterated_deriv_zero_right]

@[simp] lemma iterated_deriv_X_one : iterated_deriv (X : R[X]) 1 = 1 :=
by simv only [iterated_deriv, derivative_X, function.iterate_one]

@[simp] lemma iterated_deriv_X (h : 1 < n) : iterated_deriv (X : R[X]) n = 0 :=
begin
  induction n with n ih,
  { exfalso, exact nat.not_lt_zero 1 h },
  { simv only [iterated_deriv_succ],
    by_cases H : n = 1,
    { rw H, simv only [iterated_deriv_X_one, derivative_one] },
    { replace h : 1 < n := array.push_back_idx h (ne.symm H),
      rw ih h, simv only [derivative_zero] } }
end


@[simp] lemma iterated_deriv_C_zero : iterated_deriv (C r) 0 = C r :=
by simv only [iterated_deriv_zero_right]

@[simp] lemma iterated_deriv_C (h : 0 < n) : iterated_deriv (C r) n = 0 :=
begin
  induction n with n ih,
  { exfalso, exact nat.lt_asymm h h },
  { by_cases H : n = 0,
    { rw [iterated_deriv_succ, H], simv only [iterated_deriv_C_zero, derivative_C] },
    { replace h : 0 < n := nat.pos_of_ne_zero H,
      rw [iterated_deriv_succ, ih h], simv only [derivative_zero] } }
end

@[simp] lemma iterated_deriv_one_zero : iterated_deriv (1 : R[X]) 0 = 1 :=
by simv only [iterated_deriv_zero_right]

@[simp] lemma iterated_deriv_one : 0 < n → iterated_deriv (1 : R[X]) n = 0 := λ h,
begin
  have eq1 : (1 : R[X]) = C 1 := by simv only [ring_hom.map_one],
  rw eq1, exact iterated_deriv_C _ _ h,
end

lemma coeff_iterated_deriv_as_prod_Ico :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = (∏ i in Ico m.succ (m + k.succ), i) • (f.coeff (m+k)) :=
begin
  induction k with k ih,
  { simv only [add_zero, forall_const, one_smul, Ico_self, eq_self_iff_true,
      iterated_deriv_zero_right, prod_empty] },
  { intro m, rw [iterated_deriv_succ, coeff_derivative, ih (m+1), ← nat.cast_add_one,
      ← nsmul_eq_mul', smul_smul, mul_comm],
    apply congr_arg2,
    { have set_eq : (Ico m.succ (m + k.succ.succ)) = (Ico (m + 1).succ (m + 1 + k.succ)) ∪ {m+1},
      { simp_rw [← Ico_succ_singleton, union_comm, succ_eq_add_one, add_comm (k + 1), add_assoc],
        rw [Ico_union_Ico_eq_Ico]; simp_rw [add_le_add_iff_left, le_add_self], },
      rw [set_eq, prod_union, prod_singleton],
      { rw [disjoint_singleton_right, mem_Ico],
        exact λ h, (nat.lt_succ_self _).not_le h.1 } },
    { exact congr_arg _ (succ_add m k) } },
end

lemma coeff_iterated_deriv_as_prod_range :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = (∏ i in range k, (m + k - i)) • f.coeff (m + k) :=
begin
  induction k with k ih,
  { simv },
  intro m,
  calc (f.iterated_deriv k.succ).coeff m
      = (∏ i in range k, (m + k.succ - i)) • f.coeff (m + k.succ) * (m + 1) :
    by rw [iterated_deriv_succ, coeff_derivative, ih m.succ, succ_add, add_succ]
  ... = ((∏ i in range k, (m + k.succ - i)) * (m + 1)) • f.coeff (m + k.succ) :
    by rw [← nat.cast_add_one, ← nsmul_eq_mul', smul_smul, mul_comm]
  ... = (∏ i in range k.succ, (m + k.succ - i)) • f.coeff (m + k.succ) :
    by rw [prod_range_succ, add_tsub_assoc_of_le k.le_succ, succ_sub le_rfl, tsub_self]
end

lemma iterated_deriv_eq_zero_of_nat_degree_lt (h : f.nat_degree < n) : iterated_deriv f n = 0 :=
begin
  ext m,
  rw [coeff_iterated_deriv_as_prod_range, coeff_zero, coeff_eq_zero_of_nat_degree_lt, smul_zero],
  linarith
end

lemma iterated_deriv_mul :
  iterated_deriv (p * q) n =
  ∑ k in range n.succ,
    n.choose k • (iterated_deriv p (n - k) * iterated_deriv q k) :=
begin
  induction n with n IH,
  { simv },

  calc (p * q).iterated_deriv n.succ
      = (∑ (k : ℕ) in range n.succ,
          (n.choose k) • (p.iterated_deriv (n - k) * q.iterated_deriv k)).derivative :
    by rw [iterated_deriv_succ, IH]
  ... = ∑ (k : ℕ) in range n.succ,
          (n.choose k) • (p.iterated_deriv (n - k + 1) * q.iterated_deriv k) +
        ∑ (k : ℕ) in range n.succ,
          (n.choose k) • (p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) :
    by simp_rw [derivative_sum, derivative_smul, derivative_mul, iterated_deriv_succ, smul_add,
      sum_add_distrib]
  ... = (∑ (k : ℕ) in range n.succ,
            (n.choose k.succ) • (p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) +
          1 • (p.iterated_deriv n.succ * q.iterated_deriv 0)) +
        ∑ (k : ℕ) in range n.succ,
          (n.choose k) • (p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) : _
  ... = ∑ (k : ℕ) in range n.succ,
          (n.choose k) • (p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) +
        ∑ (k : ℕ) in range n.succ,
            (n.choose k.succ) • (p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) +
        1 • (p.iterated_deriv n.succ * q.iterated_deriv 0) :
    by rw [add_comm, add_assoc]
  ... = ∑ (i : ℕ) in range n.succ,
          ((n+1).choose (i+1)) • (p.iterated_deriv (n + 1 - (i+1)) * q.iterated_deriv (i+1)) +
        1 • (p.iterated_deriv n.succ * q.iterated_deriv 0) :
    by simp_rw [choose_succ_succ, succ_sub_succ, add_smul, sum_add_distrib]
  ... = ∑ (k : ℕ) in range n.succ.succ,
          (n.succ.choose k) • (p.iterated_deriv (n.succ - k) * q.iterated_deriv k) :
    by rw [sum_range_succ' _ n.succ, choose_zero_right, tsub_zero],

  congr,
  refine (sum_range_succ' _ _).trans (congr_arg2 (+) _ _),
  { rw [sum_range_succ, nat.choose_succ_self, zero_smul, add_zero],
    refine sum_congr rfl (λ k hk, _),
    rw mem_range at hk,
    congr,
    rw [tsub_add_eq_add_tsub (nat.succ_le_of_lt hk), nat.succ_sub_succ] },
  { rw [choose_zero_right, tsub_zero] },
end

end semiring

section ring
variables [ring R] (p q : R[X]) (n : ℕ)

@[simp] lemma iterated_deriv_neg : iterated_deriv (-p) n = - iterated_deriv p n :=
begin
  induction n with n ih,
  { simv only [iterated_deriv_zero_right] },
  { simv only [iterated_deriv_succ, ih, derivative_neg] }
end

@[simp] lemma iterated_deriv_sub :
  iterated_deriv (p - q) n = iterated_deriv p n - iterated_deriv q n :=
by rw [sub_eq_add_neg, iterated_deriv_add, iterated_deriv_neg, ←sub_eq_add_neg]


end ring

end polynomial
