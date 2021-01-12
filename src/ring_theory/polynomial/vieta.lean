/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hanting Zhang
-/
import tactic
import ring_theory.polynomial.basic
import algebra.polynomial.big_operators

/-!
# Vieta's Formula

The main result is `coeff_of_prod_X_add_C`, which relates the roots of
a product of linear terms to the coefficients.
-/

universes u v w
open_locale big_operators

open finset polynomial

namespace vieta

variables {α : Type u} [integral_domain α]
variables {n : ℕ} {r : ℕ → α} {f : polynomial α}

lemma coeff_zero_X_add_C (a : α) : coeff (X + C a) 0 = a :=
begin
  simp [polynomial.coeff_zero_eq_eval_zero],
end

lemma coeff_one_X_add_C (a : α) : coeff (X + C a) 1 = (1 : α) :=
begin
  simp [polynomial.coeff_zero_eq_eval_zero, coeff_C_ne_zero],
end

lemma coeff_ge_two_X_add_C (a : α) (h : 2 ≤ n) : coeff (X + C a) n = (0 : α) :=
begin
  rw [coeff_add, coeff_C_ne_zero, add_zero, coeff_X, if_neg (ne_of_lt (nat.succ_le_iff.mp h))],
  exact ne_of_gt (lt_of_lt_of_le zero_lt_two h),
end

lemma degree_X_add_C' (a : α) : degree (X + C a) = 1 :=
have degree (C a) < degree (X : polynomial α),
from calc degree (C a) ≤ 0 : degree_C_le
                   ... < 1 : with_bot.some_lt_some.mpr zero_lt_one
                   ... = degree X : degree_X.symm,
by rw [degree_add_eq_left_of_degree_lt this, degree_X]

lemma coeff_top (n : ℕ) (r : ℕ → α) : coeff (∏ i in range n, (X + C (r i))) n = 1 :=
begin
  have h : nat_degree (∏ i in range n, (X + C (r i))) = n :=
  begin
    rw nat_degree_prod,
    conv { to_rhs, rw [← card_range n, finset.card_eq_sum_ones] },
    congr, ext,
    rw ← degree_eq_iff_nat_degree_eq,
    simp only [degree_X_add_C, with_top.coe_one],
    exact monic.ne_zero (monic_X_add_C (r x)),
    intros,
    exact monic.ne_zero (monic_X_add_C (r i)),
  end,
  conv { to_lhs, congr, skip, rw ← h, },
  rw [coeff_nat_degree, leading_coeff_prod, ← one_mul X, ← C_1],
  conv { to_rhs, rw ← @prod_const_one _ _ (range n : finset ℕ), },
  congr, ext,
  rw leading_coeff_X_add_C,
  norm_num,
end

lemma sum_prod_mul_X_add_C (n k: ℕ) (h: k ≤ n) : ∑ l in range (k + 1),
  (∑ A in powerset_len (n - l) (range n), ∏ j in A, r j) * (X + C (r n)).coeff (k - l) =
  (∑ A in powerset_len (n - k + 1) (range n), ∏ j in A, r j)
    + (∑ A in powerset_len (n - k) (range n), ∏ j in A, r j) * (r n) :=
begin
  rw [sum_range_succ, nat.sub_self, coeff_zero_X_add_C],
  cases nat.eq_zero_or_pos k,
  { rw h_1, simp,
    have hh : powerset_len (n + 1) (range n) = ∅ :=
    by { apply finset.card_eq_zero.mp, simp },
    rw hh, simp },
  rw [← nat.succ_pred_eq_of_pos h_1, nat.succ_eq_add_one, sum_range_succ,
      nat.add_sub_cancel_left, coeff_one_X_add_C, mul_one],
  have hsum : ∑ x in range k.pred,
              (∑ A in powerset_len (n - x) (range n),
              ∏ j  in A, r j) * (X + C (r n)).coeff (k.pred + 1 - x) = ∑ x in range k.pred, 0 :=
  begin
    refine finset.sum_congr rfl (λ x hx, _),
    rw [coeff_ge_two_X_add_C, mul_zero],
    rw add_comm k.pred _,
    exact nat.lt_sub_right_of_add_lt (add_lt_add_left (mem_range.mp hx) 1),
  end,
  rw hsum,
  simp only [hsum, add_zero, sum_const_zero],
  rw add_comm,
  have h_re : n - (k.pred + 1) + 1 = n - k.pred :=
  begin
    rw [nat.pred_eq_sub_one, nat.sub_add_eq_max, max_eq_left],
    omega nat, exact h_1,
  end,
  rwa h_re,
end

lemma sum_prod_insert (n k : ℕ) : ∑ A in powerset_len (n - k) (range n), (∏ j in A, r j) * r n =
                       ∑ A in powerset_len (n - k) (range n), ∏ j in insert n A, r j :=
begin
  refine finset.sum_congr rfl (λ t ht, _),
  rw [mul_comm, prod_insert],
  intro hn,
  apply @not_mem_range_self n,
  exact mem_of_subset (mem_powerset_len.mp ht).left hn,
end

lemma powerset_len_sum_succ_insert (n k : ℕ) (h : k ≤ n) :
  ∑ A in powerset_len (n - k + 1) (range n), ∏ j in A, r j +
  ∑ A in powerset_len (n - k) (range n), ∏ j in insert n A, r j =
  ∑ A in powerset_len (n.succ - k) (range n.succ), ∏ j in A, r j :=
begin
  have hh : ∑ a in filter (λ (a : finset ℕ), (insert n a).card = n.succ - k) (range n).powerset,
            ∏ j in insert n a, r j =
            ∑ a in filter (λ (a : finset ℕ), a.card = n - k) (range n).powerset,
            ∏ j in insert n a, r j :=
  begin
    apply sum_congr,
    { ext,
      rw [mem_filter, mem_filter, and.congr_right_iff],
      intro ha,
      rw card_insert_of_not_mem,
      omega,
      rw finset.mem_powerset at ha,
      intro h,
      apply not_mem_range_self,
      exact mem_of_subset ha h },
    simp,
  end,
  rw [@powerset_len_eq_filter _ _ (range n.succ), range_add_one, sum_filter, sum_powerset_insert,
    ← sum_filter, ← sum_filter, ← powerset_len_eq_filter, hh, ← @powerset_len_eq_filter],
  congr,
  omega,
  exact not_mem_range_self,
end

/-- A sum version of Vieta's Formulas -/
lemma coeff_of_prod_X_add_C :
  ∀ (k : ℕ), k ≤ n → coeff (∏ i in range n, (X + C (r i))) k
  = ∑ A in (powerset_len (n - k) (range n)), (∏ j in A, r j) :=
begin
  induction n with n ih,
  { simp only [nat.nat_zero_eq_zero, le_zero_iff_eq, nat.zero_sub, forall_eq, range_zero],
    rw [prod_empty, coeff_one_zero, powerset_len_zero ∅, sum_singleton, prod_empty] },
  { intros k hk,
    cases nat.of_le_succ hk,
  { calc (∏ i in range n.succ, (X + C (r i))).coeff k
        = ∑ l in range (k + 1),
          coeff (∏ (i : ℕ) in range n, (X + C (r i))) l * (X + C (r n)).coeff (k - l) :
    begin
      rw [nat.succ_eq_add_one, prod_range_succ, mul_comm, coeff_mul],
      rw ← nat.sum_antidiagonal_eq_sum_range_succ
        (λ a, λ b, coeff (finset.prod (range n) (λ i, X + C (r i))) a * coeff (X + C (r n)) b) k,
    end
    ... = ∑ l in range (k + 1),
          (∑ A in powerset_len (n - l) (range n), ∏ j in A, r j) * (X + C (r n)).coeff (k - l) :
    begin
      apply sum_congr, { refl },
      intros l hl,
      specialize ih l,
      have h_ln : l ≤ n := by { rw finset.mem_range_succ_iff at hl, exact le_trans hl h, },
      rw ih h_ln,
    end
    ... = (∑ A in powerset_len (n - k + 1) (range n), ∏ j in A, r j)
          + (∑ A in powerset_len (n - k) (range n), ∏ j in A, r j) * (r n)  :
    by { exact sum_prod_mul_X_add_C n k h }
    ... = ∑ A in powerset_len (n.succ - k) (range n.succ), (∏ j in A, r j) :
    by rwa [sum_mul, sum_prod_insert, powerset_len_sum_succ_insert] },

    { simp only [h, nat.sub_self, powerset_len_zero, sum_singleton, prod_empty],
      convert coeff_top n.succ r } }
end

end vieta
