/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hanting Zhang
-/
import algebra.polynomial.big_operators
import algebra.big_operators.nat_antidiagonal

/-!
# Vieta's Formula

The main result is `coeff_of_prod_X_add_C`, which shows that the `k`th coefficient of
a product of linear terms `X + r i` is the `k`th symmetric polynomial of the constant terms `r i`.
-/

universes u v w
open_locale big_operators

open finset polynomial

namespace vieta

variables {α : Type u} [integral_domain α]
variables {n : ℕ} {r : ℕ → α} {f : polynomial α}

lemma coeff_zero_X_add_C (a : α) : coeff (X + C a) 0 = a :=
by simp [coeff_zero_eq_eval_zero]

lemma coeff_one_X_add_C (a : α) : coeff (X + C a) 1 = (1 : α) :=
by simp [coeff_zero_eq_eval_zero, coeff_C_ne_zero]

lemma coeff_ge_two_X_add_C (a : α) (h : 2 ≤ n) : coeff (X + C a) n = (0 : α) :=
begin
  rw [coeff_add, coeff_C_ne_zero, add_zero, coeff_X, if_neg (nat.succ_le_iff.mp h).ne],
  exact ne_of_gt (lt_of_lt_of_le zero_lt_two h),
end

lemma nat_degree_prod_X_add_C (n : ℕ) (r : ℕ → α) :
  nat_degree (∏ i in range n, (X + C (r i))) = n :=
begin
  have hnz : ∀ i, X + C (r i) ≠ 0 := λ i, (monic_X_add_C (r i)).ne_zero,
  rw nat_degree_prod,
  { conv_rhs { rw [← card_range n, finset.card_eq_sum_ones] },
    congr, ext x,
    rw ← degree_eq_iff_nat_degree_eq (hnz x),
    simp only [degree_X_add_C, with_top.coe_one], },
  exact λ i _, hnz i,
end

lemma monic_prod_X_add_C (n : ℕ) (r : ℕ → α) : monic (∏ i in range n, (X + C (r i))) :=
monic_prod_of_monic _ _ (λ _ _, monic_X_add_C (r _))

lemma coeff_top (n : ℕ) (r : ℕ → α) : coeff (∏ i in range n, (X + C (r i))) n = 1 :=
begin
  convert (monic_prod_X_add_C n r).leading_coeff,
  exact (nat_degree_prod_X_add_C n r).symm,
end

lemma sum_prod_mul_X_add_C_aux (k n : ℕ) (r : ℕ → α) : ∑ x in range k,
  (∑ A in powerset_len (n - x) (range n),
    ∏ j in A, r j) * (X + C (r n)).coeff (k + 1 - x) = 0 :=
begin
  rw [← nsmul_zero (range k).card, ← sum_const],
  refine sum_congr rfl (λ x hx, _),
  rw [coeff_ge_two_X_add_C, mul_zero],
  rw add_comm k _,
  exact nat.lt_sub_right_of_add_lt (add_lt_add_left (mem_range.mp hx) 1),
end

lemma sum_prod_mul_X_add_C (k n : ℕ) (h : k ≤ n) : ∑ l in range (k + 1),
  (∑ A in powerset_len (n - l) (range n), ∏ j in A, r j) * (X + C (r n)).coeff (k - l) =
  (∑ A in powerset_len (n - k + 1) (range n), ∏ j in A, r j)
    + (∑ A in powerset_len (n - k) (range n), ∏ j in A, r j) * (r n) :=
begin
  rw [sum_range_succ, nat.sub_self, coeff_zero_X_add_C],
  cases k with k, { simp, },
  rw [nat.succ_eq_add_one, sum_range_succ, nat.add_sub_cancel_left, coeff_one_X_add_C, mul_one,
    sum_prod_mul_X_add_C_aux, add_zero, add_comm],
  congr,
  omega nat,
end

lemma sum_prod_insert {n k : ℕ} :
  ∑ A in powerset_len (n - k) (range n), (∏ j in A, r j) * r n =
    ∑ A in powerset_len (n - k) (range n), ∏ j in insert n A, r j :=
begin
  refine sum_congr rfl (λ t ht, _),
  rw [mul_comm, prod_insert],
  intro hn,
  apply @not_mem_range_self n,
  exact mem_of_subset (mem_powerset_len.mp ht).left hn,
end

lemma powerset_len_sum_succ_insert_aux {n k : ℕ} (h : k ≤ n) :
  ∑ a in filter (λ (a : finset ℕ), (insert n a).card = n - k + 1) (range n).powerset,
    ∏ j in insert n a, r j =
  ∑ a in filter (λ (a : finset ℕ), a.card = n - k) (range n).powerset,
    ∏ j in insert n a, r j :=
begin
  refine sum_congr _ (λ _ _, rfl),
  ext,
  rw [mem_filter, mem_filter, and.congr_right_iff],
  intro ha,
  rw card_insert_of_not_mem,
  { exact add_left_inj _, },
  rw mem_powerset at ha,
  intro h,
  apply not_mem_range_self,
  exact mem_of_subset ha h
end

lemma powerset_len_sum_succ_insert (n k : ℕ) (h : k ≤ n) :
  ∑ A in powerset_len (n - k + 1) (range n), ∏ j in A, r j +
  ∑ A in powerset_len (n - k) (range n), ∏ j in insert n A, r j =
  ∑ A in powerset_len (n - k + 1) (range (n + 1)), ∏ j in A, r j :=
begin
  rw [@powerset_len_eq_filter _ _ (range (n + 1)), range_add_one, sum_filter, sum_powerset_insert,
    ← sum_filter, ← sum_filter, ← powerset_len_eq_filter, powerset_len_sum_succ_insert_aux h,
    ← @powerset_len_eq_filter],
  exact not_mem_range_self,
end

/-- A sum version of Vieta's Formulas which shows that the `k`th coefficient of a product
of linear terms `X + r i` is the `k`th symmetric polynomial of the constant terms `r i`. -/
lemma coeff_of_prod_X_add_C :
  ∀ {k : ℕ}, k ≤ n → coeff (∏ i in range n, (X + C (r i))) k
  = ∑ A in (powerset_len (n - k) (range n)), (∏ j in A, r j) :=
begin
  induction n with n ih, { simp, },
  { intros k hk,
    cases nat.of_le_succ hk with h h,
    { calc (∏ i in range (n + 1), (X + C (r i))).coeff k
          = ∑ l in range (k + 1),
            (∏ (i : ℕ) in range n, (X + C (r i))).coeff l * (X + C (r n)).coeff (k - l) :
        by rw [prod_range_succ, mul_comm, coeff_mul, ← nat.sum_antidiagonal_eq_sum_range_succ
            (λ a b, ((range n).prod (λ i, X + C (r i))).coeff a * (X + C (r n)).coeff b) k]
      ... = ∑ l in range (k + 1),
            (∑ A in powerset_len (n - l) (range n), ∏ j in A, r j) * (X + C (r n)).coeff (k - l) :
        begin
          refine sum_congr rfl (λ l hl, _),
          rw ih ((mem_range_succ_iff.mp hl).trans h),
        end
      ... = (∑ A in powerset_len (n - k + 1) (range n), ∏ j in A, r j)
            + (∑ A in powerset_len (n - k) (range n), ∏ j in A, r j) * (r n) :
        sum_prod_mul_X_add_C k n h
      ... = ∑ A in powerset_len (n - k + 1) (range (n + 1)), (∏ j in A, r j) :
        by rwa [sum_mul, sum_prod_insert, powerset_len_sum_succ_insert]
      ... = _ : by { congr, rw [← nat.sub_add_comm h] } },
    { simp only [h, nat.sub_self, powerset_len_zero, sum_singleton],
      exact coeff_top n.succ r } }
end

end vieta
