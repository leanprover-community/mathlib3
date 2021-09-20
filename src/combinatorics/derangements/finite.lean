/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import combinatorics.derangements.basic
import data.fintype.card
import tactic.delta_instance
import tactic.ring

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

# Main definitions

* `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.
* `num_derangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.
* `card_derangements_eq_num_derangements`: Proof that `num_derangements` really does compute the
    number of derangements.
* `num_derangements_sum`: A lemma giving an expression for `num_derangements n` in terms of
    factorials.
-/

open derangements equiv fintype
open_locale big_operators

variables {α : Type*} [decidable_eq α] [fintype α]

instance : decidable_pred (derangements α) := λ _, fintype.decidable_forall_fintype

instance : fintype (derangements α) := by delta_instance derangements

lemma card_derangements_invariant {α β : Type*} [fintype α] [decidable_eq α]
  [fintype β] [decidable_eq β] (h : card α = card β) :
  card (derangements α) = card (derangements β) :=
fintype.card_congr (equiv.derangements_congr $ equiv_of_card_eq h)

lemma card_derangements_fin_add_two (n : ℕ) :
  card (derangements (fin (n+2))) = (n+1) * card (derangements (fin n)) +
  (n+1) * card (derangements (fin (n+1))) :=
begin
  -- get some basic results about the size of fin (n+1) plus or minus an element
  have h1 : ∀ a : fin (n+1), card ({a}ᶜ : set (fin (n+1))) = card (fin n),
  { intro a,
    simp only [fintype.card_fin, finset.card_fin, fintype.card_of_finset, finset.filter_ne' _ a,
      set.mem_compl_singleton_iff, finset.card_erase_of_mem (finset.mem_univ a), nat.pred_succ] },
  have h2 : card (fin (n+2)) = card (option (fin (n+1))),
  { simp only [card_fin, card_option] },
  -- rewrite the LHS and substitute in our fintype-level equivalence
  simp only [card_derangements_invariant h2,
    card_congr (@derangements_recursion_equiv (fin (n+1)) _),
  -- push the cardinality through the Σ and ⊕ so that we can use `card_n`
    card_sigma, card_sum, card_derangements_invariant (h1 _), finset.sum_const, nsmul_eq_mul,
    finset.card_fin, mul_add, nat.cast_id],
end

/-- The number of derangements of an `n`-element set. -/
def num_derangements : ℕ → ℕ
| 0 := 1
| 1 := 0
| (n + 2) := (n + 1) * (num_derangements n + num_derangements (n+1))

@[simp] lemma num_derangements_zero : num_derangements 0 = 1 := rfl

@[simp] lemma num_derangements_one : num_derangements 1 = 0 := rfl

lemma num_derangements_add_two (n : ℕ) :
  num_derangements (n+2) = (n+1) * (num_derangements n + num_derangements (n+1)) := rfl

lemma num_derangements_succ (n : ℕ) :
  (num_derangements (n+1) : ℤ) = (n + 1) * (num_derangements n : ℤ) - (-1)^n :=
begin
  induction n with n hn,
  { refl },
  { simp only [num_derangements_add_two, hn, pow_succ,
      int.coe_nat_mul, int.coe_nat_add, int.coe_nat_succ],
    ring }
end

lemma card_derangements_fin_eq_num_derangements {n : ℕ} :
  card (derangements (fin n)) = num_derangements n :=
begin
  induction n using nat.strong_induction_on with n hyp,
  obtain (_|_|n) := n, { refl }, { refl },  -- knock out cases 0 and 1
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [num_derangements_add_two, card_derangements_fin_add_two, mul_add,
    hyp _ (nat.lt_add_of_pos_right zero_lt_two), hyp _ (lt_add_one _)],
end

lemma card_derangements_eq_num_derangements (α : Type*) [fintype α] [decidable_eq α] :
  card (derangements α) = num_derangements (card α) :=
begin
  rw ←card_derangements_invariant (card_fin _),
  exact card_derangements_fin_eq_num_derangements,
end

theorem num_derangements_sum (n : ℕ) :
  (num_derangements n : ℤ) = ∑ k in finset.range (n + 1), (-1:ℤ)^k * nat.asc_factorial k (n - k) :=
begin
  induction n with n hn, { refl },
  rw [finset.sum_range_succ, num_derangements_succ, hn, finset.mul_sum, nat.sub_self,
    nat.asc_factorial_zero, int.coe_nat_one, mul_one, pow_succ, neg_one_mul, sub_eq_add_neg,
    add_left_inj, finset.sum_congr rfl],
  -- show that (n + 1) * (-1)^x * asc_fac x (n - x) = (-1)^x * asc_fac x (n.succ - x)
  intros x hx,
  have h_le : x ≤ n := finset.mem_range_succ_iff.mp hx,
  rw [nat.succ_sub h_le, nat.asc_factorial_succ, nat.add_sub_cancel' h_le,
    int.coe_nat_mul, int.coe_nat_succ, mul_left_comm],
end
