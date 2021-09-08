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

  - `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.

  - `num_derangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.

  - `card_derangements_eq_num_derangements`: Proof that `num_derangements` really does compute the
    number of derangements.

  - `num_derangements_sum`: A lemma giving an expression for `num_derangements n` in terms of
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

lemma card_derangements_fin_succ_succ (n : ℕ) :
  card (derangements (fin (n+2))) = (n+1) * card (derangements (fin n)) +
  (n+1) * card (derangements (fin (n+1))) :=
begin
  -- get some basic results about the size of fin (n+1) plus or minus an element
  have card_n' : ∀ a : fin (n+1), card ({a}ᶜ : set (fin (n+1))) = n,
  { intro a,
    simp only [fintype.card_of_finset, set.mem_compl_singleton_iff],
    rw [finset.filter_ne' _ a, finset.card_erase_of_mem (finset.mem_univ a)],
    simp },
  have card_n : ∀ a : fin (n+1), card ({a}ᶜ : set (fin (n+1))) = card (fin n),
  { intro a, rw card_n' a, simp },
  have card_n2 : card (fin (n+2)) = card (option (fin (n+1))) := by simp,
  -- rewrite the LHS and substitute in our fintype-level equivalence
  rw [card_derangements_invariant card_n2,
    card_congr (@derangements_recursion_equiv (fin (n+1)) _)],
  -- push the cardinality through the Σ and ⊕ so that we can use `card_n`
  rw card_sigma,
  simp_rw [card_sum, card_derangements_invariant (card_n _)],
  rw [finset.sum_const, nsmul_eq_mul, finset.card_fin, mul_add],
  norm_cast,
end

/-- The number of derangements on an `n`-element set. -/
def num_derangements : ℕ → ℕ
| 0 := 1
| 1 := 0
| (n + 2) := (n + 1) * (num_derangements n + num_derangements (n+1))

lemma num_derangements_succ {n : ℕ} :
  (num_derangements (n+1) : ℤ) = (n + 1) * (num_derangements n : ℤ) - (-1)^n :=
begin
  induction n with n hn,
  { refl },
  { rw num_derangements,
    push_cast,
    rw hn,
    rw pow_succ,
    ring }
end

lemma card_derangements_fin_eq_num_derangements {n : ℕ} :
  card (derangements (fin n)) = num_derangements n :=
begin
  apply nat.strong_induction_on n,
  clear n, -- to avoid confusion with the n in the hypothesis
  intros n hyp,
  -- knock out cases 0 and 1
  cases n, { refl },
  cases n, { refl },
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_succ_succ`
  rw num_derangements,
  have n_le : n < n + 2 := nat.lt_succ_of_le (nat.le_succ _),
  have n_succ_le : n + 1 < n + 2 := lt_add_one _,
  rw [← hyp n n_le, ← hyp n.succ n_succ_le],
  rw card_derangements_fin_succ_succ,
  rw mul_add,
end

lemma card_derangements_eq_num_derangements (α : Type*) [fintype α] [decidable_eq α] :
  card (derangements α) = num_derangements (card α) :=
begin
  rw ←card_derangements_invariant (card_fin _),
  exact card_derangements_fin_eq_num_derangements,
end

theorem num_derangements_sum (n : ℕ) :
  (num_derangements n : ℤ) = ∑ k in finset.range (n + 1),
  (-1 : ℤ)^k * nat.asc_factorial k (n - k) :=
begin
  induction n with n hn,
  { refl },
  { rw [finset.sum_range_succ, num_derangements_succ, hn, finset.mul_sum, sub_eq_add_neg],
    congr' 1,
    -- show that (n + 1) * (-1)^x * desc_fac x (n - x) = (-1)^x * desc_fac x (n.succ - x)
    { refine finset.sum_congr (refl _) _,
      intros x hx,
      have h_le : x ≤ n := finset.mem_range_succ_iff.mp hx,
      rw [nat.succ_sub h_le, nat.asc_factorial_succ, nat.add_sub_cancel' h_le],
      push_cast,
      ring },
    -- show that -(-1)^n = (-1)^n.succ * desc_fac n.succ (n.succ - n.succ)
    { simp [pow_succ] } }
end
