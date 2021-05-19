/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import data.equiv.basic
import data.equiv.derangements.basic
import data.fintype.basic
import data.fintype.card
import data.set.finite

import tactic.ring
import tactic.zify

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

# Main definitions

  - `num_derangements n`: The number of derangements on an n-element set. For concreteness, `fin n`
    is used.

  - `num_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.

  - `num_derangements_recursive`: A lemma giving a recursive expression for `num_derangements (n+2)`
    in terms of `num_derangements n` and `num_derangements (n+1)`.

  - `num_derangements_sum`: A lemma giving an expression for `num_derangements n` in terms of
    factorials.
-/

open equiv fintype perm
open_locale big_operators

variables {α : Type*} [decidable_eq α] [fintype α]

instance : decidable_pred (@is_derangement α) :=
begin
  intro f,
  apply fintype.decidable_forall_fintype,
end

instance : fintype (derangements α) :=
begin
  have : fintype (perm α) := by apply_instance,
  dsimp [derangements],
  exact set_fintype (set_of is_derangement),
end

/-- The number of derangements on an `n`-element set. -/
def num_derangements (n : ℕ) : ℕ := card (derangements (fin n))

@[simp] lemma num_derangements_invariant (α : Type*) [fintype α] [decidable_eq α] :
  card (derangements α) = num_derangements (card α) :=
begin
  unfold num_derangements,
  apply card_eq.mpr,  -- card_eq because we don't need the specific equivalence
  use derangements_congr (equiv_fin α),
end

theorem num_derangements_recursive (n : ℕ) :
  num_derangements (n+2) = (n+1) * num_derangements n + (n+1) * num_derangements (n+1) :=
begin
  let X := fin(n+1),
  -- TODO why can't it infer the `fintype` instances unless i bestow a name on `everything_but`?
  let everything_but : X → set X := λ a, {a}ᶜ,
  have card_everything_but : ∀ a : X, card (everything_but a) = n,
  { intro a,
    simp only [everything_but, fintype.card_of_finset, set.mem_compl_singleton_iff],
    rw finset.filter_ne' _ a,
    rw finset.card_erase_of_mem (finset.mem_univ a),
    simp },
  have key := card_congr (@derangements_recursion_equiv X _),
  rw [num_derangements_invariant, fintype.card_option, fintype.card_fin] at key,
  simp [card_everything_but, mul_add, key],
end

lemma num_derangements_0 : num_derangements 0 = 1 := rfl

lemma num_derangements_1 : num_derangements 1 = 0 := rfl

theorem num_derangements_sum (n : ℕ) :
  (num_derangements n : ℤ) = ∑ k in finset.range (n + 1), (-1 : ℤ)^k * nat.desc_fac k (n - k) :=
begin
  refine nat.strong_induction_on n _,
  clear n, -- to avoid confusion with the n in the hypothesis
  intros n hyp,
  -- need to knock out cases n = 0, 1
  cases n, { rw num_derangements_0, simp },
  cases n, { rw num_derangements_1, simp [finset.sum_range_succ] },
  -- now we have n ≥ 2
  rw num_derangements_recursive,
  push_cast,
  -- TODO can these proofs be inferred from some tactic? i tried linarith,
  -- but for some reason that didn't work
  rw hyp n (nat.lt_succ_of_le (nat.le_succ _)),
  rw hyp n.succ (lt_add_one _),
  -- push all the constants inside the sums, strip off some trailing terms,
  -- and compare term-wise
  repeat { rw finset.mul_sum },
  conv_lhs { congr, skip, rw finset.sum_range_succ },
  rw [← add_assoc, ← finset.sum_add_distrib],
  conv_rhs {
    rw finset.sum_range_succ,
    rw finset.sum_range_succ,
    rw add_assoc },
  -- now both sides are of the form `sum (x : ℕ) in finset.range(n+1) (...) + (...)`, in such
  -- a way that we can just check that the LHS and RHS match up in each summand
  congr' 1,
  -- show that (n+1) (-1)^k / (n! / k!) + (n+1) (-1)^k ((n+1)! / k!) = (-1)^k ((n+2)! / k!)
  { refine finset.sum_congr rfl _,
    -- introduce k and rewrite the constraint to `k ≤ n`
    intros k h_mem,
    have h_le : k ≤ n := nat.lt_succ_iff.mp (finset.mem_range.mp h_mem),
    have h_le' : k ≤ n.succ := nat.le_succ_of_le h_le,
    -- rw (n.succ-k) to (n-k).succ, and similar
    rw [nat.succ_sub h_le', nat.succ_sub h_le],
    -- expand desc_fac recursively
    repeat {rw nat.desc_fac_succ},
    rw ← nat.add_one,
    zify [h_le],
    ring },
  -- show that `(n+1) * (-1)^(n+1) ((n+1)! / (n+1)!)` (from the n+1 sum) =
  -- `(-1)^(n+1) ((n+2)! / (n+1)!) + (-1)^(n+2) ((n+2)! / (n+2)!)` (from the n+2 sum)
  { -- get rid of all n.succ
    simp only [←nat.add_one, pow_succ],
    -- simplify the arguments to desc_fac, and then evaluate them explicitly
    simp only [nat.sub_self, nat.add_sub_cancel_left, nat.desc_fac_succ, nat.desc_fac_zero],
    push_cast,
    ring },
end
