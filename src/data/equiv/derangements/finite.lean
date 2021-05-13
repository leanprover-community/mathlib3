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

import tactic.field_simp
import tactic.ring

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

open equiv fintype
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
  use derangement_congr (equiv_fin α),
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

-- TODO incorporate desc_fac once that lands and you can rebase on top of that
theorem num_derangements_sum (n : ℕ) :
  (num_derangements n : ℚ) = n.factorial * ∑ k in finset.range (n + 1), (-1 : ℚ)^k / k.factorial :=
begin
  refine nat.strong_induction_on n _,
  clear n, -- ???

  intros n hyp,

  -- need to knock out cases n = 0, 1
  cases n,
  { rw num_derangements_0, simp },

  cases n,
  { rw num_derangements_1, simp [finset.sum_range_succ] },

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

  congr,
  -- show that (n+1) n! (-1)^k / k! + (n+1) (n+1)! (-1)^k / k! = (n+2)! (-1)^k / k!
  { funext,
    have : (n+2).factorial = (n + 1) * (n.factorial + (n+1).factorial),
    { simp only [nat.factorial_succ, ← nat.add_one], ring },
    rw this,
    push_cast,
    ring },
  -- show that `(n+1) (n+1)! * (-1)^(n+1) / (n+1)!` (from the n+1 sum) =
  -- `(n+2)! (-1)^(n+1)/(n+1)! + (n+2)! (-1)^(n+2) / (n+2)!` (from the n+2 sum)
  { -- delay factorial simplification until we're done clearing
    -- denominators
    -- TODO this works, but it's kinda silly. why can't i notice that the fraction is
    -- a * b * c / b, and reduce it to a * c (given a proof that b ≠ 0)
    field_simp [nat.factorial_ne_zero, -nat.factorial_succ, -nat.factorial],
    simp only [nat.factorial_succ, pow_succ],
    push_cast,
    ring, },
end
