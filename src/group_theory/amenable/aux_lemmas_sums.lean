/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import data.real.basic


import topology.category.Top

import algebra.big_operators.basic
import algebra.big_operators.order


/-!

# Auxiliary Lemmas on Sums

This file collects some auxiliary lemmas on sums over finsets.

## Implementation Notes

TODO : These statements are probably already in the mathlib
(probably in some more general form). These lemmas may be
replaced by / moved to different parts of the mathlib.

-/


open_locale big_operators -- to enable ∑ notation

open classical

lemma sum_scalar {α : Type*} {S:finset α}
  {f: α → ℝ}
  (r:ℝ)
  : ∑ x in S, (r *  (f x)) = r *  (∑ x in S, f x )
:= begin
  classical,
  apply finset.induction_on S,
    --case emptyset
    simp,
  assume a s a_nin_s,
  assume ind_hyp,
  calc  ∑ (x : α) in insert a s, r * f x
      = (∑ (x : α) in s, r * f x) + (r * f a)
        : by finish
  ... =  r* (∑ (x : α) in s, f x) + r * f a
        : by simp [ind_hyp]
  ... = r * ((∑ (x : α) in s, f x) + f a )
        : by ring
  ... = r * ∑ (x : α) in insert a s,  f x
        : by finish,
end

/--For the difference between summing over S and T, we can
take sums over the relative complements-/
lemma symm_diff_of_diff_sum
  {α : Type*} [decidable_eq α]
  {S T:finset α}
  {f: α → ℝ}
  : ∑ x in S, f x - ∑ x in T, f x
  = ∑ x in S \ T, f x - ∑ x in T \ S, f x
:= begin
  apply finset.induction_on S,
    by simp,
  assume a s a_nin_s,
  assume ind_hyp,
  rw finset.sum_insert a_nin_s,
  by_cases a_in_T : a ∈ T,
  {
    have h₁ : insert a s \ T = s \ T,
    {
      ext x,
      split,
      {
        assume xinL,
        simp at xinL,
        simp,
        finish,
      },
      assume xinR,
      simp at xinR,
      simp,
      split,
      {
        right,
        exact xinR.left,
      },
      exact xinR.right,
    },
    have h₂ : T \ s = insert a (T \ (insert a s)),
    {
      ext x,
      simp,
      split,
      {
        intro xin,
        by_cases xa: x=a,
          left,
          exact xa,
        right,
        apply and.intro xin.left,
        push_neg,
        apply and.intro xa,
        exact xin.right,
      },
      intro xin,
      cases xin,
      {
        rw xin,
        exact ⟨a_in_T, a_nin_s⟩,
      },
      apply and.intro xin.left,
      push_neg at xin,
      exact xin.right.right,
    },
    have h₃ : a ∉ T \ insert a s :=  by simp,
    calc  f a + ∑ (x : α) in s, f x - ∑ (x : α) in T, f x
        = f a + (∑ (x : α) in s, f x - ∑ (x : α) in T, f x)
          : by ring
    ... = f a + (∑ (x : α) in s \ T, f x - ∑ (x : α) in T \ s, f x)
          : by rw ind_hyp
    ... = f a + (∑ (x : α) in (insert a s) \ T, f x - ∑ (x : α) in T \ s, f x)
          : by rw h₁
    ... = f a + (∑ (x : α) in (insert a s) \ T, f x - ∑ (x : α) in insert a (T \ (insert a s)), f x)
          : by rw h₂
    ... = f a + (∑ (x : α) in (insert a s) \ T, f x - (f a + ∑ (x : α) in (T \ (insert a s)), f x))
          : by rw finset.sum_insert h₃
    ... = ∑ (x : α) in insert a s \ T, f x - ∑ (x : α) in T \ insert a s, f x
          : by ring,
  },
  {
    have h₁ : insert a s \ T = insert a (s \ T),
    {
      ext x,
      simp,
      split,
      {
        intro xin,
        cases xin.left with xa xins,
          left,
          exact xa,
        right,
        exact ⟨xins, xin.right⟩,
      },
      intro xin,
      split,
      {
        cases xin with xa xins,
            left,
            exact xa,
        right,
        exact xins.left
      },
      cases xin with xa xalt,
      {
        rw xa,
        exact a_in_T,
      },
      exact xalt.right,
    },
    have h₂ : T \ s = T \ (insert a s),
    {
      ext x,
      split,
      {
        intro xin,
        simp at xin,
        simp,
        apply and.intro xin.left,
        push_neg,
        split,
          intro h,
          rw ← h at a_in_T,
          exact a_in_T xin.left,
        exact xin.right,
      },
      intro xin,
      simp at xin,
      simp,
      tauto,
    },
    have h₃ : a ∉ s \ T,
    {
      simp,
      intro h,
      exfalso,
      exact a_nin_s h,
    },
    calc  f a + ∑ (x : α) in s, f x - ∑ (x : α) in T, f x
        = f a + (∑ (x : α) in s, f x - ∑ (x : α) in T, f x)
          : by ring
    ... = f a + (∑ (x : α) in s \ T, f x - ∑ (x : α) in T \ s, f x)
          : by rw ind_hyp
    ... = (f a + ∑ (x : α) in s \ T, f x) - ∑ (x : α) in T \ s, f x
          : by ring
    ... = ∑ (x : α) in insert a (s \ T), f x - ∑ (x : α) in T \ s, f x
          : by rw finset.sum_insert h₃
    ... = ∑ (x : α) in insert a s \ T, f x - ∑ (x : α) in T \ s, f x
          : by rw h₁
    ... = ∑ (x : α) in insert a s \ T, f x - ∑ (x : α) in T \ insert a s, f x
          : by rw h₂,
  },
end

lemma abs_le_symm_diff_of_diff_sum
  {α : Type*} [decidable_eq α]
  {S T:finset α}
  {f: α → ℝ}
  : |∑ x in S, f x - ∑ x in T, f x|
  ≤ ∑ x in symm_diff S T, |f x|
:= begin
  calc  |∑ x in S, f x - ∑ x in T, f x|
      = |∑ x in S \ T, f x - ∑ x in T \ S, f x|
        : by rw symm_diff_of_diff_sum
  ... ≤ |∑ x in S \ T, f x| + |∑ x in T \ S, f x|
        : abs_sub _ _
  ... ≤ ∑ x in S \ T, |f x| + ∑ x in T \ S, |f x|
        : by {
          apply add_le_add; exact finset.abs_sum_le_sum_abs _ _,
        }
  ... = ∑ x in symm_diff S T, |f x|
        : by {
          dsimp[symm_diff],
          exact eq.symm (finset.sum_union (begin
            unfold disjoint,
            assume x xininters,
            finish,
          end)),
        },
end
