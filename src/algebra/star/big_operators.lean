/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.big_operators.basic
import algebra.star.basic

/-! # Big-operators lemmas about `star` algebraic operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These results are kept separate from `algebra.star.basic` to avoid it needing to import `finset`.
-/

variables {R : Type*}

open_locale big_operators

@[simp] lemma star_prod [comm_monoid R] [star_semigroup R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∏ x in s, f x) = ∏ x in s, star (f x) :=
map_prod (star_mul_aut : R ≃* R) _ _

@[simp] lemma star_sum [add_comm_monoid R] [star_add_monoid R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∑ x in s, f x) = ∑ x in s, star (f x) :=
(star_add_equiv : R ≃+ R).map_sum _ _
