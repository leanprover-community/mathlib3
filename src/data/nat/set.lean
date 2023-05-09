/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import data.set.image

/-!
### Recursion on the natural numbers and `set.range`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace nat
section set

open set

theorem zero_union_range_succ : {0} ∪ range succ = univ :=
by { ext n, cases n; simp }

@[simp] protected lemma range_succ : range succ = {i | 0 < i} :=
by ext (_ | i); simp [succ_pos, succ_ne_zero]

variables {α : Type*}

theorem range_of_succ (f : ℕ → α) : {f 0} ∪ range (f ∘ succ) = range f :=
by rw [← image_singleton, range_comp, ← image_union, zero_union_range_succ, image_univ]

theorem range_rec {α : Type*} (x : α) (f : ℕ → α → α) :
  (set.range (λ n, nat.rec x f n) : set α) =
    {x} ∪ set.range (λ n, nat.rec (f 0 x) (f ∘ succ) n) :=
begin
  convert (range_of_succ _).symm,
  ext n,
  induction n with n ihn,
  { refl },
  { dsimp at ihn ⊢,
    rw ihn }
end

theorem range_cases_on {α : Type*} (x : α) (f : ℕ → α) :
  (set.range (λ n, nat.cases_on n x f) : set α) = {x} ∪ set.range f :=
(range_of_succ _).symm

end set
end nat
