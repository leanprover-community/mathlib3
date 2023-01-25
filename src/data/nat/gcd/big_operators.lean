/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import data.nat.gcd.basic
import algebra.big_operators.basic

/-! # Lemmas about coprimality with big products.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These lemmas are kept separate from `data.nat.gcd.basic` in order to minimize imports.
-/

namespace nat

open_locale big_operators

/-- See `is_coprime.prod_left` for the corresponding lemma about `is_coprime` -/
lemma coprime_prod_left
  {ι : Type*} {x : ℕ} {s : ι → ℕ} {t : finset ι} :
  (∀ (i : ι), i ∈ t → coprime (s i) x) → coprime (∏ (i : ι) in t, s i) x :=
finset.prod_induction s (λ y, y.coprime x) (λ a b, coprime.mul) (by simp)

/-- See `is_coprime.prod_right` for the corresponding lemma about `is_coprime` -/
lemma coprime_prod_right
  {ι : Type*} {x : ℕ} {s : ι → ℕ} {t : finset ι} :
  (∀ (i : ι), i ∈ t → coprime x (s i)) → coprime x (∏ (i : ι) in t, s i) :=
finset.prod_induction s (λ y, x.coprime y) (λ a b, coprime.mul_right) (by simp)

end nat
