/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.pairing

/-!
# Equivalences involving `ℕ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines some additional constructive equivalences using `encodable` and the pairing
function on `ℕ`.
-/

open nat function

namespace equiv

variables {α : Type*}

/--
An equivalence between `bool × ℕ` and `ℕ`, by mapping `(tt, x)` to `2 * x + 1` and `(ff, x)` to
`2 * x`.
-/
@[simps] def bool_prod_nat_equiv_nat : bool × ℕ ≃ ℕ :=
{ to_fun := uncurry bit,
  inv_fun := bodd_div2,
  left_inv := λ ⟨b, n⟩, by simp only [bodd_bit, div2_bit, uncurry_apply_pair, bodd_div2_eq],
  right_inv := λ n, by simp only [bit_decomp, bodd_div2_eq, uncurry_apply_pair] }

/--
An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(sum.inl x)` to `2 * x` and `(sum.inr x)` to
`2 * x + 1`.
-/
@[simps symm_apply] def nat_sum_nat_equiv_nat : ℕ ⊕ ℕ ≃ ℕ :=
(bool_prod_equiv_sum ℕ).symm.trans bool_prod_nat_equiv_nat

@[simp] lemma nat_sum_nat_equiv_nat_apply : ⇑nat_sum_nat_equiv_nat = sum.elim bit0 bit1 :=
by ext (x|x); refl

/--
An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
def int_equiv_nat : ℤ ≃ ℕ :=
int_equiv_nat_sum_nat.trans nat_sum_nat_equiv_nat

/--
An equivalence between `α × α` and `α`, given that there is an equivalence between `α` and `ℕ`.
-/
def prod_equiv_of_equiv_nat (e : α ≃ ℕ) : α × α ≃ α :=
calc α × α ≃ ℕ × ℕ : prod_congr e e
      ...  ≃ ℕ     : mkpair_equiv
      ...  ≃ α     : e.symm

end equiv
