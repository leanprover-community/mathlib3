/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.pairing
import data.pnat.basic

/-!
# Equivalences involving `ℕ`

This file defines some additional constructive equivalences using `encodable` and the pairing
function on `ℕ`.
-/

open nat function

namespace equiv

variables {α : Type*}

/--
An equivalence between `ℕ × ℕ` and `ℕ`, using the `mkpair` and `unpair` functions in
`data.nat.pairing`.
-/
@[simps] def nat_prod_nat_equiv_nat : ℕ × ℕ ≃ ℕ :=
{ to_fun := uncurry mkpair,
  inv_fun := unpair,
  left_inv := λ ⟨m, n⟩, nat.unpair_mkpair m n,
  right_inv := nat.mkpair_unpair }

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
@[simp] def nat_sum_nat_equiv_nat : ℕ ⊕ ℕ ≃ ℕ :=
(bool_prod_equiv_sum ℕ).symm.trans bool_prod_nat_equiv_nat

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
      ...  ≃ ℕ     : nat_prod_nat_equiv_nat
      ...  ≃ α     : e.symm

/--
An equivalence between `ℕ+` and `ℕ`, by mapping `x` in `ℕ+` to `x - 1` in `ℕ`.
-/
def pnat_equiv_nat : ℕ+ ≃ ℕ :=
⟨λ n, pred n.1, succ_pnat,
  λ ⟨n, h⟩, by { cases n, cases h, simp [succ_pnat, h] }, λ n, by simp [succ_pnat] ⟩


end equiv
