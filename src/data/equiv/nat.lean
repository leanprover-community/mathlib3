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

open nat

namespace equiv

variables {α : Type*}

/--
An equivalence between `ℕ × ℕ` and `ℕ`, using the `mkpair` and `unpair` functions in
`data.nat.pairing`.
-/
@[simp] def nat_prod_nat_equiv_nat : ℕ × ℕ ≃ ℕ :=
⟨λ p, nat.mkpair p.1 p.2,
 nat.unpair,
 λ p, begin cases p, apply nat.unpair_mkpair end,
 nat.mkpair_unpair⟩

/--
An equivalence between `bool × ℕ` and `ℕ`, by mapping `(tt, x)` to `2 * x + 1` and `(ff, x)` to
`2 * x`.
-/
@[simp] def bool_prod_nat_equiv_nat : bool × ℕ ≃ ℕ :=
⟨λ ⟨b, n⟩, bit b n, bodd_div2,
 λ ⟨b, n⟩, by simp [bool_prod_nat_equiv_nat._match_1, bodd_bit, div2_bit],
 λ n, by simp [bool_prod_nat_equiv_nat._match_1, bit_decomp]⟩

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
