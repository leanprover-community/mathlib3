/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pointwise
import order.filter.pointwise

/-!
# Ensuring priority of the `ℕ` and `ℤ` actions over pointwise ones

See Note [pointwise nat action].
-/

open_locale pointwise

variables {α β : Type*} [add_group α] [decidable_eq α] [group β] [decidable_eq β]

-- It is ok for the proofs to stop being `rfl`, but these statements should remain true
example (s : set α) (n : ℕ) : n • s = nsmul_rec n s := rfl
example (s : set α) (n : ℤ) : n • s = zsmul_rec n s := rfl
example (s : set β) (n : ℕ) : s ^ n = npow_rec n s := rfl
example (s : set β) (n : ℤ) : s ^ n = zpow_rec n s := rfl
example (s : finset α) (n : ℕ) : n • s = nsmul_rec n s := rfl
example (s : finset α) (n : ℤ) : n • s = zsmul_rec n s := rfl
example (s : finset β) (n : ℕ) : s ^ n = npow_rec n s := rfl
example (s : finset β) (n : ℤ) : s ^ n = zpow_rec n s := rfl
example (s : filter α) (n : ℕ) : n • s = nsmul_rec n s := rfl
example (s : filter α) (n : ℤ) : n • s = zsmul_rec n s := rfl
example (s : filter β) (n : ℕ) : s ^ n = npow_rec n s := rfl
example (s : filter β) (n : ℤ) : s ^ n = zpow_rec n s := rfl

example : 2 • ({2, 3} : finset ℕ) = {4, 5, 6} := rfl
example : ({2, 3}^2 : finset ℕ) = {4, 6, 9} := rfl
