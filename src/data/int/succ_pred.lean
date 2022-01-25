/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.int.basic
import order.succ_pred

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/

open function int

@[reducible] -- so that Lean reads `int.succ` through `succ_order.succ`
instance : succ_order ℤ :=
{ succ := succ,
  ..succ_order.of_succ_le_iff succ (λ a b, iff.rfl) }

@[reducible] -- so that Lean reads `int.pred` through `pred_order.pred`
instance : pred_order ℤ :=
{ pred := pred,
  pred_le := λ a, (sub_one_lt_of_le le_rfl).le,
  minimal_of_le_pred := λ a ha, ((sub_one_lt_of_le le_rfl).not_le ha).elim,
  le_pred_of_lt := λ a b, le_sub_one_of_lt,
  le_of_pred_lt := λ a b, le_of_sub_one_lt }

lemma int.succ_iterate (a : ℤ) : ∀ n, succ^[n] a = a + n
| 0       := (add_zero a).symm
| (n + 1) := by { rw [function.iterate_succ', int.coe_nat_succ, ←add_assoc],
    exact congr_arg _ (int.succ_iterate n) }

lemma int.pred_iterate (a : ℤ) : ∀ n, pred^[n] a = a - n
| 0       := (sub_zero a).symm
| (n + 1) := by { rw [function.iterate_succ', int.coe_nat_succ, ←sub_sub],
    exact congr_arg _ (int.pred_iterate n) }

instance : is_succ_archimedean ℤ :=
⟨λ a b h, ⟨(b - a).to_nat,
  by rw [int.succ_iterate, int.to_nat_sub_of_le h, ←add_sub_assoc, add_sub_cancel']⟩⟩

instance : is_pred_archimedean ℤ :=
⟨λ a b h, ⟨(b - a).to_nat, by rw [int.pred_iterate, int.to_nat_sub_of_le h, sub_sub_cancel]⟩⟩
