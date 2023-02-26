/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.int.order.basic
import data.nat.succ_pred

/-!
# Successors and predecessors of integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we show that `ℤ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/

open function order

namespace int

@[reducible] -- so that Lean reads `int.succ` through `succ_order.succ`
instance : succ_order ℤ :=
{ succ := succ,
  ..succ_order.of_succ_le_iff succ (λ a b, iff.rfl) }

@[reducible] -- so that Lean reads `int.pred` through `pred_order.pred`
instance : pred_order ℤ :=
{ pred := pred,
  pred_le := λ a, (sub_one_lt_of_le le_rfl).le,
  min_of_le_pred := λ a ha, ((sub_one_lt_of_le le_rfl).not_le ha).elim,
  le_pred_of_lt := λ a b, le_sub_one_of_lt,
  le_of_pred_lt := λ a b, le_of_sub_one_lt }

@[simp] lemma succ_eq_succ : order.succ = succ := rfl
@[simp] lemma pred_eq_pred : order.pred = pred := rfl

lemma pos_iff_one_le {a : ℤ} : 0 < a ↔ 1 ≤ a := order.succ_le_iff.symm

lemma succ_iterate (a : ℤ) : ∀ n, succ^[n] a = a + n
| 0       := (add_zero a).symm
| (n + 1) := by { rw [function.iterate_succ', int.coe_nat_succ, ←add_assoc],
    exact congr_arg _ (succ_iterate n) }

lemma pred_iterate (a : ℤ) : ∀ n, pred^[n] a = a - n
| 0       := (sub_zero a).symm
| (n + 1) := by { rw [function.iterate_succ', int.coe_nat_succ, ←sub_sub],
    exact congr_arg _ (pred_iterate n) }

instance : is_succ_archimedean ℤ :=
⟨λ a b h, ⟨(b - a).to_nat,
  by rw [succ_eq_succ, succ_iterate, to_nat_sub_of_le h, ←add_sub_assoc, add_sub_cancel']⟩⟩

instance : is_pred_archimedean ℤ :=
⟨λ a b h, ⟨(b - a).to_nat, by rw [pred_eq_pred, pred_iterate, to_nat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/

protected lemma covby_iff_succ_eq {m n : ℤ} : m ⋖ n ↔ m + 1 = n := succ_eq_iff_covby.symm

@[simp] lemma sub_one_covby (z : ℤ) : z - 1 ⋖ z :=
by rw [int.covby_iff_succ_eq, sub_add_cancel]

@[simp] lemma covby_add_one (z : ℤ) : z ⋖ z + 1 :=
int.covby_iff_succ_eq.mpr rfl

end int

@[simp, norm_cast] lemma nat.cast_int_covby_iff {a b : ℕ} : (a : ℤ) ⋖ b ↔ a ⋖ b :=
by { rw [nat.covby_iff_succ_eq, int.covby_iff_succ_eq], exact int.coe_nat_inj' }

alias nat.cast_int_covby_iff ↔ _ covby.cast_int
