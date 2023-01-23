/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.prod
import data.fintype.sum
import data.int.units

/-!
# fintype instances relating to units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

instance units_int.fintype : fintype ℤˣ :=
⟨{1, -1}, λ x, by cases int.units_eq_one_or x; simp *⟩

@[simp] lemma units_int.univ : (finset.univ : finset ℤˣ) = {1, -1} := rfl

@[simp] theorem fintype.card_units_int : fintype.card ℤˣ = 2 := rfl

instance [monoid α] [fintype α] [decidable_eq α] : fintype αˣ :=
fintype.of_equiv _ (units_equiv_prod_subtype α).symm

instance [monoid α] [finite α] : finite αˣ := finite.of_injective _ units.ext

lemma fintype.card_units [group_with_zero α] [fintype α] [fintype αˣ] :
  fintype.card αˣ = fintype.card α - 1 :=
begin
  classical,
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : α)⟩),
    fintype.card_congr (units_equiv_ne_zero α)],
  have := fintype.card_congr (equiv.sum_compl (= (0 : α))).symm,
  rwa [fintype.card_sum, add_comm, fintype.card_subtype_eq] at this,
end
