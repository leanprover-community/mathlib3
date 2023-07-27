/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import order.conditionally_complete_lattice.basic
import algebra.order.group.type_tags

/-!
# Conditionally complete lattices and groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


section group

variables {α : Type*} {ι : Sort*} {ι' : Sort*}
  [nonempty ι] [nonempty ι'] [conditionally_complete_lattice α] [group α]

@[to_additive]
lemma le_mul_cinfi [covariant_class α α (*) (≤)] {a : α} {g : α} {h : ι → α}
  (H : ∀ j, a ≤ g * h j) : a ≤ g * infi h :=
inv_mul_le_iff_le_mul.mp $ le_cinfi $ λ hi, inv_mul_le_iff_le_mul.mpr $ H _

@[to_additive]
lemma mul_csupr_le [covariant_class α α (*) (≤)] {a : α} {g : α} {h : ι → α}
  (H : ∀ j, g * h j ≤ a) : g * supr h ≤ a :=
@le_mul_cinfi αᵒᵈ _ _ _ _ _ _ _ _ H

@[to_additive]
lemma le_cinfi_mul [covariant_class α α (function.swap (*)) (≤)] {a : α} {g : ι → α} {h : α}
  (H : ∀ i, a ≤ g i * h) : a ≤ infi g * h :=
mul_inv_le_iff_le_mul.mp $ le_cinfi $ λ gi, mul_inv_le_iff_le_mul.mpr $ H _

@[to_additive]
lemma csupr_mul_le [covariant_class α α (function.swap (*)) (≤)] {a : α} {g : ι → α} {h : α}
  (H : ∀ i, g i * h ≤ a) : supr g * h ≤ a :=
@le_cinfi_mul αᵒᵈ _ _ _ _ _ _ _ _ H

@[to_additive]
lemma le_cinfi_mul_cinfi [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]
  {a : α} {g : ι → α} {h : ι' → α} (H : ∀ i j, a ≤ g i * h j) : a ≤ infi g * infi h :=
le_cinfi_mul $ λ i, le_mul_cinfi $ H _

@[to_additive]
lemma csupr_mul_csupr_le [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]
  {a : α} {g : ι → α} {h : ι' → α} (H : ∀ i j, g i * h j ≤ a) : supr g * supr h ≤ a :=
csupr_mul_le $ λ i, mul_csupr_le $ H _

end group
