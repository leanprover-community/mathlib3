/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import order.hom.basic
import algebra.hom.equiv.basic
import algebra.ring.basic
import algebra.order.sub.defs

/-!
# Additional results about ordered Subtraction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α β : Type*}

section has_add

variables [preorder α] [has_add α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma add_hom.le_map_tsub [preorder β] [has_add β] [has_sub β] [has_ordered_sub β]
  (f : add_hom α β) (hf : monotone f) (a b : α) :
  f a - f b ≤ f (a - b) :=
by { rw [tsub_le_iff_right, ← f.map_add], exact hf le_tsub_add }

lemma le_mul_tsub {R : Type*} [distrib R] [preorder R] [has_sub R] [has_ordered_sub R]
  [covariant_class R R (*) (≤)] {a b c : R} :
  a * b - a * c ≤ a * (b - c) :=
(add_hom.mul_left a).le_map_tsub (monotone_id.const_mul' a) _ _

lemma le_tsub_mul {R : Type*} [comm_semiring R] [preorder R] [has_sub R] [has_ordered_sub R]
  [covariant_class R R (*) (≤)] {a b c : R} :
  a * c - b * c ≤ (a - b) * c :=
by simpa only [mul_comm _ c] using le_mul_tsub

end has_add

/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
lemma order_iso.map_tsub {M N : Type*} [preorder M] [has_add M] [has_sub M] [has_ordered_sub M]
  [partial_order N] [has_add N] [has_sub N] [has_ordered_sub N] (e : M ≃o N)
  (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) :
  e (a - b) = e a - e b :=
begin
  set e_add : M ≃+ N := { map_add' := h_add, .. e },
  refine le_antisymm _ (e_add.to_add_hom.le_map_tsub e.monotone a b),
  suffices : e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)), by simpa,
  exact e.monotone (e_add.symm.to_add_hom.le_map_tsub e.symm.monotone _ _)
end

/-! ### Preorder -/

section preorder
variables [preorder α]

variables [add_comm_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma add_monoid_hom.le_map_tsub [preorder β] [add_comm_monoid β] [has_sub β]
  [has_ordered_sub β] (f : α →+ β) (hf : monotone f) (a b : α) :
  f a - f b ≤ f (a - b) :=
f.to_add_hom.le_map_tsub hf a b

end preorder
