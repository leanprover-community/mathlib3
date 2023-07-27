/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import data.set.intervals.basic
import order.hom.set

/-!
# Lemmas about images of intervals under order isomorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α β : Type*}
open set

namespace order_iso

section preorder
variables [preorder α] [preorder β]

@[simp] lemma preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' (Iic b) = Iic (e.symm b) :=
by { ext x, simp [← e.le_iff_le] }

@[simp] lemma preimage_Ici (e : α ≃o β) (b : β) : e ⁻¹' (Ici b) = Ici (e.symm b) :=
by { ext x, simp [← e.le_iff_le] }

@[simp] lemma preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' (Iio b) = Iio (e.symm b) :=
by { ext x, simp [← e.lt_iff_lt] }

@[simp] lemma preimage_Ioi (e : α ≃o β) (b : β) : e ⁻¹' (Ioi b) = Ioi (e.symm b) :=
by { ext x, simp [← e.lt_iff_lt] }

@[simp] lemma preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' (Icc a b) = Icc (e.symm a) (e.symm b) :=
by simp [← Ici_inter_Iic]

@[simp] lemma preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' (Ico a b) = Ico (e.symm a) (e.symm b) :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_Ioc (e : α ≃o β) (a b : β) : e ⁻¹' (Ioc a b) = Ioc (e.symm a) (e.symm b) :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' (Ioo a b) = Ioo (e.symm a) (e.symm b) :=
by simp [← Ioi_inter_Iio]

@[simp] lemma image_Iic (e : α ≃o β) (a : α) : e '' (Iic a) = Iic (e a) :=
by rw [e.image_eq_preimage, e.symm.preimage_Iic, e.symm_symm]

@[simp] lemma image_Ici (e : α ≃o β) (a : α) : e '' (Ici a) = Ici (e a) :=
e.dual.image_Iic a

@[simp] lemma image_Iio (e : α ≃o β) (a : α) : e '' (Iio a) = Iio (e a) :=
by rw [e.image_eq_preimage, e.symm.preimage_Iio, e.symm_symm]

@[simp] lemma image_Ioi (e : α ≃o β) (a : α) : e '' (Ioi a) = Ioi (e a) :=
e.dual.image_Iio a

@[simp] lemma image_Ioo (e : α ≃o β) (a b : α) : e '' (Ioo a b) = Ioo (e a) (e b) :=
by rw [e.image_eq_preimage, e.symm.preimage_Ioo, e.symm_symm]

@[simp] lemma image_Ioc (e : α ≃o β) (a b : α) : e '' (Ioc a b) = Ioc (e a) (e b) :=
by rw [e.image_eq_preimage, e.symm.preimage_Ioc, e.symm_symm]

@[simp] lemma image_Ico (e : α ≃o β) (a b : α) : e '' (Ico a b) = Ico (e a) (e b) :=
by rw [e.image_eq_preimage, e.symm.preimage_Ico, e.symm_symm]

@[simp] lemma image_Icc (e : α ≃o β) (a b : α) : e '' (Icc a b) = Icc (e a) (e b) :=
by rw [e.image_eq_preimage, e.symm.preimage_Icc, e.symm_symm]

end preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
def Iic_top [preorder α] [order_top α] : set.Iic (⊤ : α) ≃o α :=
{ map_rel_iff' := λ x y, by refl,
  .. (@equiv.subtype_univ_equiv α (set.Iic (⊤ : α)) (λ x, le_top)), }

/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/
def Ici_bot [preorder α] [order_bot α] : set.Ici (⊥ : α) ≃o α :=
{ map_rel_iff' := λ x y, by refl,
  .. (@equiv.subtype_univ_equiv α (set.Ici (⊥ : α)) (λ x, bot_le)) }

end order_iso
