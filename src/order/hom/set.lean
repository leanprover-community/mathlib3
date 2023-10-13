/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.hom.basic
import logic.equiv.set
import data.set.image

/-!
# Order homomorphisms and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open order_dual

variables {F α β γ δ : Type*}

namespace order_iso

section has_le

variables [has_le α] [has_le β] [has_le γ]

lemma range_eq (e : α ≃o β) : set.range e = set.univ := e.surjective.range_eq

@[simp] lemma symm_image_image (e : α ≃o β) (s : set α) : e.symm '' (e '' s) = s :=
e.to_equiv.symm_image_image s

@[simp] lemma image_symm_image (e : α ≃o β) (s : set β) : e '' (e.symm '' s) = s :=
e.to_equiv.image_symm_image s

lemma image_eq_preimage (e : α ≃o β) (s : set α) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

@[simp] lemma preimage_symm_preimage (e : α ≃o β) (s : set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
e.to_equiv.preimage_symm_preimage s

@[simp] lemma symm_preimage_preimage (e : α ≃o β) (s : set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
e.to_equiv.symm_preimage_preimage s

@[simp] lemma image_preimage (e : α ≃o β) (s : set β) : e '' (e ⁻¹' s) = s :=
e.to_equiv.image_preimage s

@[simp] lemma preimage_image (e : α ≃o β) (s : set α) : e ⁻¹' (e '' s) = s :=
e.to_equiv.preimage_image s

end has_le

open set

variables [preorder α] [preorder β] [preorder γ]

/-- Order isomorphism between two equal sets. -/
def set_congr (s t : set α) (h : s = t) : s ≃o t :=
{ to_equiv := equiv.set_congr h,
  map_rel_iff' := λ x y, iff.rfl }

/-- Order isomorphism between `univ : set α` and `α`. -/
def set.univ : (set.univ : set α) ≃o α :=
{ to_equiv := equiv.set.univ α,
  map_rel_iff' := λ x y, iff.rfl }

end order_iso

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def strict_mono_on.order_iso {α β} [linear_order α] [preorder β]
  (f : α → β) (s : set α) (hf : strict_mono_on f s) :
  s ≃o f '' s :=
{ to_equiv := hf.inj_on.bij_on_image.equiv _,
  map_rel_iff' := λ x y, hf.le_iff_le x.2 y.2 }

namespace strict_mono

variables {α β} [linear_order α] [preorder β]
variables (f : α → β) (h_mono : strict_mono f) (h_surj : function.surjective f)

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
@[simps apply] protected noncomputable def order_iso : α ≃o set.range f :=
{ to_equiv := equiv.of_injective f h_mono.injective,
  map_rel_iff' := λ a b, h_mono.le_iff_le }

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def order_iso_of_surjective : α ≃o β :=
(h_mono.order_iso f).trans $ (order_iso.set_congr _ _ h_surj.range_eq).trans order_iso.set.univ

@[simp] lemma coe_order_iso_of_surjective :
  (order_iso_of_surjective f h_mono h_surj : α → β) = f :=
rfl

@[simp] lemma order_iso_of_surjective_symm_apply_self (a : α) :
  (order_iso_of_surjective f h_mono h_surj).symm (f a) = a :=
(order_iso_of_surjective f h_mono h_surj).symm_apply_apply _

lemma order_iso_of_surjective_self_symm_apply (b : β) :
  f ((order_iso_of_surjective f h_mono h_surj).symm b) = b :=
(order_iso_of_surjective f h_mono h_surj).apply_symm_apply _

end strict_mono

section boolean_algebra
variables (α) [boolean_algebra α]

/-- Taking complements as an order isomorphism to the order dual. -/
@[simps]
def order_iso.compl : α ≃o αᵒᵈ :=
{ to_fun := order_dual.to_dual ∘ compl,
  inv_fun := compl ∘ order_dual.of_dual,
  left_inv := compl_compl,
  right_inv := compl_compl,
  map_rel_iff' := λ x y, compl_le_compl_iff_le }

theorem compl_strict_anti : strict_anti (compl : α → α) :=
(order_iso.compl α).strict_mono

theorem compl_antitone : antitone (compl : α → α) :=
(order_iso.compl α).monotone

end boolean_algebra
