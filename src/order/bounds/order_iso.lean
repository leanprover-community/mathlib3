/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import order.bounds.basic
import order.hom.set

/-!
# Order isomorhpisms and bounds.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α β : Type*}
open set

namespace order_iso

variables [preorder α] [preorder β] (f : α ≃o β)

lemma upper_bounds_image {s : set α} :
  upper_bounds (f '' s) = f '' upper_bounds s :=
subset.antisymm
  (λ x hx, ⟨f.symm x, λ y hy, f.le_symm_apply.2 (hx $ mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
  f.monotone.image_upper_bounds_subset_upper_bounds_image

lemma lower_bounds_image {s : set α} : lower_bounds (f '' s) = f '' lower_bounds s :=
@upper_bounds_image αᵒᵈ βᵒᵈ _ _ f.dual _

@[simp] lemma is_lub_image {s : set α} {x : β} :
  is_lub (f '' s) x ↔ is_lub s (f.symm x) :=
⟨λ h, is_lub.of_image (λ _ _, f.le_iff_le) ((f.apply_symm_apply x).symm ▸ h),
  λ h, is_lub.of_image (λ _ _, f.symm.le_iff_le) $ (f.symm_image_image s).symm ▸ h⟩

lemma is_lub_image' {s : set α} {x : α} :
  is_lub (f '' s) (f x) ↔ is_lub s x :=
by rw [is_lub_image, f.symm_apply_apply]

@[simp] lemma is_glb_image {s : set α} {x : β} :
  is_glb (f '' s) x ↔ is_glb s (f.symm x) :=
f.dual.is_lub_image

lemma is_glb_image' {s : set α} {x : α} :
  is_glb (f '' s) (f x) ↔ is_glb s x :=
f.dual.is_lub_image'

@[simp] lemma is_lub_preimage {s : set β} {x : α} :
  is_lub (f ⁻¹' s) x ↔ is_lub s (f x) :=
by rw [← f.symm_symm, ← image_eq_preimage, is_lub_image]

lemma is_lub_preimage' {s : set β} {x : β} :
  is_lub (f ⁻¹' s) (f.symm x) ↔ is_lub s x :=
by rw [is_lub_preimage, f.apply_symm_apply]

@[simp] lemma is_glb_preimage {s : set β} {x : α} :
  is_glb (f ⁻¹' s) x ↔ is_glb s (f x) :=
f.dual.is_lub_preimage

lemma is_glb_preimage' {s : set β} {x : β} :
  is_glb (f ⁻¹' s) (f.symm x) ↔ is_glb s x :=
f.dual.is_lub_preimage'

end order_iso
