/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import order.antichain

/-!
# Orders with involution

This file concerns orders that admit an order-reversing involution. In the case of a lattice,
these are sometimes referred to as 'i-lattices' or 'lattices with involution'. Such an involution
is more general than a `boolean_algebra` complement, but retains many of its properties. Other than
a boolean algebra, an example is the subspace lattice of the vector space `𝕂ⁿ` for `𝕂` of nonzero
characteristic, where for each subspace `W` we have `invo W = {x ∈ V | ∀ w ∈ W, wᵀx = 0}`; this is
not a complement in the stronger sense because `invo W` can intersect `W`.

## Main declarations

* `has_involution`: typeclass applying to types with a `preorder` that admit an antitone involution.

* `ⁱ` : postfix notation for the function `invo : α → α` given a type `α` with `[has_involution α]`

## TODO

Provide instances other than the one from `boolean_algebra`.
-/

universe u

class has_involution (α : Type u) [preorder α]  :=
(invo : α → α)
(invo_antitone' : ∀ (x y : α), x ≤ y → invo y ≤ invo x)
(invo_involutive' : function.involutive invo)

open has_involution

variables {α : Type u}

postfix `ⁱ`:(max+1) := invo

section preorder

variables [preorder α] [has_involution α] {x y : α}

@[simp] lemma invo_invo (x : α) : xⁱⁱ = x :=  invo_involutive' x

lemma invo_eq_iff_invo_eq : xⁱ = y ↔ yⁱ = x :=
by {rw [eq_comm], exact invo_involutive'.eq_iff.symm}

lemma eq_invo_iff_eq_invo : x = yⁱ ↔ y = xⁱ :=
by rw [← invo_invo x, invo_eq_iff_invo_eq, invo_invo, invo_invo]

lemma invo_le_invo (h : x ≤ y) : yⁱ ≤ xⁱ := invo_antitone' _ _ h

lemma le_of_invo_le (h : xⁱ ≤ yⁱ) : y ≤ x :=
by {rw [←invo_invo x, ←invo_invo y], exact invo_le_invo h,}

lemma invo_le_invo_iff_le : xⁱ ≤ yⁱ ↔ y ≤ x := ⟨le_of_invo_le, invo_le_invo⟩

lemma le_invo_iff_le_invo : x ≤ yⁱ ↔ y ≤ xⁱ := by rw [←invo_le_invo_iff_le, invo_invo]

lemma invo_le_iff_invo_le : xⁱ ≤ y ↔ yⁱ ≤ x := by rw [←invo_le_invo_iff_le, invo_invo]

lemma invo_inj (h : xⁱ = yⁱ) : x = y := invo_involutive'.injective h

lemma invo_lt_invo_iff_lt : xⁱ < yⁱ ↔ y < x := by simp [lt_iff_le_not_le, invo_le_invo_iff_le]

lemma lt_invo_iff_lt_invo : x < yⁱ ↔ y < xⁱ := by rw [←invo_lt_invo_iff_lt, invo_invo]

lemma invo_lt_iff_invo_lt : xⁱ < y ↔ yⁱ < x := by rw [←invo_lt_invo_iff_lt, invo_invo]

lemma le_invo_of_le_invo (h : y ≤ xⁱ) : x ≤ yⁱ := le_invo_iff_le_invo.mp h

lemma invo_le_of_invo_le (h : yⁱ ≤ x) : xⁱ ≤ y := invo_le_iff_invo_le.mp h

lemma invo_involutive : function.involutive (invo : α → α) := invo_invo

lemma invo_bijective : function.bijective (invo : α → α) := invo_involutive.bijective

lemma invo_surjective : function.surjective (invo : α → α) := invo_involutive.surjective

lemma invo_injective : function.injective (invo : α → α) := invo_involutive.injective

lemma invo_antitone : antitone (invo: α → α) := λ _ _, invo_le_invo

@[simp] lemma invo_inj_iff : xⁱ = yⁱ ↔ x = y := invo_injective.eq_iff

lemma invo_comp_invo : invo ∘ invo = @id α := funext invo_invo

/-- Taking the involution as an order isomorphism to the order dual. -/
@[simps]
def order_iso.invo (α) [preorder α] [has_involution α] : α ≃o αᵒᵈ :=
{ to_fun := λ x, order_dual.to_dual (xⁱ),
  inv_fun := invo ∘ order_dual.of_dual,
  left_inv := invo_invo,
  right_inv := invo_invo,
  map_rel_iff' := λ _ _, invo_le_invo_iff_le }

@[priority 100]
instance order_dual.has_involution : has_involution αᵒᵈ :=
{ invo := λ x, order_dual.to_dual (order_dual.of_dual x)ⁱ,
  invo_antitone' := λ a b h, @invo_antitone' α _ _ b a h,
  invo_involutive' := invo_involutive' }

lemma invo_strict_anti : strict_anti (invo : α → α) := (order_iso.invo α).strict_mono

end preorder

section boolean_algebra

@[priority 100]
instance boolean_algebra.to_has_involution [boolean_algebra α] : has_involution α :=
{ invo := compl,
  invo_antitone' := λ _ _, compl_le_compl,
  invo_involutive' := compl_involutive }

end boolean_algebra

section lattice

variables [lattice α] [has_involution α] {x y : α}

lemma invo_sup : (x ⊔ y)ⁱ = xⁱ ⊓ yⁱ := @order_iso.map_sup α αᵒᵈ _ _ (order_iso.invo α) x y

lemma invo_inf : (x ⊓ y)ⁱ = xⁱ ⊔ yⁱ := @order_iso.map_inf α αᵒᵈ _ _ (order_iso.invo α) x y

end lattice

section image

variables [preorder α] [has_involution α] {s : set α} {x y : α}

open set order_dual

lemma image_invo_eq_preimage_invo : invo '' s = invo ⁻¹' s :=
ext (λ x, ⟨by {rintro ⟨x',hx',rfl⟩, rwa [←invo_invo x'] at hx'}, λ h, ⟨xⁱ, ⟨h, invo_invo x⟩⟩⟩)

@[simp] lemma invo_invo_image : invo '' (invo '' s) = s := by {ext, simp}

lemma mem_image_invo {x : α} {s : set α} : x ∈ invo '' s ↔ xⁱ ∈ s :=
by {rw image_invo_eq_preimage_invo, refl}

lemma mem_image_invo' {x : α} {P : α → Prop} : (invo '' P) x ↔ P xⁱ := mem_image_invo

lemma mem_preimage_invo' {x : α} {P : α → Prop} : (invo ⁻¹' P) x ↔ P xⁱ :=
by rw [←image_invo_eq_preimage_invo, mem_image_invo']

lemma is_antichain.image_invo (hs : is_antichain (≤) s) : is_antichain (≤) (invo '' s) :=
(hs.image_embedding (order_iso.invo α).to_order_embedding).flip

lemma is_antichain.preimage_invo (hs : is_antichain (≤) s) : is_antichain (≤) (invo ⁻¹' s) :=
image_invo_eq_preimage_invo.subst hs.image_invo

@[simp] lemma preimage_invo_Iic : invo ⁻¹' (Iic x) = Ici xⁱ := ext (λ _, invo_le_iff_invo_le)

@[simp] lemma preimage_invo_Ici : invo ⁻¹' (Ici x) = Iic xⁱ := ext (λ _, le_invo_iff_le_invo)

@[simp] lemma preimage_invo_Iio : invo ⁻¹' (Iio x) = Ioi xⁱ := ext (λ _, invo_lt_iff_invo_lt)

@[simp] lemma preimage_invo_Ioi : invo ⁻¹' (Ioi x) = Iio xⁱ := ext (λ _, lt_invo_iff_lt_invo)

@[simp] lemma preimage_invo_Icc : invo ⁻¹' (Icc x y) = Icc yⁱ xⁱ :=
by simp [←Iic_inter_Ici, inter_comm]

@[simp] lemma preimage_invo_Ioo : invo ⁻¹' (Ioo x y) = Ioo yⁱ xⁱ :=
by simp [←Iio_inter_Ioi, inter_comm]

@[simp] lemma preimage_invo_Ico : invo ⁻¹' (Ico x y) = Ioc yⁱ xⁱ :=
by simp [←Iio_inter_Ici, ←Iic_inter_Ioi, inter_comm]

@[simp] lemma preimage_invo_Ioc : invo ⁻¹' (Ioc x y) = Ico yⁱ xⁱ :=
by simp [←Iio_inter_Ici, ←Iic_inter_Ioi, inter_comm]

@[simp] lemma image_invo_Iic : invo '' (Iic x) = Ici xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Iic]

@[simp] lemma image_invo_Ici : invo '' (Ici x) = Iic xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Ici]

@[simp] lemma image_invo_Iio : invo '' (Iio x) = Ioi xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Iio]

@[simp] lemma image_invo_Ioi : invo '' (Ioi x) = Iio xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Ioi]

@[simp] lemma image_invo_Icc : invo '' (Icc x y) = Icc yⁱ xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Icc]

@[simp] lemma image_invo_Ioo : invo '' (Ioo x y) = Ioo yⁱ xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Ioo]

@[simp] lemma image_invo_Ioc : invo '' (Ioc x y) = Ico yⁱ xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Ioc]

@[simp] lemma image_invo_Ico : invo '' (Ico x y) = Ioc yⁱ xⁱ :=
by rw [image_invo_eq_preimage_invo, preimage_invo_Ico]

end image
