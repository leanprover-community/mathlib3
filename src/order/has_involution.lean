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

lemma invo_le_invo (hxy : x ≤ y) : yⁱ ≤ xⁱ := invo_antitone' _ _ hxy

lemma le_of_invo_le (hx : xⁱ ≤ yⁱ) : y ≤ x :=
by {rw [←invo_invo x, ←invo_invo y], exact invo_le_invo hx,}

lemma invo_le_invo_iff_le : xⁱ ≤ yⁱ ↔ y ≤ x := ⟨le_of_invo_le, invo_le_invo⟩

lemma le_invo_iff_le_invo : x ≤ yⁱ ↔ y ≤ xⁱ := by rw [←invo_le_invo_iff_le, invo_invo]

lemma invo_le_iff_invo_le : xⁱ ≤ y ↔ yⁱ ≤ x := by rw [←invo_le_invo_iff_le, invo_invo]

lemma invo_inj (h : xⁱ = yⁱ) : x = y := invo_involutive'.injective h

lemma invo_lt_invo_iff_lt : xⁱ < yⁱ ↔ y < x := by simp [lt_iff_le_not_le, invo_le_invo_iff_le]

lemma lt_invo_iff_lt_invo : x < yⁱ ↔ y < xⁱ := by rw [←invo_lt_invo_iff_lt, invo_invo]

lemma invo_lt_iff_invo_lt : xⁱ < y ↔ yⁱ < x := by rw [←invo_lt_invo_iff_lt, invo_invo]

lemma le_invo_of_le_invo (h : y ≤ xⁱ) : x ≤ yⁱ := le_invo_iff_le_invo.mp h

lemma invo_le_of_invo_le (h : yⁱ ≤ x) : xⁱ ≤ y := invo_le_iff_invo_le.mp h

lemma invo_involutive : function.involutive (has_involution.invo : α → α) := invo_invo

lemma invo_bijective : function.bijective (invo : α → α) := invo_involutive.bijective

lemma invo_surjective : function.surjective (invo : α → α) := invo_involutive.surjective

lemma invo_injective : function.injective (invo : α → α) := invo_involutive.injective

lemma invo_antitone : antitone (invo: α → α) := λ a b, invo_le_invo

@[simp] lemma invo_inj_iff : xⁱ = yⁱ ↔ x = y := invo_injective.eq_iff

lemma invo_comp_invo : invo ∘ invo = @id α := funext invo_invo

end preorder

section lattice

variables [lattice α] [has_involution α]

@[simp] lemma invo_inf (x y : α) : (x ⊓ y)ⁱ = xⁱ ⊔ yⁱ :=
le_antisymm (invo_le_iff_invo_le.mpr (le_inf (invo_le_iff_invo_le.mp le_sup_left)
    ((invo_le_iff_invo_le.mp le_sup_right))))
      (sup_le (invo_le_invo inf_le_left) (invo_le_invo inf_le_right))

@[simp] lemma invo_sup (x y : α) : (x ⊔ y)ⁱ = xⁱ ⊓ yⁱ :=
by rw [invo_eq_iff_invo_eq, invo_inf, invo_invo, invo_invo]

end lattice

section boolean_algebra

@[priority 100]
instance boolean_algebra.to_has_involution [boolean_algebra α] : has_involution α :=
{ invo := compl,
  invo_antitone' := λ _ _, compl_le_compl,
  invo_involutive' := compl_involutive }

end boolean_algebra

section hom

variables (α) [preorder α] [has_involution α]

instance order_dual.has_involution : has_involution αᵒᵈ :=
{ invo := λ x, order_dual.to_dual (order_dual.of_dual x)ⁱ,
  invo_antitone' := λ a b h, @invo_antitone' α _ _ b a h,
  invo_involutive' := invo_involutive' }

/-- Taking the involution as an order isomorphism to the order dual. -/
@[simps]
def order_iso.invo : α ≃o αᵒᵈ :=
{ to_fun := order_dual.to_dual ∘ invo,
  inv_fun := invo ∘ order_dual.of_dual,
  left_inv := invo_invo,
  right_inv := invo_invo,
  map_rel_iff' := λ _ _, invo_le_invo_iff_le }

lemma invo_strict_anti : strict_anti (invo : α → α) := (order_iso.invo α).strict_mono

end hom

section antichain

variables [preorder α] [has_involution α] {s : set α}

lemma image_invo (hs : is_antichain (≤) s) :
  is_antichain (≤) (invo '' s) :=
(hs.image_embedding (order_iso.invo α).to_order_embedding).flip

lemma preimage_invo (hs : is_antichain (≤) s) :
  is_antichain (≤) (invo ⁻¹' s) :=
λ a ha a' ha' hne hle, hs ha' ha (λ h, hne (invo_inj_iff.mp h.symm)) (invo_le_invo hle)

end antichain
