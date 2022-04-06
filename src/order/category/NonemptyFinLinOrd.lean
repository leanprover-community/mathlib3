/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.fintype.order
import order.category.LinearOrder

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear orders with monotone maps.
This is the index category for simplicial objects.
-/

universes u v

open category_theory

/-- A typeclass for nonempty finite linear orders. -/
class nonempty_fin_lin_ord (α : Type*) extends fintype α, linear_order α :=
(nonempty : nonempty α . tactic.apply_instance)

attribute [instance] nonempty_fin_lin_ord.nonempty

@[priority 100]
instance nonempty_fin_lin_ord.to_bounded_order (α : Type*) [nonempty_fin_lin_ord α] :
  bounded_order α :=
fintype.to_bounded_order α

instance punit.nonempty_fin_lin_ord : nonempty_fin_lin_ord punit :=
{ .. punit.linear_ordered_cancel_add_comm_monoid,
  .. punit.fintype }

instance fin.nonempty_fin_lin_ord (n : ℕ) : nonempty_fin_lin_ord (fin (n+1)) :=
{ .. fin.fintype _,
  .. fin.linear_order }

instance ulift.nonempty_fin_lin_ord (α : Type u) [nonempty_fin_lin_ord α] :
  nonempty_fin_lin_ord (ulift.{v} α) :=
{ nonempty := ⟨ulift.up ⊥⟩,
  .. linear_order.lift equiv.ulift (equiv.injective _),
  .. ulift.fintype _ }

instance (α : Type*) [nonempty_fin_lin_ord α] : nonempty_fin_lin_ord (order_dual α) :=
{ ..order_dual.fintype α }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrd := bundled nonempty_fin_lin_ord

namespace NonemptyFinLinOrd

instance : bundled_hom.parent_projection @nonempty_fin_lin_ord.to_linear_order := ⟨⟩

attribute [derive [large_category, concrete_category]] NonemptyFinLinOrd

instance : has_coe_to_sort NonemptyFinLinOrd Type* := bundled.has_coe_to_sort

/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
def of (α : Type*) [nonempty_fin_lin_ord α] : NonemptyFinLinOrd := bundled.of α

@[simp] lemma coe_of (α : Type*) [nonempty_fin_lin_ord α] : ↥(of α) = α := rfl

instance : inhabited NonemptyFinLinOrd := ⟨of punit⟩

instance (α : NonemptyFinLinOrd) : nonempty_fin_lin_ord α := α.str

instance has_forget_to_LinearOrder : has_forget₂ NonemptyFinLinOrd LinearOrder :=
bundled_hom.forget₂ _ _

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end NonemptyFinLinOrd

lemma NonemptyFinLinOrd_dual_comp_forget_to_LinearOrder :
  NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd LinearOrder =
    forget₂ NonemptyFinLinOrd LinearOrder ⋙ LinearOrder.dual := rfl
