/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.antisymmetrization
import order.category.Preorder

/-!
# Category of partial orders

This defines `PartialOrder`, the category of partial orders with monotone maps.
-/

open category_theory

universe u

/-- The category of partially ordered types. -/
def PartialOrder := bundled partial_order

namespace PartialOrder

instance : bundled_hom.parent_projection @partial_order.to_preorder := ⟨⟩

attribute [derive [large_category, concrete_category]] PartialOrder

instance : has_coe_to_sort PartialOrder Type* := bundled.has_coe_to_sort

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type*) [partial_order α] : PartialOrder := bundled.of α

@[simp] lemma coe_of (α : Type*) [partial_order α] : ↥(of α) = α := rfl

instance : inhabited PartialOrder := ⟨of punit⟩

instance (α : PartialOrder) : partial_order α := α.str

instance has_forget_to_Preorder : has_forget₂ PartialOrder Preorder := bundled_hom.forget₂ _ _

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : PartialOrder.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def dual : PartialOrder ⥤ PartialOrder :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `PartialOrder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : PartialOrder ≌ PartialOrder :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end PartialOrder

lemma PartialOrder_dual_comp_forget_to_Preorder :
  PartialOrder.dual ⋙ forget₂ PartialOrder Preorder =
    forget₂ PartialOrder Preorder ⋙ Preorder.dual := rfl

/-- `antisymmetrization` as a functor. It is the free functor. -/
def Preorder_to_PartialOrder : Preorder.{u} ⥤ PartialOrder :=
{ obj := λ X, PartialOrder.of (antisymmetrization X (≤)),
  map := λ X Y f, f.antisymmetrization,
  map_id' := λ X,
    by { ext, exact quotient.induction_on' x (λ x, quotient.map'_mk' _ (λ a b, id) _) },
  map_comp' := λ X Y Z f g,
    by { ext, exact quotient.induction_on' x (λ x, order_hom.antisymmetrization_apply_mk _ _) } }

/-- `Preorder_to_PartialOrder` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preorder` to `PartialOrder`. -/
def Preorder_to_PartialOrder_forget_adjunction :
  Preorder_to_PartialOrder.{u} ⊣ forget₂ PartialOrder Preorder :=
adjunction.mk_of_hom_equiv
  { hom_equiv := λ X Y, { to_fun := λ f,
      ⟨f ∘ to_antisymmetrization (≤), f.mono.comp to_antisymmetrization_mono⟩,
    inv_fun := λ f, ⟨λ a, quotient.lift_on' a f $ λ a b h, (antisymm_rel.image h f.mono).eq, λ a b,
      quotient.induction_on₂' a b $ λ a b h, f.mono h⟩,
    left_inv := λ f, order_hom.ext _ _ $ funext $ λ x, quotient.induction_on' x $ λ x, rfl,
    right_inv := λ f, order_hom.ext _ _ $ funext $ λ x, rfl },
  hom_equiv_naturality_left_symm' := λ X Y Z f g,
    order_hom.ext _ _ $ funext $ λ x, quotient.induction_on' x $ λ x, rfl,
  hom_equiv_naturality_right' := λ X Y Z f g, order_hom.ext _ _ $ funext $ λ x, rfl }

/-- `Preorder_to_PartialOrder` and `order_dual` commute. -/
@[simps] def Preorder_to_PartialOrder_comp_to_dual_iso_to_dual_comp_Preorder_to_PartialOrder :
 (Preorder_to_PartialOrder.{u} ⋙ PartialOrder.dual) ≅
    (Preorder.dual ⋙ Preorder_to_PartialOrder) :=
nat_iso.of_components (λ X, PartialOrder.iso.mk $ order_iso.dual_antisymmetrization _) $
  λ X Y f, order_hom.ext _ _ $ funext $ λ x, quotient.induction_on' x $ λ x, rfl
