/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.fin.basic
import data.fintype.sort
import order.category.LinearOrder

/-! # Nonempty finite linear orders

Nonempty finite linear orders form the index category for simplicial objects.
-/

universes u v

open category_theory

/-- A typeclass for nonempty finite linear orders. -/
class nonempty_fin_lin_ord (α : Type*) extends fintype α, linear_order α :=
(nonempty : nonempty α . tactic.apply_instance)

attribute [instance] nonempty_fin_lin_ord.nonempty

@[priority 100]
instance nonempty_fin_lin_ord.order_bot (α : Type*) [h : nonempty_fin_lin_ord α] : order_bot α :=
{ bot := finset.min' finset.univ ⟨classical.arbitrary α, by simp⟩,
  bot_le := λ a, finset.min'_le _ a (by simp),
  ..h }

@[priority 100]
instance nonempty_fin_lin_ord.order_top (α : Type*) [h : nonempty_fin_lin_ord α] : order_top α :=
{ top := finset.max' finset.univ ⟨classical.arbitrary α, by simp⟩,
  le_top := λ a, finset.le_max' _ a (by simp),
  ..h }

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

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrd := bundled nonempty_fin_lin_ord

namespace NonemptyFinLinOrd

instance : bundled_hom.parent_projection @nonempty_fin_lin_ord.to_linear_order := ⟨⟩

attribute [derive [large_category, concrete_category]] NonemptyFinLinOrd

instance : has_coe_to_sort NonemptyFinLinOrd Type* := bundled.has_coe_to_sort

/-- Construct a bundled NonemptyFinLinOrd from the underlying type and typeclass. -/
def of (α : Type*) [nonempty_fin_lin_ord α] : NonemptyFinLinOrd := bundled.of α

instance : inhabited NonemptyFinLinOrd := ⟨of punit⟩

instance (α : NonemptyFinLinOrd) : nonempty_fin_lin_ord α := α.str

end NonemptyFinLinOrd
