/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import order.category.NonemptyFinLinOrd.basic

/-! # Nonempty finite linear orders

Nonempty finite linear orders form the index category for simplicial objects.
-/

universe variables u v

open category_theory

section
open_locale classical

instance fin.complete_linear_order (n : ℕ) :
  complete_linear_order (fin (n+1)) :=
{ sup := max,
  le_sup_left := le_max_left,
  le_sup_right := le_max_right,
  sup_le := λ a b c, max_le,
  inf := min,
  inf_le_left := min_le_left,
  inf_le_right := min_le_right,
  le_inf := λ a b c, le_min,
  top := fin.last n,
  le_top := fin.le_last,
  bot := 0,
  bot_le := fin.zero_le,
  Sup := λ s, sorry,
  Inf := λ s, sorry,
  le_Sup := sorry,
  Sup_le := sorry,
  Inf_le := sorry,
  le_Inf := sorry,
  .. fin.decidable_linear_order }

instance fin.nonempty_fin_lin_ord (n : ℕ) :
  nonempty_fin_lin_ord (fin (n+1)) :=
{ nonempty := ⟨0⟩ }

instance ulift.nonempty_fin_lin_ord (α : Type u) [nonempty_fin_lin_ord α] :
  nonempty_fin_lin_ord (ulift.{v} α) := sorry

end

namespace NonemptyFinLinOrd

/-- Lifting across universes -/
@[simps]
def ulift : NonemptyFinLinOrd.{u} ⥤ NonemptyFinLinOrd.{v} :=
{ obj := λ α, @NonemptyFinLinOrd.of (_root_.ulift (fin (fintype.card α))) sorry,
  map := _,
  map_id' := _,
  map_comp' := _ }

/-- Equivalence across universes -/
def ulift_equivalence : NonemptyFinLinOrd.{u} ≌ NonemptyFinLinOrd.{v} :=
{ functor := ulift,
  inverse := ulift,
  unit_iso := _,
  counit_iso := _,
  functor_unit_iso_comp' := _ }

end NonemptyFinLinOrd
