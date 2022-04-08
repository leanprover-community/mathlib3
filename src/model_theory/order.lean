/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.semantics

/-!
# Ordered First-Ordered Structures
This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions
* `first_order.language.order` is the language consisting of a single relation representing `≤`.
* `first_order.language.order_Structure` is the structure on an ordered type, assigning the symbol
representing `≤` to the actual relation `≤`.
* `first_order.language.is_ordered` points out a specific symbol in a language as representing `≤`.
* `first_order.language.is_ordered_structure` indicates that a structure over a
* `first_order.language.linear_order` and similar define the theories of preorders, partial orders,
and linear orders.

## Main Results
* `partial_order`s model the theory of partial orders, and `linear_order`s model the theory of
linear orders.

-/

universes u v w

namespace first_order
namespace language
open Structure

variables {L : language.{u v}} {α : Type w} {n : ℕ}

/-- The language consisting of a single relation representing `≤`. -/
protected def order : language :=
language.mk₂ empty empty empty empty unit

instance order.Structure [has_le α] : language.order.Structure α :=
Structure.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, (≤))

instance : is_relational (language.order) := language.is_relational_mk₂

instance : subsingleton (language.order.relations n) :=
language.subsingleton_mk₂_relations

/-- A language is ordered if it has a symbol representing `≤`. -/
class is_ordered (L : language.{u v}) := (le_symb : L.relations 2)

export is_ordered (le_symb)

section is_ordered

variables [is_ordered L]

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
def term.le (t₁ t₂ : L.term (α ⊕ fin n)) : L.bounded_formula α n :=
le_symb.bounded_formula₂ t₁ t₂

variable (L)

/-- The language homomorphism sending the unique symbol `≤` of `language.order` to `≤` in an ordered
 language. -/
def order_Lhom : language.order →ᴸ L :=
Lhom.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, le_symb)

end is_ordered

instance : is_ordered language.order := ⟨unit.star⟩

@[simp]
lemma order_Lhom_order : order_Lhom language.order = Lhom.id language.order :=
Lhom.funext (subsingleton.elim _ _) (subsingleton.elim _ _)

instance : is_ordered (L.sum language.order) := ⟨sum.inr is_ordered.le_symb⟩

/-- The theory of preorders. -/
protected def Theory.preorder : language.order.Theory :=
{le_symb.reflexive, le_symb.transitive}

/-- The theory of partial orders. -/
protected def Theory.partial_order : language.order.Theory :=
{le_symb.reflexive, le_symb.antisymmetric, le_symb.transitive}

/-- The theory of linear orders. -/
protected def Theory.linear_order : language.order.Theory :=
{le_symb.reflexive, le_symb.antisymmetric, le_symb.transitive, le_symb.total}

variables (L α)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
def is_ordered_structure [is_ordered L] [has_le α] [L.Structure α] : Prop :=
Lhom.is_expansion_on (order_Lhom L) α

instance is_ordered_structure_has_le [has_le α] :
  is_ordered_structure language.order α :=
begin
  rw [is_ordered_structure, order_Lhom_order],
  exact Lhom.id_is_expansion_on α,
end

instance model_preorder [preorder α] :
  α ⊨ Theory.preorder :=
begin
  simp only [Theory.preorder, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, forall_eq,
    relations.realize_transitive],
  exact ⟨le_refl, λ _ _ _, le_trans⟩
end

instance model_partial_order [partial_order α] :
  α ⊨ Theory.partial_order :=
begin
  simp only [Theory.partial_order, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    forall_eq, relations.realize_transitive],
  exact ⟨le_refl, λ _ _, le_antisymm, λ _ _ _, le_trans⟩,
end

instance model_linear_order [linear_order α] :
  α ⊨ Theory.linear_order :=
begin
  simp only [Theory.linear_order, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    relations.realize_transitive, forall_eq, relations.realize_total],
  exact ⟨le_refl, λ _ _, le_antisymm, λ _ _ _, le_trans, le_total⟩,
end

end language
end first_order
