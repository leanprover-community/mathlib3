/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.semantics

/-!

-/

universes u v w

namespace first_order
namespace language
open Structure

variables {L : language.{u v}} {α : Type w} {n : ℕ}

protected def order : language :=
language.mk₂ empty empty empty empty unit

instance order.Structure [has_le α] : language.order.Structure α :=
Structure.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, (≤))

instance : is_relational (language.order) := language.is_relational_mk₂

class is_ordered (L : language.{u v}) := (le_symb : L.relations 2)

namespace is_ordered

variables [is_ordered L]

def term.le (t₁ t₂ : L.term (α ⊕ fin n)) : L.bounded_formula α n :=
le_symb.bounded_formula₂ t₁ t₂

def order_Lhom : language.order →ᴸ L :=
Lhom.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, le_symb)

end is_ordered

instance : is_ordered language.order := ⟨unit.star⟩

instance : is_ordered (L.sum language.order) := ⟨sum.inr is_ordered.le_symb⟩

protected def Theory.partial_order : language.order.Theory :=
{is_ordered.le_symb.antisymmetric, is_ordered.le_symb.transitive}

protected def Theory.linear_order : language.order.Theory :=
{is_ordered.le_symb.antisymmetric, is_ordered.le_symb.transitive, is_ordered.le_symb.reflexive}

variables (L α)

class is_ordered_structure [is_ordered L] [has_le α] [L.Structure α] : Prop :=
(rel_map_le_symb : ∀ (v : fin 2 → α), rel_map (is_ordered.le_symb : L.relations 2) v ↔ v 0 ≤ v 1)

@[simp]
lemma rel_map_le_symb [has_le α] {v : fin 2 → α} :
  Structure.rel_map (is_ordered.le_symb : language.order.relations 2) v ↔ v 0 ≤ v 1 := iff.rfl

instance model_partial_order [partial_order α] :
  α ⊨ Theory.partial_order :=
⟨begin
  rintro φ (rfl | hφ),
  { exact λ _ _, le_antisymm },
  { rw set.eq_of_mem_singleton hφ,
    exact λ _ _ _, le_trans },
end⟩

instance model_linear_order [linear_order α] :
  α ⊨ Theory.linear_order :=
⟨begin
  rintro φ (rfl | rfl | hφ),
  { exact λ _ _, le_antisymm },
  { exact λ _ _ _, le_trans },
  { rw set.eq_of_mem_singleton hφ,
    exact λ _, le_rfl }
end⟩

end language
end first_order
