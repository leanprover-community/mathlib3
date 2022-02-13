/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import topology.separation

/-!
# Priestley spaces

This file defines Priestley spaces.
-/

open set

variables {α : Type*}

def is_upset (s : set α) : Prop := sorry
def is_downset (s : set α) : Prop := sorry

lemma not_le_or_not_le_of_ne [partial_order α] {a b : α} (h : a ≠ b) : ¬ a ≤ b ∨ ¬ b ≤ a :=
not_and_distrib.1 $ le_antisymm_iff.not.1 h

alias not_le_or_not_le_of_ne ← ne.not_le_or_not_le

/-- A Priestley space is Compactness is often assumed, but we do not include it here. -/
class priestley_space (α : Type*) [preorder α] [topological_space α] :=
(priestley {x y : α} : ¬ x ≤ y → ∃ U : set α, is_clopen U ∧ is_upset U ∧ x ∈ U ∧ y ∉ U)

variables [topological_space α]

section preorder
variables [preorder α] [priestley_space α] {x y : α}

lemma exists_clopen_upset_of_not_le :
  ¬ x ≤ y → ∃ U : set α, is_clopen U ∧ is_upset U ∧ x ∈ U ∧ y ∉ U :=
priestley_space.priestley

lemma exists_clopen_downset_of_not_le (h : ¬ x ≤ y) :
  ∃ U : set α, is_clopen U ∧ is_downset U ∧ x ∉ U ∧ y ∈ U :=
let ⟨U, hU, hU', hx, hy⟩ := exists_clopen_upset_of_not_le h in
  ⟨Uᶜ, hU.compl, sorry, not_not.2 hx, hy⟩

end preorder

section partial_order
variables [partial_order α] [priestley_space α] {x y : α}

instance priestley_space.to_t2_space : t2_space α :=
⟨λ x y h, begin
  obtain (h | h) := h.not_le_or_not_le,
  { obtain ⟨U, hU, hU', hx, hy⟩ := exists_clopen_upset_of_not_le h,
    exact ⟨U, Uᶜ, hU.is_open, hU.compl.is_open, hx, hy, inter_compl_self _⟩ },
  { obtain ⟨U, hU, hU', hy, hx⟩ := exists_clopen_upset_of_not_le h,
    exact ⟨Uᶜ, U, hU.compl.is_open, hU.is_open, hx, hy, compl_inter_se _⟩ }
end⟩

end partial_order
