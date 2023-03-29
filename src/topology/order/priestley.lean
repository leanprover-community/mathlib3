/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.upper_lower.basic
import topology.separation

/-!
# Priestley spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines Priestley spaces. A Priestley space is an ordered compact topological space such
that any two distinct points can be separated by a clopen upper set.

## Main declarations

* `priestley_space`: Prop-valued mixin stating the Priestley separation axiom: Any two distinct
  points can be separated by a clopen upper set.

## Implementation notes

We do not include compactness in the definition, so a Priestley space is to be declared as follows:
`[preorder α] [topological_space α] [compact_space α] [priestley_space α]`

## References

* [Wikipedia, *Priestley space*](https://en.wikipedia.org/wiki/Priestley_space)
* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
-/

open set

variables {α : Type*}

/-- A Priestley space is an ordered topological space such that any two distinct points can be
separated by a clopen upper set. Compactness is often assumed, but we do not include it here. -/
class priestley_space (α : Type*) [preorder α] [topological_space α] :=
(priestley {x y : α} : ¬ x ≤ y → ∃ U : set α, is_clopen U ∧ is_upper_set U ∧ x ∈ U ∧ y ∉ U)

variables [topological_space α]

section preorder
variables [preorder α] [priestley_space α] {x y : α}

lemma exists_clopen_upper_of_not_le :
  ¬ x ≤ y → ∃ U : set α, is_clopen U ∧ is_upper_set U ∧ x ∈ U ∧ y ∉ U :=
priestley_space.priestley

lemma exists_clopen_lower_of_not_le (h : ¬ x ≤ y) :
  ∃ U : set α, is_clopen U ∧ is_lower_set U ∧ x ∉ U ∧ y ∈ U :=
let ⟨U, hU, hU', hx, hy⟩ := exists_clopen_upper_of_not_le h in
  ⟨Uᶜ, hU.compl, hU'.compl, not_not.2 hx, hy⟩

end preorder

section partial_order
variables [partial_order α] [priestley_space α] {x y : α}

lemma exists_clopen_upper_or_lower_of_ne (h : x ≠ y) :
  ∃ U : set α, is_clopen U ∧ (is_upper_set U ∨ is_lower_set U) ∧ x ∈ U ∧ y ∉ U :=
begin
  obtain (h | h) := h.not_le_or_not_le,
  { exact (exists_clopen_upper_of_not_le h).imp (λ U, and.imp_right $ and.imp_left or.inl) },
  { obtain ⟨U, hU, hU', hy, hx⟩ := exists_clopen_lower_of_not_le h,
    exact ⟨U, hU, or.inr hU', hx, hy⟩ }
end

@[priority 100] -- See note [lower instance priority]
instance priestley_space.to_t2_space : t2_space α :=
⟨λ x y h, let ⟨U, hU, _, hx, hy⟩ := exists_clopen_upper_or_lower_of_ne h in
   ⟨U, Uᶜ, hU.is_open, hU.compl.is_open, hx, hy, disjoint_compl_right⟩⟩

end partial_order
