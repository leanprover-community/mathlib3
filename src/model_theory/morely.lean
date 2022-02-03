/-
Copyright (c) 2022 Aris Papadopoulos, Ramon Fernández Mir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aris Papadopoulos, Ramon Fernández Mir
-/
import model_theory.basic
import data.set.finite

/-!
# Morley's Theorem

## Main Definitions
*

## References
-

  -/

universes u

instance {α : Type u} {X : set α} : has_mem X (𝒫 X) :=
  ⟨λ x A, x.1 ∈ A.1⟩

instance {α : Type u} {X : set α} : has_subset (𝒫 X) :=
  ⟨λ A B, A.1 ⊆ B.1⟩

instance {α : Type u} {X : set α} : has_union (𝒫 X) :=
  ⟨λ A B, ⟨A.1 ∪ B.1, set.union_subset A.2 B.2⟩⟩

instance {α : Type u} {X : set α} : has_singleton X (𝒫 X) :=
  ⟨λ a, ⟨{a}, set.singleton_subset_iff.2 a.2⟩⟩

instance {α : Type u} {X : set α} : has_sdiff (𝒫 X) :=
  ⟨λ A B, ⟨A.val \ B.val, subset_trans (set.diff_subset A.1 B.1) A.2⟩⟩

class pregeometry (α : Type u) :=
(X : set α)
(cl : 𝒫 X → 𝒫 X)
(monotone_dominating : ∀ {A B}, A ⊆ B → A ⊆ cl A ∧ cl A ⊆ cl B)
(idempotent : ∀ A, cl (cl A) = cl A)
(finite_character : ∀ {A}, ∀ a ∈ cl A, ∃ F ⊆ A, set.finite F.1 ∧ a ∈ cl F)
(exchange_principle : ∀ a b C, b ∈ cl (C ∪ {a}) \ cl C → a ∈ cl (C ∪ {b}))
