/-
Copyright (c) 2022 Aris Papadopoulos, Ramon Fernández Mir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aris Papadopoulos, Ramon Fernández Mir
-/
import model_theory.basic
import data.set.finite
import data.

/-!
# Morley's Theorem

## Main Definitions
*

## References
-

  -/

universes u

section pregeometry

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

instance {α : Type u} {X : set α} : is_refl (𝒫 X) has_subset.subset :=
  ⟨λ a x hx, hx⟩

class pregeometry {α : Type u} (X : set α) (cl : 𝒫 X → 𝒫 X) :=
  (monotone_dominating : ∀ {A B}, A ⊆ B → A ⊆ cl A ∧ cl A ⊆ cl B)
  (idempotent : ∀ A, cl (cl A) = cl A)
  (finite_character : ∀ {A}, ∀ a ∈ cl A, ∃ F ⊆ A, set.finite F.1 ∧ a ∈ cl F)
  (exchange_principle : ∀ {a b C}, b ∈ cl (C ∪ {a}) \ cl C → a ∈ cl (C ∪ {b}))

lemma exchange_principle_extended {α : Type} (X : set α) (cl : 𝒫 X → 𝒫 X) [pregeometry X cl] :
  ∀ a b C, b ∈ cl (C ∪ {a}) \ cl C → a ∈ cl (C ∪ {b}) \ cl C :=
  begin
    intros a b C hb,
    have ha := pregeometry.exchange_principle hb,
    suffices hanclC : a ∉ cl C,
    { exact ⟨ha, hanclC⟩, },
    intros haC,
    apply hb.2,
    suffices hclCaclC : cl (C ∪ {a}) ⊆ cl C,
    { exact (set.mem_of_subset_of_mem hclCaclC hb.1), },
    suffices hCaclC : (C ∪ {a}) ⊆ cl C,
    { have hclclC : cl C = cl (cl C) := (pregeometry.idempotent C).symm,
      rw [hclclC],
      exact (pregeometry.monotone_dominating hCaclC).2, },
    have hCcl : C ⊆ cl C := (pregeometry.monotone_dominating (subset_refl C)).1,
    have haC := (@set.singleton_subset_iff _ a.1 (cl C).1).2 haC,
    exact set.union_subset hCcl haC,
  end

end pregeometry

section strongly_minimal

open first_order

class minimal {α : Type u} {L : language} {M : set α} (S : L.Structure M) :=
  (infinite : M.infinite)
  (definable_sets : ∀ {β} [fintype β] (φ : L.definable_set M β),
    set.finite φ.1 ∨ set.finite φ.1ᶜ)

end strongly_minimal
