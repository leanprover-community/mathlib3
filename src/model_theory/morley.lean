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

universes u v

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
    have haC : {a} ⊆ cl C := (@set.singleton_subset_iff _ a.1 (cl C).1).2 haC,
    exact set.union_subset hCcl haC,
  end

end pregeometry

section strongly_minimal

open first_order

-- Copied from the Flypitch project.
section flypitch

-- variables (L : language.{u v}) (α : Type) [fintype α]

-- inductive preformula : ℕ → Type (max u v)
-- | falsum {} : preformula 0
-- | equal (t₁ t₂ : L.term α) : preformula 0
-- | rel {l : ℕ} (R : L.relations l) : preformula l
-- | apprel {l : ℕ} (f : preformula (l + 1)) (t : L.term α) : preformula l
-- | imp (f₁ f₂ : preformula 0) : preformula 0
-- | all (f : preformula 0) : preformula 0
-- export preformula

-- @[reducible] def formula := preformula L α 0
-- variables {L : language} {α : Type} [fintype α]

-- notation `⊥` := language.bounded_formula.falsum -- input: \bot
-- infix ` ≃ `:88 := language.bounded_formula.bd_equal -- input \~- or \simeq
-- infixr ` ⟹ `:62 := language.bounded_formula.bd_imp -- input \==>
-- prefix `∀'`:110 := language.bounded_formula.bd_all
-- prefix `∼`:max := language.bd_not -- input \~, the ASCII character ~ has too low precedence
-- notation `⊤` := ∼⊥ -- input: \top
-- def bd_biimp (f₁ f₂ : L.formula α) : L.formula α := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
-- infix ` ⇔ `:61 := bd_biimp -- input \<=>
-- def ex (f : L.bounded_formula α 1) :  L.formula α := ∼ ∀' ∼f
-- prefix `∃'`:110 := ex -- input \ex

-- inductive prf {L : language} : set (L.formula α) → L.formula α → Type u
-- | axm     {Γ A} (h : A ∈ Γ) : prf Γ A
-- | impI    {Γ : set $ L.formula α} {A B} (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
-- | impE    {Γ} (A) {B} (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
-- | falsumE {Γ : set $ L.formula α} {A} (h : prf (insert ∼A Γ) ⊥) : prf Γ A
-- | allI    {Γ A} (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀' A)
-- | allE₂   {Γ} A t (h : prf Γ (∀' A)) : prf Γ (A[t // 0])
-- | ref     (Γ t) : prf Γ (t ≃ t)
-- | subst₂  {Γ} (s t f) (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f[s // 0])) : prf Γ (f[t // 0])

end flypitch

structure first_order.language.minimal {α : Type u} (L : language) (M : set α) [L.Structure M] :=
  (infinite : M.infinite)
  (definable_sets : ∀ {β} [fintype β] (φ : L.definable_set M β),
    set.finite φ.1 ∨ set.finite φ.1ᶜ)

class minimal_theory {α : Type u} {L : language} (T : L.theory) :=
  -- (consistent : ¬(provable T (⊥ : L.sentence)))
  -- (complete : ∀ (f : L.sentence), f ∈ T ∨ ~ f ∈ T)
  (minimal_models : ∀ φ ∈ T, ∀ (M : set α) [L.Structure M],
    language.realize_sentence M φ → L.minimal M)

end strongly_minimal
