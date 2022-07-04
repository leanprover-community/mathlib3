/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.subrep_lattice

variables {k G V V₂ : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
  [add_comm_monoid V₂] [module k V₂]

/-- A representation is irreducible if its only subreps are the singleton (zero representation)
or the whole representation -/
def is_irreducible (ρ : representation k G V) : Prop := ∀ (p : subrep ρ), p = ⊥ ∨ p = ⊤

namespace representation

lemma schur_injective {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h : is_irreducible ρ) : f = 0 ∨ function.injective f := sorry
-- Need: kernel of f in V is a subrepresentation of V. Then ker f = bot or top.
-- If ker f = top, then f = 0. If ker f = bot, then f is injective

lemma schur_surjective {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h : is_irreducible ρ₂) : f = 0 ∨ function.surjective f := sorry

theorem schur {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h₁ : is_irreducible ρ) (h₂ : is_irreducible ρ₂) : function.bijective f :=
⟨representation.schur_injective f h₁, representation.schur_surjective f h₂⟩

theorem schur_equiv

end representation
