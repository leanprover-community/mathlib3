/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.subrep_hom

variables {k G V V₂ : Type*} [comm_ring k] [monoid G] [add_comm_group V] [module k V]
  [add_comm_group V₂] [module k V₂]

/-- A representation is irreducible if its only subreps are the singleton (zero representation)
or the whole representation -/
def is_irreducible (ρ : representation k G V) : Prop := ∀ (p : subrep ρ), p = ⊥ ∨ p = ⊤

namespace representation

/-- A rep_hom from an irreducible representation to another representation is either 0 or
injective. -/
lemma schur_injective {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h : is_irreducible ρ) : f = 0 ∨ function.injective f :=
begin
  have := h f.ker,
  cases this with hk hk,
  { apply or.intro_right,
    exact rep_hom.ker_eq_bot.mp hk },
  { apply or.intro_left,
    exact rep_hom.ker_eq_top.mp hk }
end

/-- A rep_hom from a representation to an irreducible representation is either 0 or
surjective. -/
lemma schur_surjective {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h : is_irreducible ρ₂) : f = 0 ∨ function.surjective f :=
begin
  have := h f.range,
  cases this with hr hr,
  { apply or.intro_left,
    exact rep_hom.range_eq_bot.mp hr },
  { apply or.intro_right,
    exact rep_hom.range_eq_top.mp hr }
end

/-- Schur's lemma: A rep_hom between irreducible representations is either 0 or bijective. -/
theorem schur {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h₁ : is_irreducible ρ) (h₂ : is_irreducible ρ₂) : f = 0 ∨ function.bijective f :=
begin
  have := and.intro (schur_injective f h₁) (schur_surjective f h₂),
  rw [←or_and_distrib_left, ←function.bijective] at this,
  exact this
end

/-- Produce a rep_equiv using Schur's lemma -/
noncomputable def schur_equiv {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h₁ : is_irreducible ρ) (h₂ : is_irreducible ρ₂) (h₃ : f ≠ 0) : ρ ≃ᵣ ρ₂ :=
begin
  apply rep_equiv.of_bijective f,
  { have h_inj := schur_injective f h₁,
    cases h_inj,
    exact absurd h_inj h₃,
    exact h_inj },
  { have h_sur := schur_surjective f h₂,
    cases h_sur,
    exact absurd h_sur h₃,
    exact h_sur }
end

end representation
