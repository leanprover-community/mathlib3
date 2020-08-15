/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.pseudoelements

/-!
# The four lemma

We prove the "mono" version of the four lemma in an arbitrary abelian category.

## Future work

The "epi" four lemma and the five lemma, which is then an easy corollary.

## Tags

four lemma, diagram lemma, diagram chase
-/
open category_theory
open category_theory.abelian.pseudoelements

universes v u

variables {V : Type u} [category.{v} V] [abelian V]

local attribute [instance] preadditive.has_equalizers_of_has_kernels
local attribute [instance] object_to_sort hom_to_fun

section four

/-

A ---f--> B ---g--> C ---h--> D
|         |         |         |
α         β         γ         δ
|         |         |         |
v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D'

-/

variables {A B C D A' B' C' D' : V}
variables {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
variables {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'}
variables [exact f g] [exact g h] [exact f' g']
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include comm₁ comm₂ comm₃

/-- The four lemma, mono version -/
lemma mono_of_epi_of_mono_of_mono (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
mono_of_zero_of_map_zero _ $ λ c hc,
  have h c = 0, from
    suffices δ (h c) = 0, from zero_of_map_zero _ (pseudo_injective_of_mono _) _ this,
    calc δ (h c) = h' (γ c) : by rw [←comp_apply, ←comm₃, comp_apply]
             ... = h' 0     : by rw hc
             ... = 0        : apply_zero _,
  exists.elim (pseudo_exact_of_exact.2 _ this) $ λ b hb,
    have g' (β b) = 0, from
      calc g' (β b) = γ (g b) : by rw [←comp_apply, comm₂, comp_apply]
                ... = γ c     : by rw hb
                ... = 0       : hc,
    exists.elim (pseudo_exact_of_exact.2 _ this) $ λ a' ha',
      exists.elim (pseudo_surjective_of_epi α a') $ λ a ha,
      have f a = b, from
        suffices β (f a) = β b, from pseudo_injective_of_mono _ this,
        calc β (f a) = f' (α a) : by rw [←comp_apply, ←comm₁, comp_apply]
                 ... = f' a'    : by rw ha
                 ... = β b      : ha',
      calc c = g b     : hb.symm
         ... = g (f a) : by rw this
         ... = 0       : pseudo_exact_of_exact.1 _

end four
