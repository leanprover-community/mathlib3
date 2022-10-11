/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import topology.sheaves.sheaf
import topology.sheaves.limits
import topology.sheaves.skyscraper
import topology.sheaves.stalks
import category_theory.preadditive.injective

/-!
# Godement resolution

For a presheaf `𝓕 : (opens X)ᵒᵖ ⥤ C`, we can embedded `𝓕` into a sheaf `∏ₓ skyscraper(𝓕ₓ)` where
`x` ranges over `X` and `𝓕 ⟶ ∏ₓ skyscraper(𝓕ₓ)` is mono.

## Main definition
* `godement_presheaf`: for a presheaf `𝓕`, its Godement presheaf is `∏ₓ skyscraper(𝓕ₓ)`
* `to_godement_presheaf`: the canonical map `𝓕 ⟶ godement_presheaf 𝓕` sending `s : 𝓕(U)` to a
  bundle of stalks `x ↦ sₓ`.
-/

noncomputable theory

section presheaf

open Top
open topological_space
open category_theory
open category_theory.limits

universes u v

variables {X : Top.{u}} {C : Type u} [category.{u} C]
variables [has_limits C] [has_colimits C]
variables [Π (x : X) (U : opens X), decidable (x ∈ U)]
variables (𝓕 : presheaf C X) (𝓖 : sheaf C X)

/--
The `godement_presheaf` for a presheaf `𝓕` is defined as a product presheaf `∏ₓ skyscraper(𝓕ₓ)`
-/
def godement_presheaf : presheaf C X :=
∏ (λ x, skyscraper_presheaf x (𝓕.stalk x) : X → presheaf C X)

/--
Under the isomorphism `godement_presheaf(𝓕, U) ≅ ∏ₓ skyscraper(x, 𝓕ₓ)(U)`, there is a morphism
`𝓕 ⟶ ∏ₓ skyscraper(x, 𝓕ₓ) ≅ godement_presheaf(𝓕)`
-/
def to_godement_presheaf : 𝓕 ⟶ godement_presheaf 𝓕 :=
pi.lift $ λ p₀, (skyscraper_presheaf_stalk_adjunction p₀).unit.app 𝓕

lemma godement_presheaf_is_sheaf (h : 𝓕.is_sheaf) : (godement_presheaf 𝓕).is_sheaf :=
limit_is_sheaf _ $ λ ⟨x⟩, (skyscraper_sheaf x _).2

def godement_sheaf : sheaf C X :=
⟨godement_presheaf 𝓖.1, godement_presheaf_is_sheaf _ 𝓖.2⟩


end presheaf
