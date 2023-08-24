/-
Copyright (c) 2022 Sam van Gool and Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool, Jake Levinson
-/

import topology.sheaves.presheaf
import topology.sheaves.stalks
import category_theory.sites.surjective

/-!

# Locally surjective maps of presheaves.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `X` be a topological space, `ℱ` and `𝒢` presheaves on `X`, `T : ℱ ⟶ 𝒢` a map.

In this file we formulate two notions for what it means for
`T` to be locally surjective:

  1. For each open set `U`, each section `t : 𝒢(U)` is in the image of `T`
     after passing to some open cover of `U`.

  2. For each `x : X`, the map of *stalks* `Tₓ : ℱₓ ⟶ 𝒢ₓ` is surjective.

We prove that these are equivalent.

-/

universes v u

noncomputable theory

open category_theory
open topological_space
open opposite

namespace Top.presheaf

section locally_surjective

local attribute [instance] concrete_category.has_coe_to_fun
local attribute [instance] concrete_category.has_coe_to_sort

open_locale algebraic_geometry

/-- Let `C` be a concrete category, `X` a topological space. -/
variables {C : Type u} [category.{v} C] [concrete_category.{v} C] {X : Top.{v}}

/-- Let `ℱ, 𝒢 : (opens X)ᵒᵖ ⥤ C` be `C`-valued presheaves on `X`. -/
variables {ℱ 𝒢 : X.presheaf C}

/--
A map of presheaves `T : ℱ ⟶ 𝒢` is **locally surjective** if for any open set `U`,
section `t` over `U`, and `x ∈ U`, there exists an open set `x ∈ V ⊆ U` and a section `s` over `V`
such that `$T_*(s_V) = t|_V$`.

See `is_locally_surjective_iff` below.
-/
def is_locally_surjective (T : ℱ ⟶ 𝒢) :=
  category_theory.is_locally_surjective (opens.grothendieck_topology X) T

lemma is_locally_surjective_iff (T : ℱ ⟶ 𝒢) :
  is_locally_surjective T ↔
    ∀ U t (x ∈ U), ∃ V (ι : V ⟶ U), (∃ s, T.app _ s = t |_ₕ ι) ∧ x ∈ V :=
iff.rfl

section surjective_on_stalks

variables [limits.has_colimits C] [limits.preserves_filtered_colimits (forget C)]

/-- An equivalent condition for a map of presheaves to be locally surjective
is for all the induced maps on stalks to be surjective. -/
lemma locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) :
  is_locally_surjective T ↔
  ∀ (x : X), function.surjective ((stalk_functor C x).map T) :=
begin
  split; intro hT,
  { /- human proof:
    Let g ∈ Γₛₜ 𝒢 x be a germ. Represent it on an open set U ⊆ X
    as ⟨t, U⟩. By local surjectivity, pass to a smaller open set V
    on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
    Then the germ of s maps to g -/

    -- Let g ∈ Γₛₜ 𝒢 x be a germ.
    intros x g,
    -- Represent it on an open set U ⊆ X as ⟨t, U⟩.
    obtain ⟨U, hxU, t, rfl⟩ :=  𝒢.germ_exist x g,
    -- By local surjectivity, pass to a smaller open set V
    -- on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
    rcases hT U t x hxU with ⟨V, ι, ⟨s, h_eq⟩, hxV⟩,

    -- Then the germ of s maps to g.
    use ℱ.germ ⟨x, hxV⟩ s,
    convert stalk_functor_map_germ_apply V ⟨x, hxV⟩ T s,

    simpa [h_eq] using germ_res_apply 𝒢 ι ⟨x,hxV⟩ t, },

  { /- human proof:
    Let U be an open set, t ∈ Γ ℱ U a section, x ∈ U a point.
    By surjectivity on stalks, the germ of t is the image of
    some germ f ∈ Γₛₜ ℱ x. Represent f on some open set V ⊆ X as ⟨s, V⟩.
    Then there is some possibly smaller open set x ∈ W ⊆ V ∩ U on which
    we have T(s) |_ W = t |_ W. -/
    intros U t x hxU,
    set t_x := 𝒢.germ ⟨x, hxU⟩ t with ht_x,
    obtain ⟨s_x, hs_x : ((stalk_functor C x).map T) s_x = t_x⟩ := hT x t_x,
    obtain ⟨V, hxV, s, rfl⟩ := ℱ.germ_exist x s_x,
    -- rfl : ℱ.germ x s = s_x
    have key_W := 𝒢.germ_eq x hxV hxU (T.app _ s) t
      (by { convert hs_x,
            symmetry,
            convert stalk_functor_map_germ_apply _ _ _ s, }),
    obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W,

    refine ⟨W, hWU, ⟨ℱ.map hWV.op s, _⟩, hxW⟩,
    convert h_eq,
    simp only [← comp_apply, T.naturality], },
end

end surjective_on_stalks

end locally_surjective

end Top.presheaf
