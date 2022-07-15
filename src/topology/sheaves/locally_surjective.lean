/-
Copyright (c) 2022 Sam van Gool and Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool, Jake Levinson
-/

import topology.sheaves.presheaf
import topology.sheaves.stalks

/-!

Locally surjective maps of presheaves.

Let X be a topological space, ℱ and 𝒢 presheaves on X, T : ℱ ⟶ 𝒢 a map.

In this file we formulate two notions for what it means for
T to be locally surjective:

  1. For each open set U, each section t ∈ 𝒢(U) is in the image of T
     after passing to some open cover of U.

  2. For each x : X, the map of *stalks* Tₓ : ℱₓ ⟶ 𝒢ₓ is surjective.

We prove that these are equivalent.

-/

universes v u

noncomputable theory

open category_theory
open topological_space
open opposite

section locally_surjective

/-- Let C be a concrete category, X a topological space. -/
variables {C : Type u} [category.{v} C] [concrete_category.{v} C] {X : Top.{v}}

/-- Let ℱ, 𝒢 : (opens X)ᵒᵖ ⥤ C be C-valued presheaves on X. -/
variables {ℱ : X.presheaf C} {𝒢 : X.presheaf C}

/-- When U is an open set, we introduce the notation "Γ_ ℱ U"
for the set of sections of ℱ over U.
-/
@[nolint has_inhabited_instance] -- This may be empty.
def sections_of_presheaf_on_open (ℱ : X.presheaf C) (U : opens X) : Type v :=
  (forget C).obj (ℱ.obj (op U))
local notation `Γ_` : 80 := sections_of_presheaf_on_open

/-- When i : V ⟶ U is an inclusion of an open set V into an open set U,
and s ∈ Γ_ ℱ U, we write "s|_i" for the restriction of s to V. -/
def restrict_along {ℱ : X.presheaf C} {U : opens X} {V : opens X}
  (s : Γ_ ℱ U) (i : V ⟶ U) : Γ_ ℱ V := (forget C).map (ℱ.map i.op) s
local infix `|_` : 80 := restrict_along

/-- When T : ℱ ⟶ 𝒢 is a natural transformation, and s ∈ Γ_ ℱ U, we
write "T _* s" for the image of s under the map T_U : Γ_ ℱ U ⟶ Γ_ 𝒢 U. -/
def map_on_sections {U : opens X} (T : ℱ ⟶ 𝒢) (s : Γ_ ℱ U) :
  Γ_ 𝒢 U := (forget C).map (T.app (op U)) s
local infix ` _* ` : 80 := map_on_sections

/-- A map of presheaves T : ℱ ⟶ 𝒢 is **locally surjective** if for
any open set U, section t over U, and x ∈ U, there exists an open set
x ∈ V ⊆ U such that $T_*(s_V) = t|_V$. -/
def is_locally_surjective (T : ℱ ⟶ 𝒢) :=
  ∀ (U : opens X) (t : Γ_ 𝒢 U) (x : X) (hx : x ∈ U),
  ∃ (V : opens X) (ι : V ⟶ U) (hxV : x ∈ V) (s : Γ_ ℱ V),
  T _* s = t |_ ι

section surjective_on_stalks

variables [category_theory.limits.has_colimits C]

/-- When (x : X) is a point, we introduce the notation "Γₛₜ ℱ x" for
the (underlying object of) the stalk of ℱ at x. -/
@[nolint has_inhabited_instance] -- This may be empty.
def stalk_set (ℱ : X.presheaf C) (x : X) :=
  (forget C).obj (ℱ.stalk x)
local notation `Γₛₜ` : 80 := stalk_set

/-- When (T : ℱ ⟶ 𝒢) is a map of presheaves, we introduce the notation "T _ₛₜ x"
for the induced map of (underlying objects of) stalks. -/
def map_on_stalks (T : ℱ ⟶ 𝒢) (x : X) :
  Γₛₜ ℱ x ⟶ Γₛₜ 𝒢 x := (forget C).map ((Top.presheaf.stalk_functor C x).map T)
local infix `_ₛₜ` : 80 := map_on_stalks

/-- An equivalent condition for a map of presheaves to be locally surjective
is for all the induced maps on stalks to be surjective. -/
def is_surjective_on_stalks (T : ℱ ⟶ 𝒢) :=
  ∀ (x : X), function.surjective (T _ₛₜ x)

variables [category_theory.limits.preserves_filtered_colimits (forget C)]

/-- Being locally surjective is equivalent to being surjective on stalks. -/
lemma locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) :
  is_locally_surjective T ↔ is_surjective_on_stalks T :=
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
    rcases 𝒢.germ_exist x g with ⟨U, hxU, t, rfl⟩,
    -- By local surjectivity, pass to a smaller open set V
    -- on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
    rcases hT U t x hxU with ⟨V, ι, hxV, s, h_eq⟩,


    -- Then the germ of s maps to g.
    use (forget C).map (ℱ.germ ⟨x, hxV⟩) s,
    convert Top.presheaf.stalk_functor_map_germ_apply V ⟨x, hxV⟩ T s,

    -- I said, "then the germ of maps to g."
    change ((forget C).map _ s) = (forget C).map _ t at h_eq,

    -- The germ of s maps to g? Please?
    change _ = (forget C).map _ ((forget C).map _ _),
    rw h_eq,

    -- :(
    change _ = ((forget C).map _ ≫ (forget C).map _) _,
    rw [← (forget C).map_comp, 𝒢.germ_res],
    refl, },

  { /- human proof:
    Let U be an open set, t ∈ Γ ℱ U a section, x ∈ U a point.
    By surjectivity on stalks, the germ of t is the image of
    some germ f ∈ Γₛₜ ℱ x. Represent f on some open set V ⊆ X as ⟨s, V⟩.
    Then there is some possibly smaller open set x ∈ W ⊆ V ∩ U on which
    we have T(s) |_ W = t |_ W. -/
    intros U t x hxU,
    set t_x := (forget C).map (𝒢.germ ⟨x, hxU⟩) t with ht_x,
    obtain ⟨s_x, hs_x : (T _ₛₜ x) s_x = t_x⟩ := hT x t_x,
    obtain ⟨V, hxV, s, rfl⟩ := ℱ.germ_exist x s_x,
    -- rfl : ℱ.germ x s = s_x
    have key_W := 𝒢.germ_eq x hxV hxU (T _* s) t
      (by { convert hs_x,
            symmetry,
            convert Top.presheaf.stalk_functor_map_germ_apply _ _ _ s, }),
    obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W,
    refine ⟨W, hWU, hxW, ⟨s |_ hWV, _⟩⟩,
    convert h_eq,

    -- horrible wails from beyond the stars
    change (((forget C).map _) ≫ ((forget C).map _)) s =
    (((forget C).map _) ≫ ((forget C).map _)) s,

    rw ← (forget C).map_comp,
    rw ← (forget C).map_comp,
    rw T.naturality, },
end

end surjective_on_stalks

end locally_surjective
