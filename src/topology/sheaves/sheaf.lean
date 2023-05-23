/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import category_theory.sites.sheaf
import category_theory.sites.spaces

/-!
# Sheaves

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define sheaves on a topological space, with values in an arbitrary category.

A presheaf on a topological space `X` is a sheaf presicely when it is a sheaf under the
grothendieck topology on `opens X`, which expands out to say: For each open cover `{ Uᵢ }` of
`U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an `A : X`, there exists an unique
gluing `A ⟶ F(U)` compatible with the restriction.

See the docstring of `Top.presheaf.is_sheaf` for an explanation on the design descisions and a list
of equivalent conditions.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

-/

universes w v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C]
variables {X : Top.{w}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

/--
The sheaf condition has several different equivalent formulations.
The official definition chosen here is in terms of grothendieck topologies so that the results on
sites could be applied here easily, and this condition does not require additional constraints on
the value category.
The equivalent formulations of the sheaf condition on `presheaf C X` are as follows :

1. `Top.presheaf.is_sheaf`: (the official definition)
  It is a sheaf with respect to the grothendieck topology on `opens X`, which is to say:
  For each open cover `{ Uᵢ }` of `U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an
  `A : X`, there exists an unique gluing `A ⟶ F(U)` compatible with the restriction.

2. `Top.presheaf.is_sheaf_equalizer_products`: (requires `C` to have all products)
  For each open cover `{ Uᵢ }` of `U`, `F(U) ⟶ ∏ F(Uᵢ)` is the equalizer of the two morphisms
  `∏ F(Uᵢ) ⟶ ∏ F(Uᵢ ∩ Uⱼ)`.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_equalizer_products`.

3. `Top.presheaf.is_sheaf_opens_le_cover`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  `F(V₁) ⟶ F(V₂)` for every pair of open sets `V₁ ⊇ V₂` that are contained in some `Uᵢ`.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_opens_le_cover`.

4. `Top.presheaf.is_sheaf_pairwise_intersections`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  from `F(Uᵢ)` and `F(Uⱼ)` to `F(Uᵢ ∩ Uⱼ)` for each pair `(i, j)`.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections`.

The following requires `C` to be concrete and complete, and `forget C` to reflect isomorphisms and
preserve limits. This applies to most "algebraic" categories, e.g. groups, abelian groups and rings.

5. `Top.presheaf.is_sheaf_unique_gluing`:
  (requires `C` to be concrete and complete; `forget C` to reflect isomorphisms and preserve limits)
  For each open cover `{ Uᵢ }` of `U`, and a compatible family of elements `x : F(Uᵢ)`, there exists
  a unique gluing `x : F(U)` that restricts to the given elements.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_unique_gluing`.

6. The underlying sheaf of types is a sheaf.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_comp` and
  `category_theory.presheaf.is_sheaf_iff_is_sheaf_forget`.
-/
def is_sheaf (F : presheaf.{w v u} C X) : Prop :=
presheaf.is_sheaf (opens.grothendieck_topology X) F

/--
The presheaf valued in `unit` over any topological space is a sheaf.
-/
lemma is_sheaf_unit (F : presheaf (category_theory.discrete unit) X) : F.is_sheaf :=
λ x U S hS x hx, ⟨eq_to_hom (subsingleton.elim _ _), by tidy, by tidy⟩

lemma is_sheaf_iso_iff {F G : presheaf C X} (α : F ≅ G) : F.is_sheaf ↔ G.is_sheaf :=
presheaf.is_sheaf_of_iso_iff α

/--
Transfer the sheaf condition across an isomorphism of presheaves.
-/
lemma is_sheaf_of_iso {F G : presheaf C X} (α : F ≅ G) (h : F.is_sheaf) : G.is_sheaf :=
(is_sheaf_iso_iff α).1 h

end presheaf

variables (C X)

/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
@[derive category]
def sheaf : Type (max u v w) := Sheaf (opens.grothendieck_topology X) C

variables {C X}

/-- The underlying presheaf of a sheaf -/
abbreviation sheaf.presheaf (F : X.sheaf C) : Top.presheaf C X := F.1

variables (C X)

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_inhabited : inhabited (sheaf (category_theory.discrete punit) X) :=
⟨⟨functor.star _, presheaf.is_sheaf_unit _⟩⟩

namespace sheaf

/--
The forgetful functor from sheaves to presheaves.
-/
@[derive [full, faithful]]
def forget : Top.sheaf C X ⥤ Top.presheaf C X :=
Sheaf_to_presheaf _ _

-- Note: These can be proved by simp.
lemma id_app (F : sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _ := rfl
lemma comp_app {F G H : sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) :
  (f ≫ g).1.app t = f.1.app t ≫ g.1.app t := rfl

end sheaf

end Top
