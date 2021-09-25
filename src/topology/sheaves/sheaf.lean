/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf_condition.equalizer_products
import category_theory.full_subcategory

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category with products.

The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i ⊓ U j)`.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

## Equivalent conditions

While the "official" definition is in terms of an equalizer diagram,
in `src/topology/sheaves/sheaf_condition/pairwise_intersections.lean`
and in `src/topology/sheaves/sheaf_condition/open_le_cover.lean`
we provide two equivalent conditions (and prove they are equivalent).

The first is that `F.obj U` is the limit point of the diagram consisting of all the `F.obj (U i)`
and `F.obj (U i ⊓ U j)`.
(That is, we explode the equalizer of two products out into its component pieces.)

The second is that `F.obj U` is the limit point of the diagram constisting of all the `F.obj V`,
for those `V : opens X` such that `V ≤ U i` for some `i`.
(This condition is particularly easy to state, and perhaps should become the "official" definition.)

-/

universes v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

open sheaf_condition_equalizer_products

/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def is_sheaf (F : presheaf C X) : Prop :=
∀ ⦃ι : Type v⦄ (U : ι → opens X), nonempty (is_limit (sheaf_condition_equalizer_products.fork F U))

/--
The presheaf valued in `punit` over any topological space is a sheaf.
-/
lemma is_sheaf_punit (F : presheaf (category_theory.discrete punit) X) : F.is_sheaf :=
λ ι U, ⟨punit_cone_is_limit⟩

/--
Transfer the sheaf condition across an isomorphism of presheaves.
-/
lemma is_sheaf_of_iso {F G : presheaf C X} (α : F ≅ G) (h : F.is_sheaf) : G.is_sheaf :=
λ ι U, ⟨is_limit.of_iso_limit
  ((is_limit.postcompose_inv_equiv _ _).symm (h U).some)
  (sheaf_condition_equalizer_products.fork.iso_of_iso U α.symm).symm⟩

lemma is_sheaf_iso_iff {F G : presheaf C X} (α : F ≅ G) : F.is_sheaf ↔ G.is_sheaf :=
⟨(λ h, is_sheaf_of_iso α h), (λ h, is_sheaf_of_iso α.symm h)⟩

end presheaf

variables (C X)

/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
@[derive category]
def sheaf : Type (max u v) := { F : presheaf C X // F.is_sheaf }

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_inhabited : inhabited (sheaf (category_theory.discrete punit) X) :=
⟨⟨functor.star _, presheaf.is_sheaf_punit _⟩⟩

namespace sheaf

/--
The forgetful functor from sheaves to presheaves.
-/
@[derive [full, faithful]]
def forget : Top.sheaf C X ⥤ Top.presheaf C X :=
full_subcategory_inclusion presheaf.is_sheaf

end sheaf

end Top
