/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import topology.category.CompHaus
import topology.connected
import topology.subset_properties
import category_theory.adjunction.reflective

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. existence of products, limits(?), finite coproducts
2. `Profinite_to_Top` creates limits?
3. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/

open category_theory

/-- The type of profinite topological spaces. -/
structure Profinite :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_t2 : t2_space to_Top]
[is_totally_disconnected : totally_disconnected_space to_Top]

namespace Profinite

instance : inhabited Profinite := ⟨{to_Top := { α := pempty }}⟩

instance : has_coe_to_sort Profinite := ⟨Type*, λ X, X.to_Top⟩
instance {X : Profinite} : compact_space X := X.is_compact
instance {X : Profinite} : t2_space X := X.is_t2
instance {X : Profinite} : totally_disconnected_space X := X.is_totally_disconnected

instance category : category Profinite := induced_category.category to_Top

@[simp]
lemma coe_to_Top {X : Profinite} : (X.to_Top : Type*) = X :=
rfl

end Profinite

/-- The fully faithful embedding of `Profinite` in `Top`. -/
@[simps, derive [full, faithful]]
def Profinite_to_Top : Profinite ⥤ Top := induced_functor _

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps] def Profinite_to_CompHaus : Profinite ⥤ CompHaus :=
{ obj := λ X, { to_Top := X.to_Top },
  map := λ _ _ f, f }

instance : full Profinite_to_CompHaus := { preimage := λ _ _ f, f }
instance : faithful Profinite_to_CompHaus := {}

@[simp] lemma Profinite_to_CompHaus_to_Top :
  Profinite_to_CompHaus ⋙ CompHaus_to_Top = Profinite_to_Top :=
rfl

namespace Profinite
local attribute [instance] connected_component_setoid

/--
π₀ functor from CompHaus to Profinite, quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
def CompHaus_to_Profinite : CompHaus ⥤ Profinite :=
{ obj := λ X,
    { to_Top := { α := (π₀ X.to_Top.α) },
      is_compact := quotient.compact_space,
      is_t2 := pi0.t2,
      is_totally_disconnected := pi0.totally_disconnected_space },
  map := λ X Y f,
    { to_fun := pi0_map f.2,
      continuous_to_fun := pi0_map_continuous f.2 }}

instance : is_right_adjoint Profinite_to_CompHaus :=
{ left := CompHaus_to_Profinite,
  adj :=
  { hom_equiv := λ X Y,
    { to_fun := λ f,
      { to_fun := f.1 ∘ quotient.mk,
        continuous_to_fun := continuous.comp f.2 (continuous_quotient_mk) },
      inv_fun := λ g,
        { to_fun := pi0_lift g.2,
          continuous_to_fun := pi0_lift_continuous g.2 },
      left_inv := λ f, continuous_map.ext $ λ x, quotient.induction_on x $ λ a, rfl,
      right_inv := λ f, continuous_map.ext $ λ x, rfl },
    unit :=
      { app := λ X, { to_fun := quotient.mk,
                      continuous_to_fun := continuous_quotient_mk }},
    counit :=
      { app := λ Y, { to_fun := pi0_lift (@continuous_map.coe_continuous _ _ _ _ (𝟙 Y.to_Top)),
                      continuous_to_fun := { is_open_preimage := λ s hs, hs }}}}}
/--
The category of profinite sets is reflective in the category of compact hausdroff spaces
-/
instance : reflective Profinite_to_CompHaus :=
{ .. Profinite_to_CompHaus.category_theory.is_right_adjoint,
  .. Profinite_to_CompHaus.category_theory.full,
  .. Profinite_to_CompHaus.category_theory.faithful}

end Profinite
