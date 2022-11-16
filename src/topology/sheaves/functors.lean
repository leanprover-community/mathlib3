/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/

import topology.sheaves.sheaf_condition.pairwise_intersections
import topology.sheaves.sheaf_condition.sites

/-!
# Functors between categories of sheaves

## Main definitions
- `Top.sheaf.pushforward`: The pushforward functor between sheaf categories over topological spaces.
- `Top.sheaf.pullback`: The pullback functor between sheaf categories over topological spaces.
- `Top.sheaf.pullback_pushforward_adjunction`:
  The adjunction between pullback and pushforward for sheaves on topological spaces.

-/

noncomputable theory

universes w v u

open category_theory
open category_theory.limits
open topological_space

variables {C : Type u} [category.{v} C]
variables {X Y : Top.{w}} (f : X ⟶ Y)
variables ⦃ι : Type w⦄ {U : ι → opens Y}

namespace Top
namespace sheaf

open presheaf

/--
The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
theorem pushforward_sheaf_of_sheaf
  {F : X.presheaf C} (h : F.is_sheaf) : (f _* F).is_sheaf :=
pullback_is_sheaf_of_cover_preserving (compatible_preserving_opens_map f)
  (cover_preserving_opens_map f) ⟨F, h⟩

variables (C)

/--
The pushforward functor.
-/
def pushforward (f : X ⟶ Y) : X.sheaf C ⥤ Y.sheaf C :=
sites.pullback _ (compatible_preserving_opens_map f)
  (cover_preserving_opens_map f)

lemma pushforward_forget (f : X ⟶ Y) :
  pushforward C f ⋙ forget C Y = forget C X ⋙ presheaf.pushforward C f := rfl

/--
Pushforward of sheaves is isomorphic (actually definitionally equal) to pushforward of presheaves.
-/
def pushforward_forget_iso (f : X ⟶ Y) :
  pushforward C f ⋙ forget C Y ≅ forget C X ⋙ presheaf.pushforward C f := iso.refl _

variables {C}

@[simp] lemma pushforward_obj_val (f : X ⟶ Y) (F : X.sheaf C) :
  ((pushforward C f).obj F).1 = f _* F.1 := rfl

@[simp] lemma pushforward_map (f : X ⟶ Y) {F F' : X.sheaf C} (α : F ⟶ F') :
  ((pushforward C f).map α).1 = (presheaf.pushforward _ f).map α.1 := rfl

variables (A : Type*) [category.{w} A] [concrete_category.{w} A] [has_colimits A] [has_limits A]
variables [preserves_limits (category_theory.forget A)]
variables [preserves_filtered_colimits (category_theory.forget A)]
variables [reflects_isomorphisms (category_theory.forget A)]

/--
The pushforward functor.
-/
def pullback (f : X ⟶ Y) : Y.sheaf A ⥤ X.sheaf A :=
sites.pushforward A _ _ (opens.map f)

lemma pullback_eq (f : X ⟶ Y) :
  pullback A f = forget A Y ⋙ presheaf.pullback A f ⋙ presheaf_to_Sheaf _ _ := rfl

/--
The pullback of a sheaf is isomorphic (actually definitionally equal) to the sheafification
of the pullback as a presheaf.
-/
def pullback_iso (f : X ⟶ Y) :
  pullback A f ≅ forget A Y ⋙ presheaf.pullback A f ⋙ presheaf_to_Sheaf _ _ := iso.refl _

/-- The adjunction between pullback and pushforward for sheaves on topological spaces. -/
def pullback_pushforward_adjunction (f : X ⟶ Y) :
  pullback A f ⊣ pushforward A f :=
sites.pullback_pushforward_adjunction _ _ _ _ _

instance : is_left_adjoint (pullback A f) := ⟨_, pullback_pushforward_adjunction A f⟩
instance : is_right_adjoint (pushforward A f) := ⟨_, pullback_pushforward_adjunction A f⟩

end sheaf

end Top
