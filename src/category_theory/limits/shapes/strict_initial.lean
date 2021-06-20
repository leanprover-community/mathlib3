/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.terminal
import category_theory.epi_mono
import tactic.tfae

universes v u

namespace category_theory
namespace limits
open category

variables (C : Type u) [category.{v} C]

/--
We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.

Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist.
-/
class has_strict_initial_object : Prop :=
(out : ∀ {I A : C} (f : A ⟶ I), is_initial I → is_iso f)

variables {C} [has_strict_initial_object C]
variables {I : C}

lemma is_initial.is_iso_to (hI : is_initial I) {A : C} (f : A ⟶ I) :
  is_iso f :=
has_strict_initial_object.out f hI

lemma is_initial.subsingleton_to (hI : is_initial I) {A : C} (f g : A ⟶ I) :
  f = g :=
begin
  haveI := hI.is_iso_to f,
  haveI := hI.is_iso_to g,
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g)),
end

lemma is_initial.mono_from (hI : is_initial I) {A : C} (f : I ⟶ A) :
  mono f :=
{ right_cancellation := λ B g h i, hI.subsingleton_to _ _ }

lemma is_initial.to_mono (hI : is_initial I) {A : C} :
  mono (hI.to A) :=
hI.mono_from _

end limits
end category_theory
