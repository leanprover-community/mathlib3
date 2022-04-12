/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import topology.sheaves.sheaf_condition.pairwise_intersections

/-!
# functors between categories of sheaves

Show that the pushforward of a sheaf is a sheaf, and define
the pushforward functor from the category of C-valued sheaves
on X to that of sheaves on Y, given a continuous map between
topological spaces X and Y.

TODO: pullback for presheaves and sheaves
-/

noncomputable theory

universes v u u₁

open category_theory
open category_theory.limits
open topological_space

variables {C : Type u₁} [category.{v} C]
variables {X Y : Top.{v}} (f : X ⟶ Y)
variables ⦃ι : Type v⦄ {U : ι → opens Y}

namespace Top
namespace presheaf.sheaf_condition_pairwise_intersections

lemma map_diagram :
  pairwise.diagram U ⋙ opens.map f = pairwise.diagram ((opens.map f).obj ∘ U) :=
begin
  apply functor.hext,
  abstract obj_eq {intro i, cases i; refl},
  intros i j g, apply subsingleton.helim,
  iterate 2 {rw map_diagram.obj_eq},
end

lemma map_cocone : (opens.map f).map_cocone (pairwise.cocone U)
                     == pairwise.cocone ((opens.map f).obj ∘ U) :=
begin
  unfold functor.map_cocone cocones.functoriality, dsimp, congr,
  iterate 2 {rw map_diagram, rw opens.map_supr},
  apply subsingleton.helim, rw [map_diagram, opens.map_supr],
  apply proof_irrel_heq,
end

theorem pushforward_sheaf_of_sheaf {F : presheaf C X}
  (h : F.is_sheaf_pairwise_intersections) :
  (f _* F).is_sheaf_pairwise_intersections :=
λ ι U, begin
  convert h ((opens.map f).obj ∘ U) using 2,
  rw ← map_diagram, refl,
  change F.map_cone ((opens.map f).map_cocone _).op == _,
  congr, iterate 2 {rw map_diagram}, apply map_cocone,
end

end presheaf.sheaf_condition_pairwise_intersections

namespace sheaf

open presheaf

variables [has_products C]

/--
The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
theorem pushforward_sheaf_of_sheaf
  {F : presheaf C X} (h : F.is_sheaf) : (f _* F).is_sheaf :=
by rw is_sheaf_iff_is_sheaf_pairwise_intersections at h ⊢;
   exact sheaf_condition_pairwise_intersections.pushforward_sheaf_of_sheaf f h

/--
The pushforward functor.
-/
def pushforward (f : X ⟶ Y) : X.sheaf C ⥤ Y.sheaf C :=
{ obj := λ ℱ, ⟨f _* ℱ.1, pushforward_sheaf_of_sheaf f ℱ.2⟩,
  map := λ _ _, pushforward_map f }

end sheaf

end Top
