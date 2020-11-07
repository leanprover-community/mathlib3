/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.preserves.limits
import category_theory.limits.shapes

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminal_comparison G` is an isomorphism iff `G` preserves terminal
objects.
-/

universes v u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

namespace preserves

variables (X : C)

/--
The map of an empty cone is a limit iff the empty cone consisting of the mapped object is a limit.
-/
def terminal_map_cone_limit :
  is_limit (G.map_cone (as_empty_cone X)) ≃ is_terminal (G.obj X) :=
(is_limit.postcompose_hom_equiv (functor.empty_ext _ _) _).symm.trans
  (is_limit.equiv_iso_limit (cones.ext (iso.refl _) (by tidy)))

/-- The property of preserving terminal objects expressed in terms of `is_terminal`. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (functor.empty C) G]
  (l : is_terminal X) : is_terminal (G.obj X) :=
terminal_map_cone_limit G X (preserves_limit.preserves l)

/-- The property of reflecting terminal objects expressed in terms of `is_terminal`. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (functor.empty C) G]
  (l : is_terminal (G.obj X)) : is_terminal X :=
reflects_limit.reflects ((terminal_map_cone_limit G X).symm l)

/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def is_limit_of_has_terminal_of_preserves_limit [has_terminal C]
  [preserves_limit (functor.empty C) G] :
  is_terminal (G.obj (⊤_ C)) :=
map_is_limit_of_preserves_of_is_limit G (⊤_ C) terminal_is_terminal

/--
The comparison morphism from the image of a terminal object to the terminal in the target category.
This is an isomorphism if and only if `G` preserves terminal objects, shown in `preserves_terminal`
and `preserves_terminal_iso`.
-/
def terminal_comparison [has_terminal C] [has_terminal D] :
  G.obj (⊤_ C) ⟶ ⊤_ D :=
terminal.from _

/--
If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def preserves_terminal_of_iso_comparison [has_terminal C] [has_terminal D]
  [i : is_iso (terminal_comparison G)] : preserves_limit (functor.empty C) G :=
begin
  apply preserves_limit_of_preserves_limit_cone terminal_is_terminal,
  apply (terminal_map_cone_limit _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (functor.empty D)),
  apply i,
end

variables [preserves_limit (functor.empty C) G]

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` an isomorphism. -/
def preserves_terminal_iso [has_terminal C] [has_terminal D] :
  G.obj (⊤_ C) ≅ ⊤_ D :=
(is_limit_of_has_terminal_of_preserves_limit G).cone_point_unique_up_to_iso (limit.is_limit _)

@[simp]
lemma preserves_terminal_iso_hom [has_terminal C] [has_terminal D] :
  (preserves_terminal_iso G).hom = terminal_comparison G :=
rfl

end preserves
