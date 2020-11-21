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

namespace category_theory
open category limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

namespace preserves_terminal

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

variables [has_terminal C]
/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def is_limit_of_has_terminal_of_preserves_limit [preserves_limit (functor.empty C) G] :
  is_terminal (G.obj (⊤_ C)) :=
map_is_limit_of_preserves_of_is_limit G (⊤_ C) terminal_is_terminal

/--
If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
def has_terminal_of_has_terminal_of_preserves_limit [preserves_limit (functor.empty C) G] :
  has_terminal D :=
⟨λ F,
begin
  haveI := has_limit.mk ⟨_, is_limit_of_has_terminal_of_preserves_limit G⟩,
  apply has_limit_of_iso F.unique_from_empty.symm,
end⟩

/--
If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def preserves_terminal_of_iso_comparison [has_terminal D]
  [i : is_iso (terminal_comparison G)] : preserves_limit (functor.empty C) G :=
begin
  apply preserves_limit_of_preserves_limit_cone terminal_is_terminal,
  apply (terminal_map_cone_limit _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (functor.empty D)),
  apply i,
end

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_is_iso [has_terminal D]
  (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : is_iso f] : preserves_limit (functor.empty C) G :=
begin
  rw subsingleton.elim f (terminal_comparison G) at i,
  exactI preserves_terminal_of_iso_comparison G,
end

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_iso [has_terminal D]
  (f : G.obj (⊤_ C) ≅ ⊤_ D) : preserves_limit (functor.empty C) G :=
preserves_terminal_of_is_iso G f.hom

variables [has_terminal D] [preserves_limit (functor.empty C) G]

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` an isomorphism. -/
def iso : G.obj (⊤_ C) ≅ ⊤_ D :=
(is_limit_of_has_terminal_of_preserves_limit G).cone_point_unique_up_to_iso (limit.is_limit _)

@[simp]
lemma iso_hom : (preserves_terminal.iso G).hom = terminal_comparison G :=
rfl

instance : is_iso (terminal_comparison G) :=
begin
  rw ← iso_hom,
  apply_instance,
end

end preserves_terminal
end category_theory
