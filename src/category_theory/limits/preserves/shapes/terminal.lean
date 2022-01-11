/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.terminal
import category_theory.limits.preserves.basic

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminal_comparison G` is an isomorphism iff `G` preserves terminal
objects.
-/

universes v v₁ v₂ u u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables (G : C ⥤ D)

namespace category_theory.limits

variables (X : C)

section terminal

/--
The map of an empty cone is a limit iff the mapped object is terminal.
-/
def is_limit_map_cone_empty_cone_equiv :
  is_limit (G.map_cone (as_empty_cone.{v₁} X)) ≃ is_terminal (G.obj X) :=
is_limit_empty_cone_equiv D _ _ (eq_to_iso rfl)

/-- The property of preserving terminal objects expressed in terms of `is_terminal`. -/
def is_terminal.is_terminal_obj [preserves_limit (functor.empty.{v₁} C) G]
  (l : is_terminal X) : is_terminal (G.obj X) :=
is_limit_map_cone_empty_cone_equiv G X (preserves_limit.preserves l)

/-- The property of reflecting terminal objects expressed in terms of `is_terminal`. -/
def is_terminal.is_terminal_of_obj [reflects_limit (functor.empty.{v₁} C) G]
  (l : is_terminal (G.obj X)) : is_terminal X :=
reflects_limit.reflects ((is_limit_map_cone_empty_cone_equiv G X).symm l)

variables [has_terminal C]
/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def is_limit_of_has_terminal_of_preserves_limit [preserves_limit (functor.empty.{v₁} C) G] :
  is_terminal (G.obj (⊤_ C)) :=
terminal_is_terminal.is_terminal_obj G (⊤_ C)

/--
If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
lemma has_terminal_of_has_terminal_of_preserves_limit [preserves_limit (functor.empty.{v₁} C) G] :
  has_terminal D :=
⟨λ F,
begin
  haveI := has_limit.mk ⟨_, is_limit_of_has_terminal_of_preserves_limit G⟩,
  apply has_limit_of_iso F.unique_from_empty.symm,
end⟩

variable [has_terminal D]
/--
If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def preserves_terminal.of_iso_comparison
  [i : is_iso (terminal_comparison G)] : preserves_limit (functor.empty C) G :=
begin
  apply preserves_limit_of_preserves_limit_cone terminal_is_terminal,
  apply (is_limit_map_cone_empty_cone_equiv _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (functor.empty.{v₂} D)),
  apply i,
end

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_is_iso
  (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : is_iso f] : preserves_limit (functor.empty C) G :=
begin
  rw subsingleton.elim f (terminal_comparison G) at i,
  exactI preserves_terminal.of_iso_comparison G,
end

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_iso
  (f : G.obj (⊤_ C) ≅ ⊤_ D) : preserves_limit (functor.empty C) G :=
preserves_terminal_of_is_iso G f.hom

variables [preserves_limit (functor.empty.{v₁} C) G]

/--
If `G` preserves terminal objects, then the terminal comparison map for `G` is an isomorphism.
-/
def preserves_terminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
(is_limit_of_has_terminal_of_preserves_limit G).cone_point_unique_up_to_iso (limit.is_limit _)

@[simp]
lemma preserves_terminal.iso_hom : (preserves_terminal.iso G).hom = terminal_comparison G :=
rfl

instance : is_iso (terminal_comparison G) :=
begin
  rw ← preserves_terminal.iso_hom,
  apply_instance,
end

end terminal

section initial

/--
The map of an empty cocone is a colimit iff the mapped object is initial.
-/
def is_colimit_map_cocone_empty_cocone_equiv :
  is_colimit (G.map_cocone (as_empty_cocone.{v₁} X)) ≃ is_initial (G.obj X) :=
is_colimit_empty_cocone_equiv D _ _ (eq_to_iso rfl)

/-- The property of preserving initial objects expressed in terms of `is_initial`. -/
def is_initial.is_initial_obj [preserves_colimit (functor.empty.{v₁} C) G]
  (l : is_initial X) : is_initial (G.obj X) :=
is_colimit_map_cocone_empty_cocone_equiv G X (preserves_colimit.preserves l)

/-- The property of reflecting initial objects expressed in terms of `is_initial`. -/
def is_initial.is_initial_of_obj [reflects_colimit (functor.empty.{v₁} C) G]
  (l : is_initial (G.obj X)) : is_initial X :=
reflects_colimit.reflects ((is_colimit_map_cocone_empty_cocone_equiv G X).symm l)

variables [has_initial C]
/--
If `G` preserves the initial object and `C` has a initial object, then the image of the initial
object is initial.
-/
def is_colimit_of_has_initial_of_preserves_colimit [preserves_colimit (functor.empty.{v₁} C) G] :
  is_initial (G.obj (⊥_ C)) :=
initial_is_initial.is_initial_obj G (⊥_ C)

/--
If `C` has a initial object and `G` preserves initial objects, then `D` has a initial object
also.
Note this property is somewhat unique to colimits of the empty diagram: for general `J`, if `C`
has colimits of shape `J` and `G` preserves them, then `D` does not necessarily have colimits of
shape `J`.
-/
lemma has_initial_of_has_initial_of_preserves_colimit [preserves_colimit (functor.empty.{v₁} C) G] :
  has_initial D :=
⟨λ F,
begin
  haveI := has_colimit.mk ⟨_, is_colimit_of_has_initial_of_preserves_colimit G⟩,
  apply has_colimit_of_iso F.unique_from_empty,
end⟩

variable [has_initial D]
/--
If the initial comparison map for `G` is an isomorphism, then `G` preserves initial objects.
-/
def preserves_initial.of_iso_comparison
  [i : is_iso (initial_comparison G)] : preserves_colimit (functor.empty C) G :=
begin
  apply preserves_colimit_of_preserves_colimit_cocone initial_is_initial,
  apply (is_colimit_map_cocone_empty_cocone_equiv _ _).symm _,
  apply is_colimit.of_point_iso (colimit.is_colimit (functor.empty.{v₂} D)),
  apply i,
end

/-- If there is any isomorphism `⊥ ⟶ G.obj ⊥`, then `G` preserves initial objects. -/
def preserves_initial_of_is_iso
  (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : is_iso f] : preserves_colimit (functor.empty C) G :=
begin
  rw subsingleton.elim f (initial_comparison G) at i,
  exactI preserves_initial.of_iso_comparison G,
end

/-- If there is any isomorphism `⊥ ≅ G.obj ⊥ `, then `G` preserves initial objects. -/
def preserves_initial_of_iso
  (f : ⊥_ D ≅ G.obj (⊥_ C)) : preserves_colimit (functor.empty C) G :=
preserves_initial_of_is_iso G f.hom

variables [preserves_colimit (functor.empty.{v₁} C) G]

/-- If `G` preserves initial objects, then the initial comparison map for `G` is an isomorphism. -/
def preserves_initial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
(is_colimit_of_has_initial_of_preserves_colimit G).cocone_point_unique_up_to_iso
  (colimit.is_colimit _)

@[simp]
lemma preserves_initial.iso_hom : (preserves_initial.iso G).inv = initial_comparison G :=
rfl

instance : is_iso (initial_comparison G) :=
begin
  rw ← preserves_initial.iso_hom,
  apply_instance,
end

end initial

end category_theory.limits
