/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.preserves.limits
import category_theory.limits.shapes

/-!
# Preserving equalizers

Constructions to relate the notions of preserving equalizers and reflecting equalizers
to concrete forks.

In particular, we show that `equalizer_comparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/

noncomputable theory

universes v u₁ u₂

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

namespace preserves

open category_theory.limits.walking_parallel_pair

variables {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

/--
The map of a fork is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `fork.of_ι` with `functor.map_cone`.
-/
def fork_map_cone_limit :
  is_limit (G.map_cone (fork.of_ι h w)) ≃
  is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g)) :=
(is_limit.postcompose_hom_equiv (diagram_iso_parallel_pair _) _).symm.trans
  (is_limit.equiv_iso_limit (fork.ext (iso.refl _) (by simp [fork.ι_eq_app_zero])))

/-- The property of preserving equalizers expressed in terms of forks. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (parallel_pair f g) G]
  (l : is_limit (fork.of_ι h w)) :
  is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g)) :=
fork_map_cone_limit G w (preserves_limit.preserves l)

/-- The property of reflecting equalizers expressed in terms of forks. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (parallel_pair f g) G]
  (l : is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g))) :
  is_limit (fork.of_ι h w) :=
reflects_limit.reflects ((fork_map_cone_limit G w).symm l)

variables (f g) [has_equalizer f g]

/--
If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
def is_limit_of_has_equalizer_of_preserves_limit
  [preserves_limit (parallel_pair f g) G] :
  is_limit (fork.of_ι (G.map (equalizer.ι f g))
                      (by simp only [←G.map_comp, equalizer.condition])) :=
map_is_limit_of_preserves_of_is_limit G _ (equalizer_is_equalizer f g)

variables [has_equalizer (G.map f) (G.map g)]
/--
The comparison morphism from the map of an equalizer to the equalizer in the target category.
This is an isomorphism if and only if `G` preserves the equalizer of `(f,g)`, shown in
`preserves_equalizer` and `preserves_equalizers_iso`.
-/
def equalizer_comparison : G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
equalizer.lift (G.map (equalizer.ι _ _)) (by simp only [←G.map_comp, equalizer.condition])

/--
If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
def preserves_equalizer_of_iso_comparison [i : is_iso (equalizer_comparison G f g)] :
  preserves_limit (parallel_pair f g) G :=
begin
  apply preserves_limit_of_preserves_limit_cone (equalizer_is_equalizer f g),
  apply (fork_map_cone_limit _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (parallel_pair (G.map f) (G.map g))),
  apply i,
end

variables [preserves_limit (parallel_pair f g) G]
/--
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def preserves_equalizers_iso :
  G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_has_equalizer_of_preserves_limit G f g)
  (limit.is_limit _)

@[simp]
lemma preserves_equalizers_iso_hom :
  (preserves_equalizers_iso G f g).hom = equalizer_comparison G f g :=
rfl

instance : is_iso (equalizer_comparison G f g) :=
begin
  rw ← preserves_equalizers_iso_hom,
  apply_instance
end

end preserves
