/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import algebraic_topology.simplicial_object
import category_theory.limits.shapes.wide_pullbacks
import category_theory.arrow

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : arrow C`:
1. `f.cech_nerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmented_cech_nerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `simplicial_object.cech_nerve` and `simplicial_object.augmented_cech_nerve` are
  functorial versions of 1 resp. 2.

-/

open category_theory
open category_theory.limits

noncomputable theory

universes v u

variables {C : Type u} [category.{v} C]

namespace category_theory.arrow

variables (f : arrow C)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The Čech nerve associated to an arrow. -/
@[simps]
def cech_nerve : simplicial_object C :=
{ obj := λ n, wide_pullback f.right
    (λ i : ulift (fin (n.unop.len + 1)), f.left) (λ i, f.hom),
  map := λ m n g, wide_pullback.lift (wide_pullback.base _)
    (λ i, wide_pullback.π _ $ ulift.up $ g.unop.to_preorder_hom i.down) (by tidy) }

/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
def augmented_cech_nerve : simplicial_object.augmented C :=
{ left := f.cech_nerve,
  right := f.right,
  hom := { app := λ i, wide_pullback.base _ } }

end category_theory.arrow

namespace category_theory
namespace simplicial_object

variables [∀ (n : ℕ) (f : arrow C),
  has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def cech_nerve : arrow C ⥤ simplicial_object C :=
{ obj := λ f, f.cech_nerve,
  map := λ f g F,
  { app := λ n, wide_pullback.lift (wide_pullback.base _ ≫ F.right)
      (λ i, wide_pullback.π _ i ≫ F.left) (λ i, by simp [← category.assoc]) },
  -- tidy needs a bit of help here...
  map_id' := by { intros i, ext, tidy },
  map_comp' := begin
    intros f g h F G,
    ext,
    all_goals {
      dsimp,
      simp only [category.assoc, limits.wide_pullback.lift_base,
        limits.wide_pullback.lift_π, limits.limit.lift_π_assoc],
      simpa only [← category.assoc] },
  end }

/-- The augmented Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def augmented_cech_nerve : arrow C ⥤ simplicial_object.augmented C :=
{ obj := λ f, f.augmented_cech_nerve,
  map := λ f g F,
  { left := cech_nerve.map F,
    right := F.right } }

/-- A helper function used in defining the Cech adjunction. -/
@[simps]
def equivalence_right_to_left (X : simplicial_object.augmented C) (F : arrow C)
  (G : X ⟶ F.augmented_cech_nerve) : (augmented.to_arrow.obj X ⟶ F) :=
{ left := G.left.app _ ≫ wide_pullback.π _ ⟨0⟩,
  right := G.right,
  w' := begin
    have := G.w,
    apply_fun (λ e, e.app (opposite.op $ simplex_category.mk 0)) at this,
    tidy,
  end }

/-- A helper function used in defining the Cech adjunction. -/
@[simps]
def equivalence_left_to_right (X : simplicial_object.augmented C) (F : arrow C)
  (G : augmented.to_arrow.obj X ⟶ F) : (X ⟶ F.augmented_cech_nerve) :=
{ left :=
  { app := λ x, limits.wide_pullback.lift (X.hom.app _ ≫ G.right)
      (λ i, X.left.map (simplex_category.const x.unop i.down).op ≫ G.left) (by tidy),
    naturality' := begin
      intros x y f,
      ext,
      { dsimp,
        simp only [wide_pullback.lift_π, category.assoc],
        rw [← category.assoc, ← X.left.map_comp],
        refl },
      { dsimp,
        simp only [functor.const.obj_map, nat_trans.naturality_assoc,
          wide_pullback.lift_base, category.assoc],
        erw category.id_comp }
    end },
  right := G.right }

/-- A helper function used in defining the Cech adjunction. -/
@[simps]
def cech_nerve_equiv (X : simplicial_object.augmented C) (F : arrow C) :
  (augmented.to_arrow.obj X ⟶ F) ≃ (X ⟶ F.augmented_cech_nerve) :=
{ to_fun := equivalence_left_to_right _ _,
  inv_fun := equivalence_right_to_left _ _,
  left_inv := begin
    intro A,
    dsimp,
    ext,
    { dsimp,
      erw wide_pullback.lift_π,
      nth_rewrite 1 ← category.id_comp A.left,
      congr' 1,
      convert X.left.map_id _,
      rw ← op_id,
      congr' 1,
      ext ⟨a,ha⟩,
      change a < 1 at ha,
      change 0 = a,
      linarith },
    { refl, }
  end,
  right_inv := begin
    intro A,
    dsimp,
    ext _ ⟨j⟩,
    { dsimp,
      simp only [arrow.cech_nerve_map, wide_pullback.lift_π, nat_trans.naturality_assoc],
      erw wide_pullback.lift_π,
      refl },
    { dsimp,
      erw wide_pullback.lift_base,
      have := A.w,
      apply_fun (λ e, e.app x) at this,
      rw nat_trans.comp_app at this,
      erw this,
      refl },
    { refl }
  end }

/-- The augmented Cech nerve construction is right adjoint to the `to_arrow` functor. -/
@[simps]
def cech_adjunction : (augmented.to_arrow : _ ⥤ arrow C) ⊣ augmented_cech_nerve :=
adjunction.mk_of_hom_equiv { hom_equiv := cech_nerve_equiv }

end simplicial_object
end category_theory
