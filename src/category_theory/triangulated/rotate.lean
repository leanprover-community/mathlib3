/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
import category_theory.preadditive.additive_functor
import category_theory.triangulated.basic

/-!
# Rotate

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file adds the ability to rotate triangles and triangle morphisms.
It also shows that rotation gives an equivalence on the category of triangles.

-/

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v v₀ v₁ v₂ u u₀ u₁ u₂

namespace category_theory.pretriangulated
open category_theory.category

/--
We work in an preadditive category `C` equipped with an additive shift.
-/
variables {C : Type u} [category.{v} C] [preadditive C]
variables [has_shift C ℤ]

variables (X : C)

/--
If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `rotate` gives a triangle of the form:
```
      g       h        -f⟦1⟧'
  Y  ───> Z  ───>  X⟦1⟧ ───> Y⟦1⟧
```
-/
@[simps]
def triangle.rotate (T : triangle C) : triangle C := triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')

section

/--
Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `inv_rotate` gives a triangle that can be thought of as:
```
        -h⟦-1⟧'     f       g
  Z⟦-1⟧  ───>  X  ───> Y  ───> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z⟦-1⟧⟦1⟧` is
not necessarily equal to `Z`, but it is isomorphic, by the `counit_iso` of `shift C`)
-/
@[simps]
def triangle.inv_rotate (T : triangle C) : triangle C :=
triangle.mk (-T.mor₃⟦(-1:ℤ)⟧' ≫ (shift_shift_neg _ _).hom) T.mor₁
  (T.mor₂ ≫ (shift_neg_shift _ _).inv)

end

variables (C)

/--
Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def rotate : triangle C ⥤ triangle C :=
{ obj := triangle.rotate,
  map := λ T₁ T₂ f,
  { hom₁ := f.hom₂,
    hom₂ := f.hom₃,
    hom₃ := f.hom₁⟦1⟧',
    comm₃' := by { dsimp, simp only [comp_neg, neg_comp, ← functor.map_comp, f.comm₁], }, }, }

/--
The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def inv_rotate : triangle C ⥤ triangle C :=
{ obj := triangle.inv_rotate,
  map := λ T₁ T₂ f,
  { hom₁ := f.hom₃⟦-1⟧',
    hom₂ := f.hom₁,
    hom₃ := f.hom₂,
    comm₁' :=
    begin
      dsimp,
      rw [neg_comp, assoc, comp_neg, neg_inj, ← functor.map_comp_assoc, ← f.comm₃,
        functor.map_comp, assoc],
      erw [← nat_trans.naturality],
      refl,
    end,
    comm₃' := by { dsimp, erw [← f.comm₂_assoc, assoc, ← nat_trans.naturality], refl, }, }, }

variables {C}

variables [∀ n : ℤ, functor.additive (shift_functor C n)]

local attribute [simp] shift_shift_neg' shift_neg_shift'
  shift_shift_functor_comp_iso_id_add_neg_self_inv_app
  shift_shift_functor_comp_iso_id_add_neg_self_hom_app

/-- The unit isomorphism of the auto-equivalence of categories `triangle_rotation C` of
`triangle C` given by the rotation of triangles. -/
@[simps]
def rot_comp_inv_rot : 𝟭 (triangle C) ≅ rotate C ⋙ inv_rotate C :=
nat_iso.of_components (λ T, triangle.iso_mk _ _ ((shift_equiv C (1 : ℤ)).unit_iso.app T.obj₁)
  (iso.refl _) (iso.refl _) (by tidy) (by tidy) (by tidy)) (by tidy)

/-- The counit isomorphism of the auto-equivalence of categories `triangle_rotation C` of
`triangle C` given by the rotation of triangles. -/
@[simps]
def inv_rot_comp_rot : inv_rotate C ⋙ rotate C ≅ 𝟭 (triangle C) :=
nat_iso.of_components (λ T, triangle.iso_mk _ _ (iso.refl _) (iso.refl _)
  ((shift_equiv C (1 : ℤ)).counit_iso.app T.obj₃) (by tidy) (by tidy) (by tidy)) (by tidy)

variable (C)

/--
Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{ functor := rotate C,
  inverse := inv_rotate C,
  unit_iso := rot_comp_inv_rot,
  counit_iso := inv_rot_comp_rot, }

variables {C}

instance : is_equivalence (rotate C) :=
by { change is_equivalence (triangle_rotation C).functor, apply_instance, }
instance : is_equivalence (inv_rotate C) :=
by { change is_equivalence (triangle_rotation C).inverse, apply_instance, }

end category_theory.pretriangulated
