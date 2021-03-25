/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.additive.basic
import category_theory.shift
import category_theory.abelian.additive_functor
import category_theory.natural_isomorphism
import category_theory.triangulated.basic

/-!
# Rotate

This file adds the ability to rotate triangles and triangle morphisms.
It also shows that rotation gives an equivalence on the category of triangles.

-/

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v v₀ v₁ v₂ u u₀ u₁ u₂

namespace category_theory.triangulated
open category_theory.category

/--
We work in an additive category C equipped with an additive shift.
-/
variables (C : Type u) [category.{v} C] [has_shift C] [additive_category C]
  [functor.additive (shift C).functor] [functor.additive (shift C).inverse]
variables (X : C)

/--
If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
```
applying `rotate` gives a triangle of the form:
```
      g        h       -f[1]
  Y  ---> Z  --->  X[1] ---> Y[1]
```
-/
@[simps]
def triangle.rotate (T : triangle C) : triangle C :=
{ obj₁ := T.obj₂,
  obj₂ := T.obj₃,
  obj₃ := T.obj₁⟦1⟧,
  mor₁ := T.mor₂,
  mor₂ := T.mor₃,
  mor₃ := -T.mor₁⟦1⟧' }

/--
Given a triangle of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
```
applying `inv_rotate` gives a triangle that can be thought of as:
```
        -h[-1]     f       g
  Z[-1]  --->  X  ---> Y  ---> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z[-1][1]` is
not necessarily equal to `Z`, but it is isomorphic, by the counit_iso of (shift C))
-/
@[simps]
def triangle.inv_rotate (T : triangle C) : triangle C :=
{ obj₁ := T.obj₃⟦-1⟧,
  obj₂ := T.obj₁,
  obj₃ := T.obj₂,
  mor₁ := -T.mor₃⟦-1⟧' ≫ (shift C).unit_iso.inv.app T.obj₁,
  mor₂ := T.mor₁,
  mor₃ := T.mor₂ ≫ (shift C).counit_iso.inv.app T.obj₃ }



namespace triangle_morphism
variables {T₁ T₂ T₃ T₄: triangle C}
open triangle
/--
You can also rotate a triangle morphism to get a morphism between the two rotated triangles.
Given a triangle morphism of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
  |       |       |        |
  |a      |b      |c       |a[1]
  V       V       V        V
  X' ---> Y' ---> Z' ---> X'[1]
      f'      g'      h'
```
applying `rotate` gives a triangle morphism of the form:
```
      g        h       -f[1]
  Y  ---> Z  --->  X[1] ---> Y[1]
  |       |         |         |
  |b      |c        |a[1]     |b[1]
  V       V         V         V
  Y' ---> Z' ---> X'[1] ---> Y'[1]
      g'      h'       -f'[1]
```
-/
@[simps]
def rotate (f : triangle_morphism T₁ T₂) :
  triangle_morphism (T₁.rotate C) (T₂.rotate C):=
{ hom₁ := f.hom₂,
  hom₂ := f.hom₃,
  hom₃ := f.hom₁⟦1⟧',
  comm₃' := by simp only [rotate_mor₃, comp_neg, neg_comp, ← functor.map_comp, f.comm₁] }

/--
Given a triangle morphism of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
  |       |       |        |
  |a      |b      |c       |a[1]
  V       V       V        V
  X' ---> Y' ---> Z' ---> X'[1]
      f'      g'      h'
```
applying `inv_rotate` gives a triangle morphism that can be thought of as:
```
        -h[-1]      f         g
  Z[-1]  --->  X   --->  Y   --->  Z
    |          |         |         |
    |a         |b        |c        |a[1]
    V          V         V         V
  Z'[-1] --->  X'  --->  Y'  --->  Z'
        -h'[-1]     f'        g'
```
(note that this diagram doesn't technically fit the definition of triangle morphism,
as `Z[-1][1]` is not necessarily equal to `Z`, and `Z'[-1][1]` is not necessarily equal to `Z'`,
but they are isomorphic, by the `counit_iso` of `shift C`)
-/
@[simps]
def inv_rotate (f : triangle_morphism T₁ T₂) :
  triangle_morphism (T₁.inv_rotate C) (T₂.inv_rotate C) :=
{ hom₁ := f.hom₃⟦-1⟧',
  hom₂ := f.hom₁,
  hom₃ := f.hom₂,
  comm₁' := begin
    dsimp [inv_rotate_mor₁],
    simp_rw [comp_neg, neg_comp, ← assoc, ← functor.map_comp (shift C ).inverse, ← f.comm₃,
      functor.map_comp, assoc, equivalence.inv_fun_map, assoc, iso.hom_inv_id_app],
    congr,
    exact (category.comp_id f.hom₁).symm
  end }

end triangle_morphism

/--
Rotating triangles gives an endofunctor on the category of triangles in C.
-/
@[simps]
def rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.rotate C,
  map := λ _ _ f, f.rotate C }

/--
The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def inv_rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.inv_rotate C,
  map := λ _ _ f, f.inv_rotate C }

/--
There is a natural transformation between the identity functor on triangles,
and the composition of a rotation with an inverse rotation.
-/
@[simps]
def rot_comp_inv_rot_hom : 𝟭 (triangle C) ⟶ (rotate C) ⋙ (inv_rotate C) :=
{ app := λ T,
  { hom₁ := (shift C).unit.app T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := 𝟙 T.obj₃,
    comm₃' := begin
      dsimp,
      rw [id_comp, equivalence.counit_inv_app_functor],
    end } }

/--
There is a natural transformation between the composition of a rotation with an inverse rotation
on triangles, and the identity functor.
-/
@[simps]
def rot_comp_inv_rot_inv : (rotate C) ⋙ (inv_rotate C) ⟶ 𝟭 (triangle C) :=
{ app := λ T,
  { hom₁ := (shift C).unit_inv.app T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := 𝟙 T.obj₃ } }

/--
The natural transformations between the identity functor on triangles and the composition
of a rotation with an inverse rotation are natural isomorphisms (they are isomorphisms in the
category of functors).
-/
@[simps]
def rot_comp_inv_rot : 𝟭 (triangle C) ≅ (rotate C) ⋙ (inv_rotate C) :=
{ hom := rot_comp_inv_rot_hom C,
  inv := rot_comp_inv_rot_inv C }

/--
There is a natural transformation between the composition of an inverse rotation with a rotation
on triangles, and the identity functor.
-/
@[simps]
def inv_rot_comp_rot_hom : (inv_rotate C) ⋙ (rotate C) ⟶ 𝟭 (triangle C) :=
{ app := λ T,
  { hom₁ := 𝟙 T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := (shift C).counit.app T.obj₃ } }

/--
There is a natural transformation between the identity functor on triangles,
and  the composition of an inverse rotation with a rotation.
-/
@[simps]
def inv_rot_comp_rot_inv : 𝟭 (triangle C) ⟶ (inv_rotate C) ⋙ (rotate C) :=
{ app := λ T,
  { hom₁ := 𝟙 T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := (shift C).counit_inv.app T.obj₃ } }

/--
The natural transformations between the composition of a rotation with an inverse rotation
on triangles, and the identity functor on triangles are natural isomorphisms
(they are isomorphisms in the category of functors).
-/
@[simps]
def inv_rot_comp_rot : (inv_rotate C) ⋙ (rotate C) ≅ 𝟭 (triangle C) :=
{ hom := inv_rot_comp_rot_hom C,
  inv := inv_rot_comp_rot_inv C }

/--
Rotating triangles gives an auto-equivalence on the category of triangles.
-/
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{ functor := rotate C,
  inverse := inv_rotate C,
  unit_iso := rot_comp_inv_rot C,
  counit_iso := inv_rot_comp_rot C }

end category_theory.triangulated
