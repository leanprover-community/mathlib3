/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.natural_isomorphism
import category_theory.preadditive.additive_functor
import category_theory.shift
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
def triangle.rotate (T : triangle C) : triangle C := triangle.mk _ T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')

local attribute [semireducible] shift_shift_neg shift_neg_shift

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
triangle.mk _ (-T.mor₃⟦(-1:ℤ)⟧' ≫ (shift_shift_neg _ _).hom) T.mor₁
  (T.mor₂ ≫ (shift_neg_shift _ _).inv)

local attribute [reducible] shift_shift_neg shift_neg_shift discrete.add_monoidal

namespace triangle_morphism
variables {T₁ T₂ T₃ T₄: triangle C}
open triangle
/--
You can also rotate a triangle morphism to get a morphism between the two rotated triangles.
Given a triangle morphism of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
      f'      g'      h'
```
applying `rotate` gives a triangle morphism of the form:

```
      g        h       -f⟦1⟧
  Y  ───> Z  ───>  X⟦1⟧ ───> Y⟦1⟧
  │       │         │         │
  │b      │c        │a⟦1⟧     │b⟦1⟧'
  V       V         V         V
  Y' ───> Z' ───> X'⟦1⟧ ───> Y'⟦1⟧
      g'      h'       -f'⟦1⟧
```
-/
@[simps]
def rotate (f : triangle_morphism T₁ T₂) :
  triangle_morphism (T₁.rotate) (T₂.rotate):=
{ hom₁ := f.hom₂,
  hom₂ := f.hom₃,
  hom₃ := f.hom₁⟦1⟧',
  comm₃' := begin
    dsimp,
    simp only [rotate_mor₃, comp_neg, neg_comp, ← functor.map_comp, f.comm₁]
  end}

/--
Given a triangle morphism of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
      f'      g'      h'
```
applying `inv_rotate` gives a triangle morphism that can be thought of as:
```
        -h⟦-1⟧      f         g
  Z⟦-1⟧  ───>  X   ───>  Y   ───>  Z
    │          │         │         │
    │c⟦-1⟧'    │a        │b        │c
    V          V         V         V
  Z'⟦-1⟧ ───>  X'  ───>  Y'  ───>  Z'
       -h'⟦-1⟧     f'        g'
```
(note that this diagram doesn't technically fit the definition of triangle morphism,
as `Z⟦-1⟧⟦1⟧` is not necessarily equal to `Z`, and `Z'⟦-1⟧⟦1⟧` is not necessarily equal to `Z'`,
but they are isomorphic, by the `counit_iso` of `shift C`)
-/
@[simps]
def inv_rotate (f : triangle_morphism T₁ T₂) :
  triangle_morphism (T₁.inv_rotate) (T₂.inv_rotate) :=
{ hom₁ := f.hom₃⟦-1⟧',
  hom₂ := f.hom₁,
  hom₃ := f.hom₂,
  comm₁' := begin
    dsimp [inv_rotate_mor₁],
    simp only [discrete.functor_map_id, id_comp, preadditive.comp_neg, assoc,
      neg_inj, nat_trans.id_app, preadditive.neg_comp],
    rw [← functor.map_comp_assoc, ← f.comm₃, functor.map_comp_assoc],
    simp
  end,
  comm₃' := begin
    dsimp,
    simp only [discrete.functor_map_id, id_comp, opaque_eq_to_iso_inv, μ_inv_naturality,
      category.assoc, nat_trans.id_app, unit_of_tensor_iso_unit_inv_app],
    erw ε_naturality_assoc,
    simp
  end }

end triangle_morphism

/--
Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.rotate,
  map := λ _ _ f, f.rotate }


/--
The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def inv_rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.inv_rotate,
  map := λ _ _ f, f.inv_rotate }

variables [∀ n : ℤ, functor.additive (shift_functor C n)]

/-- There is a natural map from a triangle to the `inv_rotate` of its `rotate`. -/
@[simps]
def to_inv_rotate_rotate (T : triangle C) : T ⟶ inv_rotate.obj (rotate.obj T) :=
{ hom₁ := (shift_shift_neg _ _).inv,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := 𝟙 T.obj₃,
    comm₃' := begin
      dsimp,
      simp only [ε_app_obj, eq_to_iso.hom, discrete.functor_map_id, id_comp, eq_to_iso.inv,
        opaque_eq_to_iso_inv, category.assoc, obj_μ_inv_app, functor.map_comp, nat_trans.id_app,
        obj_ε_app, unit_of_tensor_iso_unit_inv_app],
      erw μ_inv_hom_app_assoc,
      refl
    end }

/--
There is a natural transformation between the identity functor on triangles in `C`,
and the composition of a rotation with an inverse rotation.
-/
@[simps]
def rot_comp_inv_rot_hom : 𝟭 (triangle C) ⟶ rotate ⋙ inv_rotate :=
{ app := to_inv_rotate_rotate,
  naturality' := begin
    introv, ext,
    { dsimp,
      simp only [nat_iso.cancel_nat_iso_inv_right_assoc, discrete.functor_map_id, id_comp,
        opaque_eq_to_iso_inv, μ_inv_naturality, assoc, nat_trans.id_app,
        unit_of_tensor_iso_unit_inv_app],
      erw ε_naturality },
    { dsimp, simp },
    { dsimp, simp }
  end }

/-- There is a natural map from the `inv_rotate` of the `rotate` of a triangle to itself. -/
@[simps]
def from_inv_rotate_rotate (T : triangle C) : inv_rotate.obj (rotate.obj T) ⟶ T :=
{ hom₁ := (shift_equiv C 1).unit_inv.app T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := 𝟙 T.obj₃,
    comm₃' := by { dsimp, simp, erw [μ_inv_hom_app, μ_inv_hom_app_assoc, category.comp_id] } }

/--
There is a natural transformation between the composition of a rotation with an inverse rotation
on triangles in `C`, and the identity functor.
-/
@[simps]
def rot_comp_inv_rot_inv : rotate ⋙ inv_rotate ⟶ 𝟭 (triangle C) :=
{ app := from_inv_rotate_rotate }

/--
The natural transformations between the identity functor on triangles in `C` and the composition
of a rotation with an inverse rotation are natural isomorphisms (they are isomorphisms in the
category of functors).
-/
@[simps]
def rot_comp_inv_rot : 𝟭 (triangle C) ≅ rotate ⋙ inv_rotate :=
{ hom := rot_comp_inv_rot_hom,
  inv := rot_comp_inv_rot_inv }

/-- There is a natural map from the `rotate` of the `inv_rotate` of a triangle to itself. -/
@[simps]
def from_rotate_inv_rotate (T : triangle C) : rotate.obj (inv_rotate.obj T) ⟶ T :=
{ hom₁ := 𝟙 T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := (shift_equiv C 1).counit.app T.obj₃,
    comm₂' := by { dsimp, simp, exact category.comp_id _ },
    comm₃' := by { dsimp, simp, erw [μ_inv_hom_app, category.comp_id, obj_zero_map_μ_app], simp } }

/--
There is a natural transformation between the composition of an inverse rotation with a rotation
on triangles in `C`, and the identity functor.
-/
@[simps]
def inv_rot_comp_rot_hom : inv_rotate ⋙ rotate ⟶ 𝟭 (triangle C) :=
{ app := from_rotate_inv_rotate }

/-- There is a natural map from a triangle to the `rotate` of its `inv_rotate`. -/
@[simps]
def to_rotate_inv_rotate (T : triangle C) : T ⟶ rotate.obj (inv_rotate.obj T) :=
{ hom₁ := 𝟙 T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := (shift_equiv C 1).counit_inv.app T.obj₃,
    comm₃' := by { dsimp, simp, erw [μ_inv_hom_app, category.comp_id, obj_zero_map_μ_app], simp } }

/--
There is a natural transformation between the identity functor on triangles in `C`,
and the composition of an inverse rotation with a rotation.
-/
@[simps]
def inv_rot_comp_rot_inv : 𝟭 (triangle C) ⟶ inv_rotate ⋙ rotate :=
{ app := to_rotate_inv_rotate,
  naturality' := by { introv, ext, { dsimp, simp }, { dsimp, simp },
    { dsimp, simp, erw [μ_inv_naturality, ε_naturality_assoc] }, } }

/--
The natural transformations between the composition of a rotation with an inverse rotation
on triangles in `C`, and the identity functor on triangles are natural isomorphisms
(they are isomorphisms in the category of functors).
-/
@[simps]
def inv_rot_comp_rot : inv_rotate ⋙ rotate ≅ 𝟭 (triangle C) :=
{ hom := inv_rot_comp_rot_hom,
  inv := inv_rot_comp_rot_inv }

/--
Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{ functor := rotate,
  inverse := inv_rotate,
  unit_iso := rot_comp_inv_rot,
  counit_iso := inv_rot_comp_rot,
  functor_unit_iso_comp' := by { introv, ext, { dsimp, simp }, { dsimp, simp },
    { dsimp, simp, erw [μ_inv_hom_app_assoc, μ_inv_hom_app], refl } } }

end category_theory.triangulated
