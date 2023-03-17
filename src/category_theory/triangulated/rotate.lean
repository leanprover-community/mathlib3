/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.preadditive.additive_functor
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
triangle.mk (-T.mor₃⟦(-1:ℤ)⟧' ≫ (shift_shift_neg _ _).hom) T.mor₁
  (T.mor₂ ≫ (shift_neg_shift _ _).inv)

end

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
  end }

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
    rw [← functor.map_comp_assoc, ← f.comm₃, functor.map_comp_assoc, μ_naturality_assoc,
      nat_trans.naturality, functor.id_map],
  end,
  comm₃' := begin
    dsimp,
    simp only [discrete.functor_map_id, id_comp, μ_inv_naturality,
      category.assoc, nat_trans.id_app, unit_of_tensor_iso_unit_inv_app],
    erw ε_naturality_assoc,
    rw comm₂_assoc
  end }

end triangle_morphism

variables (C)

/--
Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def rotate : triangle C ⥤ triangle C :=
{ obj := triangle.rotate,
  map := λ _ _ f, f.rotate }

/--
The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def inv_rotate : triangle C ⥤ triangle C :=
{ obj := triangle.inv_rotate,
  map := λ _ _ f, f.inv_rotate }

variables {C}

variables [∀ n : ℤ, functor.additive (shift_functor C n)]

/-- There is a natural map from a triangle to the `inv_rotate` of its `rotate`. -/
@[simps]
def to_inv_rotate_rotate (T : triangle C) : T ⟶ (inv_rotate C).obj ((rotate C).obj T) :=
{ hom₁ := (shift_shift_neg _ _).inv,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := 𝟙 T.obj₃,
    comm₃' := begin
      dsimp,
      simp only [ε_app_obj, eq_to_iso.hom, discrete.functor_map_id, id_comp, eq_to_iso.inv,
        category.assoc, obj_μ_inv_app, functor.map_comp, nat_trans.id_app, obj_ε_app,
        unit_of_tensor_iso_unit_inv_app],
      erw μ_inv_hom_app_assoc,
      refl
    end }

/--
There is a natural transformation between the identity functor on triangles in `C`,
and the composition of a rotation with an inverse rotation.
-/
@[simps]
def rot_comp_inv_rot_hom : 𝟭 (triangle C) ⟶ rotate C ⋙ inv_rotate C :=
{ app := to_inv_rotate_rotate,
  naturality' := begin
    introv, ext,
    { dsimp,
      simp only [nat_iso.cancel_nat_iso_inv_right_assoc, discrete.functor_map_id, id_comp,
        μ_inv_naturality, assoc, nat_trans.id_app, unit_of_tensor_iso_unit_inv_app],
      erw ε_naturality },
    { dsimp, rw [comp_id, id_comp] },
    { dsimp, rw [comp_id, id_comp] },
  end }

/-- There is a natural map from the `inv_rotate` of the `rotate` of a triangle to itself. -/
@[simps]
def from_inv_rotate_rotate (T : triangle C) : (inv_rotate C).obj ((rotate C).obj T) ⟶ T :=
{ hom₁ := (shift_equiv C 1).unit_inv.app T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := 𝟙 T.obj₃,
    comm₃' := begin
      dsimp,
      rw [unit_of_tensor_iso_unit_inv_app, ε_app_obj],
      simp only [discrete.functor_map_id, nat_trans.id_app, id_comp, assoc, functor.map_comp,
        obj_μ_app, obj_ε_inv_app, comp_id, μ_inv_hom_app_assoc],
      erw [μ_inv_hom_app, μ_inv_hom_app_assoc, category.comp_id]
    end }

/--
There is a natural transformation between the composition of a rotation with an inverse rotation
on triangles in `C`, and the identity functor.
-/
@[simps]
def rot_comp_inv_rot_inv : rotate C ⋙ inv_rotate C ⟶ 𝟭 (triangle C) :=
{ app := from_inv_rotate_rotate }

/--
The natural transformations between the identity functor on triangles in `C` and the composition
of a rotation with an inverse rotation are natural isomorphisms (they are isomorphisms in the
category of functors).
-/
@[simps]
def rot_comp_inv_rot : 𝟭 (triangle C) ≅ rotate C ⋙ inv_rotate C :=
{ hom := rot_comp_inv_rot_hom,
  inv := rot_comp_inv_rot_inv }

/-- There is a natural map from the `rotate` of the `inv_rotate` of a triangle to itself. -/
@[simps]
def from_rotate_inv_rotate (T : triangle C) : (rotate C).obj ((inv_rotate C).obj T) ⟶ T :=
{ hom₁ := 𝟙 T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := (shift_equiv C 1).counit.app T.obj₃,
    comm₂' := begin
      dsimp,
      rw unit_of_tensor_iso_unit_inv_app,
      simp only [discrete.functor_map_id, nat_trans.id_app,
        id_comp, add_neg_equiv_counit_iso_hom, eq_to_hom_refl, nat_trans.comp_app, assoc,
        μ_inv_hom_app_assoc, ε_hom_inv_app],
      exact category.comp_id _,
    end,
    comm₃' := begin
      dsimp,
      simp only [discrete.functor_map_id, nat_trans.id_app, id_comp, functor.map_neg,
        functor.map_comp, obj_μ_app, obj_ε_inv_app, comp_id, assoc, μ_naturality_assoc, neg_neg,
        category_theory.functor.map_id, add_neg_equiv_counit_iso_hom, eq_to_hom_refl,
        nat_trans.comp_app],
      erw [μ_inv_hom_app, category.comp_id, obj_zero_map_μ_app],
      rw [discrete.functor_map_id, nat_trans.id_app, comp_id],
    end }

/--
There is a natural transformation between the composition of an inverse rotation with a rotation
on triangles in `C`, and the identity functor.
-/
@[simps]
def inv_rot_comp_rot_hom : inv_rotate C ⋙ rotate C ⟶ 𝟭 (triangle C) :=
{ app := from_rotate_inv_rotate }

/-- There is a natural map from a triangle to the `rotate` of its `inv_rotate`. -/
@[simps]
def to_rotate_inv_rotate (T : triangle C) : T ⟶ (rotate C).obj ((inv_rotate C).obj T) :=
{ hom₁ := 𝟙 T.obj₁,
    hom₂ := 𝟙 T.obj₂,
    hom₃ := (shift_equiv C 1).counit_inv.app T.obj₃,
    comm₃' := begin
      dsimp,
      rw category_theory.functor.map_id,
      simp only [comp_id, add_neg_equiv_counit_iso_inv, eq_to_hom_refl, id_comp, nat_trans.comp_app,
        discrete.functor_map_id, nat_trans.id_app, functor.map_neg, functor.map_comp, obj_μ_app,
        obj_ε_inv_app, assoc, μ_naturality_assoc, neg_neg, μ_inv_hom_app_assoc],
      erw [μ_inv_hom_app, category.comp_id, obj_zero_map_μ_app],
      simp only [discrete.functor_map_id, nat_trans.id_app, comp_id, ε_hom_inv_app_assoc],
    end }

/--
There is a natural transformation between the identity functor on triangles in `C`,
and the composition of an inverse rotation with a rotation.
-/
@[simps]
def inv_rot_comp_rot_inv : 𝟭 (triangle C) ⟶ inv_rotate C ⋙ rotate C :=
{ app := to_rotate_inv_rotate,
  naturality' := begin
    introv, ext,
    { dsimp, rw [comp_id, id_comp] },
    { dsimp, rw [comp_id, id_comp] },
    { dsimp,
      rw [add_neg_equiv_counit_iso_inv, eq_to_hom_map, eq_to_hom_refl, id_comp],
      simp only [nat_trans.comp_app, assoc],
      erw [μ_inv_naturality, ε_naturality_assoc] },
  end }

/--
The natural transformations between the composition of a rotation with an inverse rotation
on triangles in `C`, and the identity functor on triangles are natural isomorphisms
(they are isomorphisms in the category of functors).
-/
@[simps]
def inv_rot_comp_rot : inv_rotate C ⋙ rotate C ≅ 𝟭 (triangle C) :=
{ hom := inv_rot_comp_rot_hom,
  inv := inv_rot_comp_rot_inv }

variables (C)

/--
Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{ functor := rotate C,
  inverse := inv_rotate C,
  unit_iso := rot_comp_inv_rot,
  counit_iso := inv_rot_comp_rot,
  functor_unit_iso_comp' := begin
    introv, ext,
    { dsimp, rw comp_id },
    { dsimp, rw comp_id },
    { dsimp,
      rw unit_of_tensor_iso_unit_inv_app,
      simp only [discrete.functor_map_id, nat_trans.id_app, id_comp, functor.map_comp, obj_ε_app,
        obj_μ_inv_app, assoc, add_neg_equiv_counit_iso_hom, eq_to_hom_refl, nat_trans.comp_app,
        ε_inv_app_obj, comp_id, μ_inv_hom_app_assoc],
      erw [μ_inv_hom_app_assoc, μ_inv_hom_app],
      refl }
  end }

variables {C}

instance : is_equivalence (rotate C) :=
by { change is_equivalence (triangle_rotation C).functor, apply_instance, }
instance : is_equivalence (inv_rotate C) :=
by { change is_equivalence (triangle_rotation C).inverse, apply_instance, }

end category_theory.pretriangulated
