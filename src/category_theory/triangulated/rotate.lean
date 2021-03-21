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
applying "rotate" gives a triangle of the form:
```
      g        h        f[1]
  Y  ---> Z  --->  X[1] ---> Y[1]
```
-/
@[simps]
def triangle.rotate (T : triangle C) : triangle C :=
{ obj1 := T.obj2,
  obj2 := T.obj3,
  obj3 := T.obj1⟦1⟧,
  mor1 := T.mor2,
  mor2 := T.mor3,
  mor3 := -T.mor1⟦1⟧' }

/--
Given a triangle of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
```
applying "inv_rotate" gives a triangle that can be thought of as:
```
        h[-1]     f       g
  Z[-1]  ---> X  ---> Y  ---> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z[-1][1]` is
not necessarily equal to `Z`, but it is isomorphic, by the counit_iso of (shift C))
-/
@[simps]
def triangle.inv_rotate (T : triangle C) : triangle C :=
{ obj1 := T.obj3⟦-1⟧,
  obj2 := T.obj1,
  obj3 := T.obj2,
  mor1 := -T.mor3⟦-1⟧' ≫ (shift C).unit_iso.inv.app T.obj1,
  mor2 := T.mor1,
  mor3 := T.mor2 ≫ (shift C).counit_iso.inv.app T.obj3}



namespace triangle_morphism
variables {T₁ T₂ T₃ T₄: triangle C}
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
applying "rotate" gives a triangle morphism of the form:
```
      g        h        f[1]
  Y  ---> Z  --->  X[1] ---> Y[1]
  |       |         |         |
  |b      |c        |a[1]     |b[1]
  V       V         V         V
  Y' ---> Z' ---> X'[1] ---> Y'[1]
      g'      h'        f'[1]
```
-/
@[simps]
def rotate (f : triangle_morphism T₁ T₂)
: triangle_morphism (T₁.rotate C) (T₂.rotate C):=
{ trimor1 := f.trimor2,
  trimor2 := f.trimor3,
  trimor3 := f.trimor1⟦1⟧',
  comm1 := by exact f.comm2,
  comm2 := by exact f.comm3,
  comm3 := begin
    repeat {rw triangle.rotate_mor3},
    rw [comp_neg,neg_comp],
    repeat {rw ← functor.map_comp},
    rw f.comm1,
  end }

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
applying "inv_rotate" gives a triangle morphism that can be thought of as:
```
        h[-1]     f       g
  Z[-1]  ---> X  ---> Y  ---> Z
    |         |       |       |
    |a        |b      |c      |a[1]
    V         V       V       V
  Z'[-1] ---> X' ---> Y' ---> Z'
        h'[-1]    f'      g'
```
(note that this diagram doesn't technically fit the definition of triangle morphism,
as `Z[-1][1]` is not necessarily equal to `Z`, and `Z'[-1][1]` is not necessarily equal to `Z'`,
but they are isomorphic, by the counit_iso of (shift C))
-/
@[simps]
def inv_rotate (f : triangle_morphism T₁ T₂)
: triangle_morphism (T₁.inv_rotate C) (T₂.inv_rotate C) :=
{ trimor1 := f.trimor3⟦-1⟧',
  trimor2 := f.trimor1,
  trimor3 := f.trimor2,
  comm1 := begin
    simp only [triangle.inv_rotate_mor1],
    rw [comp_neg, neg_comp],
    rw ← assoc,
    dsimp,
    rw ← functor.map_comp (shift C ).inverse,
    rw ← f.comm3,
    rw functor.map_comp,
    repeat {rw assoc},
    suffices h : (shift C).unit_iso.inv.app T₁.obj1 ≫ f.trimor1 =
    (shift C).inverse.map ((shift C).functor.map f.trimor1) ≫ (shift C).unit_iso.inv.app T₂.obj1,
    {
      rw h,
      refl,
    },
    {
      simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map,
      nat_iso.cancel_nat_iso_inv_left],
      exact (category.comp_id f.trimor1).symm,
    }
  end,
  comm2 := by exact f.comm1,
  comm3 := begin
    have h := f.comm2,
    repeat {rw triangle.inv_rotate_mor3},
    rw ← assoc f.trimor2 _,
    rw ← f.comm2,
    dsimp,
    repeat {rw assoc},
    simp only [equivalence.fun_inv_map, iso.inv_hom_id_app_assoc],
  end }

end triangle_morphism

/--
Rotating triangles gives an endofunctor on the category of triangles in C.
-/
@[simps]
def rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.rotate C,
  map := λ _ _ f, f.rotate C,
  map_id' := begin
    intro T₁,
    simp only [triangle_category_to_category_struct_id],
    unfold triangle_morphism.rotate,
    dsimp,
    ext,
    { refl },
    { refl },
    {
      simp only [triangle_morphism_id_trimor3, (shift C).functor.map_id],
      refl,
    }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.rotate,
    ext,
    { refl },
    { refl },
    {
      dsimp,
      rw (shift C).functor.map_comp,
    }
  end
}

/--
The inverse rotation of triangles gives an endofunctor on the category of triangles in C.
-/
@[simps]
def inv_rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.inv_rotate C,
  map := λ _ _ f, f.inv_rotate C,
  map_id' := begin
    intro T₁,
    simp only [triangle_category_to_category_struct_id],
    ext,
    {
      simp only [triangle_morphism_id_trimor3, triangle_morphism.inv_rotate_trimor1,
      triangle_morphism_id_trimor1],
      dsimp,
      rw (shift C).inverse.map_id,
    },
    { refl },
    { refl }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.inv_rotate,
    ext,
    {
      simp only [triangle_morphism.comp_trimor3, triangle_morphism.comp_trimor1,
      triangle_category_to_category_struct_comp, functor.map_comp],
    },
    { refl },
    { refl }
  end
}

/--
There is a natural transformation between the identity functor on triangles,
and the composition of a rotation with an inverse rotation.
-/
@[simps]
def rot_comp_inv_rot_hom : 𝟭 (triangle C) ⟶ (rotate C) ⋙ (inv_rotate C) :=
{
  app := begin
    intro T,
    rw functor.id_obj,
    rw functor.comp_obj,
    let f : triangle_morphism T ((inv_rotate C).obj ((rotate C).obj T)) :=
    {
      trimor1 := (shift C).unit.app T.obj1,
      trimor2 := 𝟙 T.obj2,
      trimor3 := 𝟙 T.obj3,
      comm1 := begin
        rw comp_id,
        dsimp,
        rw [comp_neg, functor.additive.map_neg (shift C).inverse],
        rw ← functor.comp_map,
        simp only [neg_comp, comp_neg, functor.comp_map, iso.hom_inv_id_app_assoc,
        iso.hom_inv_id_app, assoc, equivalence.inv_fun_map, neg_neg],
        dsimp,
        simp only [comp_id],
      end,
      comm2 := by {rw [id_comp, comp_id], refl},
      comm3 := begin
        rw id_comp,
        dsimp,
        rw equivalence.counit_inv_app_functor,
      end
    },
    exact f,
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp only [functor.id_obj, congr_arg_mpr_hom_left, functor.id_map, functor.comp_map,
    id_comp, eq_to_hom_refl, congr_arg_mpr_hom_right, comp_id, functor.comp_obj],
    ext,
    {
      dsimp,
      simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map],
    },
    {
      dsimp,
      simp only [id_comp, comp_id],
    },
    {
      dsimp,
      simp only [id_comp, comp_id],
    },
  end
}

/--
There is a natural transformation between the composition of a rotation with an inverse rotation
on triangles, and the identity functor.
-/
@[simps]
def rot_comp_inv_rot_inv : (rotate C) ⋙ (inv_rotate C) ⟶ 𝟭 (triangle C) :=
{
  app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism ((inv_rotate C).obj ((rotate C).obj T)) T :=
    {
      trimor1 := (shift C).unit_inv.app T.obj1,
      trimor2 := 𝟙 T.obj2,
      trimor3 := 𝟙 T.obj3,
      comm1 := begin
        dsimp,
        simp only [neg_comp, iso.hom_inv_id_app, functor.additive.map_neg, assoc,
        equivalence.inv_fun_map, neg_neg, comp_id, nat_iso.cancel_nat_iso_inv_left],
        dsimp,
        simp only [comp_id],
      end,
      comm2 := begin
        dsimp,
        simp only [id_comp, comp_id],
      end,
      comm3 := begin
        dsimp,
        simp only [equivalence.counit_inv_functor_comp, assoc, id_comp, comp_id],
      end
    },
    exact f,
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp only [functor.id_obj, congr_arg_mpr_hom_left, functor.id_map, functor.comp_map,
    id_comp, eq_to_hom_refl, congr_arg_mpr_hom_right, comp_id, functor.comp_obj],
    dsimp,
    ext,
    {
      simp only [triangle_morphism.comp_trimor1,
      triangle_morphism.inv_rotate_trimor1, triangle_morphism.rotate_trimor3],
      dsimp,
      simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map,
      nat_iso.cancel_nat_iso_inv_left],
      dsimp,
      simp only [comp_id],
    },
    {
      simp only [triangle_morphism.comp_trimor2,
      triangle_morphism.inv_rotate_trimor2, triangle_morphism.rotate_trimor1,
      comp_id f.trimor2, id_comp f.trimor2],
    },
    {
      simp only [triangle_morphism.comp_trimor3, triangle_morphism.rotate_trimor2,
      triangle_morphism.inv_rotate_trimor3, comp_id f.trimor3, id_comp f.trimor3],
    },
  end
}

/--
The natural transformations between the identity functor on triangles and the composition
of a rotation with an inverse rotation are natural isomorphisms (they are isomorphisms in the
category of functors).
-/
@[simps]
def rot_comp_inv_rot :𝟭 (triangle C) ≅ (rotate C) ⋙ (inv_rotate C) :=
{
  hom := rot_comp_inv_rot_hom C,
  inv := rot_comp_inv_rot_inv C,
  hom_inv_id' := begin
    ext T,
    {
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_morphism.comp_trimor1,
      triangle_category_to_category_struct_comp, rot_comp_inv_rot_inv_app,
      rot_comp_inv_rot_hom_app, iso.hom_inv_id_app, triangle_morphism.id_comp,
      nat_trans.id_app, triangle_category_to_category_struct_id,
      triangle_morphism_id_trimor1, eq_to_hom_refl, congr_arg_mpr_hom_right,
      triangle_morphism.comp_id, functor.comp_obj, nat_trans.comp_app],
      dsimp,
      refl,
    },
    {
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      rot_comp_inv_rot_inv_app, triangle_morphism.comp_trimor2, rot_comp_inv_rot_hom_app,
      triangle_morphism.id_comp, nat_trans.id_app, triangle_category_to_category_struct_id,
      triangle_morphism_id_trimor2, eq_to_hom_refl, congr_arg_mpr_hom_right,
      triangle_morphism.comp_id, functor.comp_obj, nat_trans.comp_app],
      dsimp,
      simp only [comp_id],
    },
    {
      simp,
      dsimp,
      simp only [comp_id],
    }
  end, -- (deterministic) timeout when replace simp with squeeze_simp
  inv_hom_id' := begin
    ext T,
    {
      simp,
      dsimp,
      refl,
    },
    {
      simp,
      dsimp,
      simp only [comp_id],
    },
    {
      simp,
      dsimp,
      simp only [comp_id],
    }
  end -- (deterministic) timeout when replace simp with squeeze_simp
}

/--
There is a natural transformation between the composition of an inverse rotation with a rotation
on triangles, and the identity functor.
-/
@[simps]
def inv_rot_comp_rot_hom : (inv_rotate C) ⋙ (rotate C) ⟶ 𝟭 (triangle C) :=
{
  app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism ((rotate C).obj((inv_rotate C).obj T)) T :=
    {
      trimor1 := 𝟙 T.obj1,
      trimor2 := 𝟙 T.obj2,
      trimor3 := (shift C).counit.app T.obj3,
      comm1 := begin
        dsimp,
        simp only [id_comp, comp_id]
      end,
      comm2 := begin
        dsimp ,
        simp only [iso.inv_hom_id_app, assoc, id_comp],
        dsimp,
        simp only [comp_id]
      end,
      comm3 := begin
        dsimp,
        simp only [equivalence.counit_inv_functor_comp, equivalence.fun_inv_map,
        functor.additive.map_neg, assoc, neg_neg, comp_id,functor.map_comp,
        (shift C).functor.map_id]
      end
    },
    exact f,
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp,
    dsimp,
    ext,
    {
      simp only [triangle_morphism.comp_trimor1, triangle_morphism.inv_rotate_trimor2,
      triangle_morphism.rotate_trimor1, comp_id f.trimor1, id_comp f.trimor1],
    },
    {
      simp only [triangle_morphism.rotate_trimor2, triangle_morphism.comp_trimor2,
      triangle_morphism.inv_rotate_trimor3, comp_id f.trimor2, id_comp f.trimor2],
    },
    {
      simp only [triangle_morphism.comp_trimor3, triangle_morphism.inv_rotate_trimor1,
      triangle_morphism.rotate_trimor3],
      dsimp,
      simp only [iso.inv_hom_id_app, equivalence.fun_inv_map, nat_iso.cancel_nat_iso_hom_left,
      assoc],
      dsimp,
      rw comp_id,
    }
  end
}

/--
There is a natural transformation between the identity functor on triangles,
and  the composition of an inverse rotation with a rotation.
-/
@[simps]
def inv_rot_comp_rot_inv : 𝟭 (triangle C) ⟶ (inv_rotate C) ⋙ (rotate C) :=
{
  app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism T ((rotate C).obj ((inv_rotate C).obj T)) :=
    {
      trimor1 := 𝟙 T.obj1,
      trimor2 := 𝟙 T.obj2,
      trimor3 := (shift C).counit_inv.app T.obj3,
      comm1 := begin
        dsimp,
        simp only [id_comp, comp_id],
      end,
      comm2 := begin
        dsimp,
        simp only [id_comp],
      end,
      comm3 := begin
        dsimp,
        simp only [equivalence.counit_inv_functor_comp, equivalence.fun_inv_map,
        functor.additive.map_neg, assoc, iso.inv_hom_id_app_assoc, neg_neg, functor.map_comp,
        (shift C).functor.map_id]
      end
    },
    exact f
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp,
    dsimp,
    ext,
    {
      simp only [triangle_morphism.comp_trimor1, triangle_morphism.inv_rotate_trimor2,
      triangle_morphism.rotate_trimor1, id_comp, comp_id],
    },
    {
      simp only [triangle_morphism.rotate_trimor2, triangle_morphism.comp_trimor2,
      id_comp, comp_id, triangle_morphism.inv_rotate_trimor3],
    },
    {
      simp only [triangle_morphism.comp_trimor3, triangle_morphism.inv_rotate_trimor1,
      triangle_morphism.rotate_trimor3],
      dsimp,
      simp only [equivalence.fun_inv_map, iso.inv_hom_id_app_assoc],
    }
  end
}

/--
The natural transformations between the composition of a rotation with an inverse rotation
on triangles, and the identity functor on triangles are natural isomorphisms
(they are isomorphisms in the category of functors).
-/
@[simps]
def inv_rot_comp_rot : (inv_rotate C) ⋙ (rotate C) ≅ 𝟭 (triangle C) :=
{
  hom := inv_rot_comp_rot_hom C,
  inv := inv_rot_comp_rot_inv C,
  hom_inv_id' := begin
    ext T,
    {
      dsimp,
      simp
    },
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      triangle_morphism.id_comp, triangle_category_to_category_struct_id, eq_to_hom_refl,
      congr_arg_mpr_hom_right, comp_id, triangle_morphism.comp_id, functor.comp_obj],
    },
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      iso.hom_inv_id_app, triangle_morphism.id_comp, triangle_category_to_category_struct_id,
      eq_to_hom_refl, congr_arg_mpr_hom_right, triangle_morphism.comp_id, functor.comp_obj],
      dsimp,
      refl,
    }
  end,
  inv_hom_id' := begin
    ext T,
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      triangle_morphism.id_comp, triangle_category_to_category_struct_id, eq_to_hom_refl,
      congr_arg_mpr_hom_right, comp_id, triangle_morphism.comp_id, functor.comp_obj],
    },
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      triangle_morphism.id_comp, triangle_category_to_category_struct_id, eq_to_hom_refl,
      congr_arg_mpr_hom_right, comp_id, triangle_morphism.comp_id, functor.comp_obj],
    },
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      iso.inv_hom_id_app, triangle_morphism.id_comp, triangle_category_to_category_struct_id,
      eq_to_hom_refl, congr_arg_mpr_hom_right, triangle_morphism.comp_id, functor.comp_obj],
      dsimp,
      refl,
    }
  end
}

/--
Rotating triangles gives an auto-equivalence on the category of triangles.
-/
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{
  functor := rotate C,
  inverse := inv_rotate C,
  unit_iso := rot_comp_inv_rot C,
  counit_iso := inv_rot_comp_rot C,
  functor_unit_iso_comp' := begin
    intro T,
    ext,
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      triangle_morphism.id_comp, triangle_category_to_category_struct_id, eq_to_hom_refl,
      congr_arg_mpr_hom_right, comp_id, triangle_morphism.comp_id, functor.comp_obj]
    },
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      triangle_morphism.id_comp, triangle_category_to_category_struct_id, eq_to_hom_refl,
      congr_arg_mpr_hom_right, comp_id, triangle_morphism.comp_id, functor.comp_obj],
    },
    {
      dsimp,
      simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_category_to_category_struct_comp,
      triangle_morphism.id_comp, triangle_category_to_category_struct_id, eq_to_hom_refl,
      congr_arg_mpr_hom_right, triangle_morphism.comp_id, functor.comp_obj,
      equivalence.functor_unit_comp],
    }
  end
}

end category_theory.triangulated
