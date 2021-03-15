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

This file contains the definition of triangles in an additive category with an additive shift.


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
[functor.additive (shift C).functor]
variables (X : C)

/--
If you rotate a triangle, you get another triangle.
-/
def triangle.rotate (T : triangle C) : triangle C :=
{ obj1 := T.obj2,
  obj2 := T.obj3,
  obj3 := T.obj1⟦1⟧,
  mor1 := T.mor2,
  mor2 := T.mor3,
  mor3 := T.mor1⟦1⟧' }

def triangle.inv_rotate (T : triangle C) : triangle C :=
{ obj1 := T.obj3⟦-1⟧,
  obj2 := T.obj1,
  obj3 := T.obj2,
  mor1 := T.mor3⟦-1⟧' ≫ (shift C).unit_iso.inv.app T.obj1,
  mor2 := T.mor1,
  mor3 := T.mor2 ≫ (shift C).counit_iso.inv.app T.obj3}

namespace triangle_morphism
variables {T₁ T₂ T₃ T₄: triangle C}
/--
You can also rotate a triangle morphism to get a morphism between the two rotated triangles.
-/
def rotate (f : triangle_morphism T₁ T₂)
: triangle_morphism (T₁.rotate C) (T₂.rotate C):=
{ trimor1 := f.trimor2,
  trimor2 := f.trimor3,
  trimor3 := f.trimor1⟦1⟧',
  comm1 := by exact f.comm2,
  comm2 := by exact f.comm3,
  comm3 := begin
    change T₁.mor1⟦1⟧' ≫ (shift C).functor.map f.trimor2
      = (shift C).functor.map f.trimor1 ≫ T₂.mor1⟦1⟧',
    dsimp,
    repeat {rw ← functor.map_comp},
    rw f.comm1,
  end }

def inv_rotate (f : triangle_morphism T₁ T₂)
: triangle_morphism (T₁.inv_rotate C) (T₂.inv_rotate C) :=
{ trimor1 := f.trimor3⟦-1⟧',
  trimor2 := f.trimor1,
  trimor3 := f.trimor2,
  comm1 := begin
    change (T₁.mor3⟦-1⟧' ≫ (shift C).unit_iso.inv.app T₁.obj1) ≫ f.trimor1 =
    f.trimor3⟦-1⟧' ≫ (T₂.mor3⟦-1⟧' ≫ (shift C).unit_iso.inv.app T₂.obj1),
    rw ← assoc,
    dsimp,
    rw ← functor.map_comp (shift C).inverse,
    rw ← f.comm3,
    rw functor.map_comp,
    repeat {rw assoc},
    suffices h : (shift C).unit_iso.inv.app T₁.obj1 ≫ f.trimor1 = (shift C).inverse.map ((shift C).functor.map f.trimor1) ≫ (shift C).unit_iso.inv.app T₂.obj1,
    {
      rw h,
      refl,
    },
    {
      simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map, nat_iso.cancel_nat_iso_inv_left],
      exact (category.comp_id f.trimor1).symm,
    }
  end,
  comm2 := by exact f.comm1,
  comm3 := begin
    have h := f.comm2,
    change (triangle.inv_rotate C T₁).mor3 ≫ (shift C).functor.map ((shift C).inverse.map f.trimor3) = f.trimor2 ≫ (T₂.mor2 ≫ (shift C).counit_iso.inv.app T₂.obj3),
    rw ← assoc,
    rw ← f.comm2,
    change (T₁.mor2 ≫ (shift C).counit_iso.inv.app T₁.obj3) ≫ (shift C).functor.map ((shift C).inverse.map f.trimor3) = (T₁.mor2 ≫ f.trimor3) ≫ (shift C).counit_iso.inv.app T₂.obj3,
    repeat {rw assoc},
    simp only [equivalence.fun_inv_map, iso.inv_hom_id_app_assoc],
  end }

end triangle_morphism

/--
Rotating triangles gives an endofunctor on the category of triangles in C.
-/
def rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.rotate C,
  map := λ _ _ f, f.rotate C,
  map_id' := begin
    intro T₁,
    change triangle_morphism.rotate C (triangle_morphism_id T₁) =
    triangle_morphism_id (triangle.rotate C T₁),
    unfold triangle_morphism.rotate,
    dsimp,
    ext,
    { refl },
    { refl },
    {
      unfold triangle_morphism_id,
      dsimp only,
      rw (shift C).functor.map_id,
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
      change (shift C).functor.map (f.trimor1 ≫ g.trimor1) = ((shift C).functor.map f.trimor1) ≫ ((shift C).functor.map g.trimor1),
      rw (shift C).functor.map_comp,
    }
  end
}

def inv_rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.inv_rotate C,
  map := λ _ _ f, f.inv_rotate C,
  map_id' := begin
    intro T₁,
    change triangle_morphism.inv_rotate C (triangle_morphism_id T₁) =
    triangle_morphism_id (triangle.inv_rotate C T₁),
    unfold triangle_morphism.inv_rotate,
    ext,
    {
      unfold triangle_morphism_id,
      dsimp,
      rw (shift C).inverse.map_id,
      refl,
    },
    { refl },
    { refl }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.inv_rotate,
    ext,
    {
      change (shift C).inverse.map (f ≫ g).trimor3 =
      (shift C).inverse.map f.trimor3 ≫ (shift C).inverse.map g.trimor3,
      rw ← (shift C).inverse.map_comp,
      refl,
    },
    { refl },
    { refl }
  end
}

lemma rot_inv_rot :𝟭 (triangle C) ≅ (rotate C) ⋙ (inv_rotate C) :=
{
  hom := {
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
          let unit := (shift C).unit_iso,
          change T.mor1 = unit.hom.app T.obj1 ≫
          ((shift C).functor ⋙ (shift C).inverse).map T.mor1 ≫ unit.inv.app T.obj2,
          rw nat_iso.naturality_2 unit T.mor1,
          exact functor.id_map T.mor1,
        end,
        comm2 := by {rw [id_comp, comp_id], refl},
        comm3 := begin
          rw id_comp,
          change T.mor3 ≫ (shift C ^ 1).functor.map ((shift C).unit.app T.obj1) =
          T.mor3 ≫ (shift C).counit_iso.inv.app (T.obj1⟦1⟧),
          suffices h : (shift C ^ 1).functor.map ((shift C).unit.app T.obj1) =
          (shift C).counit_iso.inv.app (T.obj1⟦1⟧),
          { rw h },
          {
            dsimp,
            rw equivalence.counit_inv_app_functor,
          }
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
        change f.trimor1 ≫ (shift C).unit.app T₂.obj1 =
        (shift C).unit.app T₁.obj1 ≫ (f.trimor1⟦1⟧')⟦-1⟧',
        dsimp,
        simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map],
      },
      {
        change f.trimor2 ≫ 𝟙 T₂.obj2 = 𝟙 T₁.obj2 ≫ ((inv_rotate C).map ((rotate C).map f)).trimor2,
        simp only [id_comp, comp_id],
        refl,
      },
      {
        dsimp,
        change f.trimor3 ≫ 𝟙 T₂.obj3 = 𝟙 T₁.obj3 ≫ ((inv_rotate C).map ((rotate C).map f)).trimor3,
        simp only [id_comp, comp_id],
        refl,
      },
    end,
  },
  inv := {
    app := begin
      intro T,
      rw [functor.id_obj, functor.comp_obj],
      let f : triangle_morphism ((inv_rotate C).obj ((rotate C).obj T)) T :=
      {
        trimor1 := (shift C).unit_inv.app T.obj1,
        trimor2 := 𝟙 T.obj2,
        trimor3 := 𝟙 T.obj3,
        comm1 := begin
          change ((T.mor1⟦1⟧')⟦-1⟧' ≫ (shift C).unit_iso.inv.app T.obj2) ≫
          𝟙 T.obj2 = (shift C).unit_inv.app T.obj1 ≫ T.mor1,
          rw assoc,
          dsimp,
          simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map, comp_id, nat_iso.cancel_nat_iso_inv_left],
          dsimp,
          exact comp_id T.mor1,
        end,
        comm2 := sorry,
        comm3 := sorry
      },
      sorry,
    end,
    naturality' := sorry,
  }
}

/--
Rotating triangles gives an auto-equivalence on the category of triangles.
-/
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{
  functor := rotate C,
  inverse := inv_rotate C,
  unit_iso := rot_inv_rot C,
  counit_iso := {
    hom := {
      app := sorry,
      naturality' := sorry,
    },
    inv := {
      app := sorry,
      naturality' := sorry,
    }
  }
}

end category_theory.triangulated
