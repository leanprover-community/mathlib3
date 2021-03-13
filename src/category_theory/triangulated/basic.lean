/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.additive.basic
import category_theory.shift
import category_theory.abelian.additive_functor

/-!
# Triangles

This file contains the definition of triangles in an additive category with an additive shift.

TODO: generalise this to n-angles in n-angulated categories as in https://arxiv.org/abs/1006.4592
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
A triangle in C is a sextuple (X,Y,Z,f,g,h) where X,Y,Z are objects of C,
and f: X → Y, g: Y → Z, h: Z → ΣX are morphisms in C.
See https://stacks.math.columbia.edu/tag/0144.
-/
structure triangle :=
(obj1 : C)
(obj2 : C)
(obj3 : C)
(mor1 : obj1 ⟶ obj2)
(mor2 : obj2 ⟶ obj3)
(mor3 : obj3 ⟶ obj1⟦1⟧)

local attribute [instance] has_zero_object.has_zero
instance [has_zero_object C] : inhabited (triangle C) :=
⟨{ obj1 := 0,
  obj2 := 0,
  obj3 := 0,
  mor1 := 0,
  mor2 := 0,
  mor3 := 0 }⟩

/--
For each object in C, there is a triangle of the form (X,X,0,𝟙_X,0,0)
-/
def contractible_triangle (X : C) : triangle C :=
{ obj1 := X,
  obj2 := X,
  obj3 := 0,
  mor1 := 𝟙 X,
  mor2 := 0,
  mor3 := 0 }

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
  mor3 := T.mor2 ≫ (shift C).counit_iso.inv.app T.obj3,}


variable {C}

/--
A morphism of triangles (X,Y,Z,f,g,h)→(X',Y',Z',f',g',h') in C is a triple of morphisms
a: X → X', b: Y → Y', c: Z → Z' such that b ≫ f = f' ≫ a, c ≫ g = g' ≫ b,
and a[1] ≫ h = h' ≫ c.
In other words, we have a commutative diagram:
     f      g      h
  X  --> Y  --> Z  --> X[1]
  |      |      |       |
  |a     |b     |c      |a[1]
  V      V      V       V
  X' --> Y' --> Z' --> X'[1]
     f'     g'     h'

See https://stacks.math.columbia.edu/tag/0144.
-/
@[ext]
structure triangle_morphism (T₁ : triangle C) (T₂ : triangle C):=
(trimor1 : T₁.obj1 ⟶ T₂.obj1)
(trimor2 : T₁.obj2 ⟶ T₂.obj2)
(trimor3 : T₁.obj3 ⟶ T₂.obj3)
(comm1: T₁.mor1 ≫ trimor2 = trimor1 ≫ T₂.mor1)
(comm2: T₁.mor2 ≫ trimor3 = trimor2 ≫ T₂.mor2)
(comm3: T₁.mor3 ≫ trimor1⟦1⟧' = trimor3 ≫ T₂.mor3)
attribute [reassoc] triangle_morphism.comm1 triangle_morphism.comm2 triangle_morphism.comm3

/--
The identity triangle morphism.
-/
def triangle_morphism_id (T : triangle C) : triangle_morphism T T :=
{ trimor1 := 𝟙 T.obj1,
  trimor2 := 𝟙 T.obj2,
  trimor3 := 𝟙 T.obj3,
  comm1 := by rw [id_comp, comp_id],
  comm2 := by rw [id_comp, comp_id],
  comm3 := by { dsimp, simp } }

instance (T: triangle C): inhabited (triangle_morphism T T) := ⟨ triangle_morphism_id T ⟩

variables {T₁ T₂ T₃ T₄: triangle C}
/--
Composition of triangle morphisms gives a triangle morphism.
-/
def triangle_morphism.comp (f : triangle_morphism T₁ T₂) (g : triangle_morphism T₂ T₃) :
triangle_morphism T₁ T₃ :=
{ trimor1 := f.trimor1 ≫ g.trimor1,
  trimor2 := f.trimor2 ≫ g.trimor2,
  trimor3 := f.trimor3 ≫ g.trimor3,
  comm1 := by rw [f.comm1_assoc, g.comm1, assoc],
  comm2 := by rw [f.comm2_assoc, g.comm2, assoc],
  comm3 := by rw [functor.map_comp, f.comm3_assoc, g.comm3, assoc], }

namespace triangle_morphism

@[simp]
lemma id_comp (f: triangle_morphism T₁ T₂) : (triangle_morphism_id T₁).comp f = f :=
begin
  unfold comp,
  unfold triangle_morphism_id,
  cases f,
  simp only [eq_self_iff_true, id_comp, and_self],
end

@[simp]
lemma comp_id (f: triangle_morphism T₁ T₂) : f.comp (triangle_morphism_id T₂) = f :=
begin
  unfold comp,
  unfold triangle_morphism_id,
  cases f,
  simp only [eq_self_iff_true, and_self, comp_id],
end

@[simp]
lemma comp_assoc (f: triangle_morphism T₁ T₂) (g: triangle_morphism T₂ T₃)
  (h: triangle_morphism T₃ T₄) : (f.comp g).comp h = f.comp (g.comp h) :=
begin
  unfold comp,
  simp only [eq_self_iff_true, assoc, and_self],
end

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
      simp,
      dsimp,
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
    simp,
  end }

end triangle_morphism

/--
Triangles with triangle morphisms form a category.
-/
instance triangle_category : category (triangle C) :=
{ hom   := λ A B, triangle_morphism A B,
  id    := λ A, triangle_morphism_id A,
  comp  := λ A B C f g, f.comp g }

/--
Rotating triangles gives an endofunctor on this category.
-/
def rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.rotate C,
  map := λ _ _ f, f.rotate,
  map_id' := begin
    intro T₁,
    change triangle_morphism.rotate (triangle_morphism_id T₁) =
    triangle_morphism_id (triangle.rotate C T₁),
    unfold triangle_morphism.rotate,
    dsimp,
    ext,
    { dsimp,
      refl,
    },
    {
      dsimp,
      refl,
    },
    {
      unfold triangle_morphism_id,
      dsimp,
      rw (shift C).functor.map_id,
      refl,
    }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.rotate,
    ext,
    {
      dsimp,
      refl,
    },
    {
      dsimp,
      refl,
    },
    {
      dsimp,
      change (shift C).functor.map (f.trimor1 ≫ g.trimor1) = ((shift C).functor.map f.trimor1) ≫ ((shift C).functor.map g.trimor1),
      rw (shift C).functor.map_comp,
    }
  end
}

def inv_rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.inv_rotate C,
  map := λ _ _ f, f.inv_rotate,
  map_id' := begin
    intro T₁,
    change triangle_morphism.inv_rotate (triangle_morphism_id T₁) =
    triangle_morphism_id (triangle.inv_rotate C T₁),
    unfold triangle_morphism.inv_rotate,
    ext,
    {
      unfold triangle_morphism_id,
      dsimp,
      rw (shift C).inverse.map_id,
      refl,
    },
    {
      dsimp,
      refl,
    },
    {
      dsimp,
      refl,
    }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.inv_rotate,
    ext,
    {
      dsimp,
      change (shift C).inverse.map (f ≫ g).trimor3 =
      (shift C).inverse.map f.trimor3 ≫ (shift C).inverse.map g.trimor3,
      rw ← (shift C).inverse.map_comp,
      refl,
    },
    {
      dsimp,
      refl,
    },
    {
      dsimp,
      refl,
    },
  end
}

/--
Rotating triangles gives an auto-equivalence on the category of triangles.
-/
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{
  functor := rotate,
  inverse := inv_rotate,
  unit_iso := by sorry,
  counit_iso := by sorry,
}





end category_theory.triangulated
