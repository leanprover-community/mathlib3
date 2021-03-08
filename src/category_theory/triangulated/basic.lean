/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.limits.constructions.pullbacks
import category_theory.limits.shapes.biproducts
import category_theory.limits.shapes.images
import category_theory.abelian.non_preadditive
import category_theory.additive.basic
import category_theory.shift

/-!
# Triangulated Categories

This file contains the definition of triangulated categories.

TODO: generalise this to n-angulated categories as in https://arxiv.org/abs/1006.4592
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

variable {C}

/--
A morphism of triangles (X,Y,Z,f,g,h)→(X',Y',Z',f',g',h') in C is a triple of morphisms
a: X → X', b: Y → Y', c: Z → Z' such that b ≫ f = f' ≫ a, c ≫ g = g' ≫ b,
and Σa ≫ h = h' ≫ c.
In other words, we have a commutative diagram:
     f      g      h
  X  --> Y  --> Z  --> ΣX
  |      |      |       |
  |a     |b     |c      |Σa
  V      V      V       V
  X' --> Y' --> Z' --> ΣX'
     f'     g'     h'

See https://stacks.math.columbia.edu/tag/0144.
-/
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

variables {T₁ T₂ T₃ : triangle C}
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


end category_theory.triangulated
