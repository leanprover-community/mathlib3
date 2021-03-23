/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.additive.basic
import category_theory.shift
import category_theory.abelian.additive_functor

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
variables (C : Type u) [category.{v} C] [additive_category C]
variables [has_shift C] [functor.additive (shift C).functor]

/--
A triangle in C is a sextuple (X,Y,Z,f,g,h) where X,Y,Z are objects of C,
and f : X ⟶ Y, g : Y ⟶ Z, h : Z ⟶ X⟦1⟧ are morphisms in C.
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
⟨⟨0,0,0,0,0,0⟩⟩

variable {C}

/--
A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple of morphisms
`a : X ⟶ X'`, `b : Y ⟶ Y'`, `c : Z ⟶ Z'` such that
`b ≫ f = f' ≫ a`, `c ≫ g = g' ≫ b`, and `a⟦1⟧' ≫ h = h' ≫ c`.
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
@[ext]
structure triangle_morphism (T₁ : triangle C) (T₂ : triangle C) :=
(trimor1 : T₁.obj1 ⟶ T₂.obj1)
(trimor2 : T₁.obj2 ⟶ T₂.obj2)
(trimor3 : T₁.obj3 ⟶ T₂.obj3)
(comm1' : T₁.mor1 ≫ trimor2 = trimor1 ≫ T₂.mor1 . obviously)
(comm2' : T₁.mor2 ≫ trimor3 = trimor2 ≫ T₂.mor2 . obviously)
(comm3' : T₁.mor3 ≫ trimor1⟦1⟧' = trimor3 ≫ T₂.mor3 . obviously)

restate_axiom triangle_morphism.comm1'
restate_axiom triangle_morphism.comm2'
restate_axiom triangle_morphism.comm3'
attribute [simp, reassoc] triangle_morphism.comm1 triangle_morphism.comm2 triangle_morphism.comm3

/--
The identity triangle morphism.
-/
@[simps]
def triangle_morphism_id (T : triangle C) : triangle_morphism T T :=
{ trimor1 := 𝟙 T.obj1,
  trimor2 := 𝟙 T.obj2,
  trimor3 := 𝟙 T.obj3, }

instance (T : triangle C) : inhabited (triangle_morphism T T) := ⟨triangle_morphism_id T⟩

variables {T₁ T₂ T₃ : triangle C}

/--
Composition of triangle morphisms gives a triangle morphism.
-/
@[simps]
def triangle_morphism.comp (f : triangle_morphism T₁ T₂) (g : triangle_morphism T₂ T₃) :
  triangle_morphism T₁ T₃ :=
{ trimor1 := f.trimor1 ≫ g.trimor1,
  trimor2 := f.trimor2 ≫ g.trimor2,
  trimor3 := f.trimor3 ≫ g.trimor3, }

/--
Triangles with triangle morphisms form a category.
-/
@[simps]
instance triangle_category : category (triangle C) :=
{ hom   := λ A B, triangle_morphism A B,
  id    := λ A, triangle_morphism_id A,
  comp  := λ A B C f g, f.comp g, }

end category_theory.triangulated
