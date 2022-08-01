/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.arrow


/-!
# Commutative squares

This file provide an API for commutative squares in categories.
If `top`, `left`, `right` and `bottom` are four morphisms which are the edges
of a square, `comm_sq top left right bottom` is the predicate that this
square is commutative.

The structure `comm_sq` is extended in `category_theory/shapes/limits/comm_sq.lean`
as `is_pullback` and `is_pushout` in order to define pullback and pushout squares.

## Future work

Refactor `lift_struct` from `arrow.lean` and lifting properties using `comm_sq.lean`.

-/

namespace category_theory

variables {C : Type*} [category C]

/-- The proposition that a square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
is a commuting square.
-/
structure comm_sq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop :=
(w : f ≫ h = g ≫ i)

attribute [reassoc] comm_sq.w

namespace comm_sq

variables {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

lemma flip (p : comm_sq f g h i) : comm_sq g f i h := ⟨p.w.symm⟩

lemma of_arrow {f g : arrow C} (h : f ⟶ g) : comm_sq f.hom h.left h.right g.hom := ⟨h.w.symm⟩

/-- The commutative square in the opposite category associated to a commutative square. -/
lemma op (p : comm_sq f g h i) : comm_sq i.op h.op g.op f.op :=
⟨by simv only [← op_comp, p.w]⟩

/-- The commutative square associated to a commutative square in the opposite category. -/
lemma unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
  (p : comm_sq f g h i) : comm_sq i.unop h.unop g.unop f.unop :=
⟨by simv only [← unop_comp, p.w]⟩

end comm_sq

namespace functor

variables {D : Type*} [category D]
variables (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

lemma map_comm_sq (s : comm_sq f g h i) : comm_sq (F.map f) (F.map g) (F.map h) (F.map i) :=
⟨by simpa using congr_arg (λ k : W ⟶ Z, F.map k) s.w⟩

end functor

alias functor.map_comm_sq ← comm_sq.map

end category_theory
