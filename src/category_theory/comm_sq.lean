/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import category_theory.arrow

/-!
# Commutative squares

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
⟨by simp only [← op_comp, p.w]⟩

/-- The commutative square associated to a commutative square in the opposite category. -/
lemma unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
  (p : comm_sq f g h i) : comm_sq i.unop h.unop g.unop f.unop :=
⟨by simp only [← unop_comp, p.w]⟩

end comm_sq

namespace functor

variables {D : Type*} [category D]
variables (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

lemma map_comm_sq (s : comm_sq f g h i) : comm_sq (F.map f) (F.map g) (F.map h) (F.map i) :=
⟨by simpa using congr_arg (λ k : W ⟶ Z, F.map k) s.w⟩

end functor

alias functor.map_comm_sq ← comm_sq.map

namespace comm_sq

variables {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}

/-- The datum of a lift in a commutative square, i.e. a up-right-diagonal
morphism which makes both triangles commute. -/
@[ext, nolint has_nonempty_instance]
structure lift_struct (sq : comm_sq f i p g) :=
(l : B ⟶ X) (fac_left' : i ≫ l = f) (fac_right' : l ≫ p = g)

namespace lift_struct

restate_axiom fac_left'
restate_axiom fac_right'

/-- A `lift_struct` for a commutative square gives a `lift_struct` for the
corresponding square in the opposite category. -/
@[simps]
def op {sq : comm_sq f i p g} (l : lift_struct sq) : lift_struct sq.op :=
{ l := l.l.op,
  fac_left' := by rw [← op_comp, l.fac_right],
  fac_right' := by rw [← op_comp, l.fac_left], }

/-- A `lift_struct` for a commutative square in the opposite category
gives a `lift_struct` for the corresponding square in the original category. -/
@[simps]
def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : comm_sq f i p g}
  (l : lift_struct sq) : lift_struct sq.unop :=
{ l := l.l.unop,
  fac_left' := by rw [← unop_comp, l.fac_right],
  fac_right' := by rw [← unop_comp, l.fac_left], }

/-- Equivalences of `lift_struct` for a square and the corresponding square
in the opposite category. -/
@[simps]
def op_equiv (sq : comm_sq f i p g) : lift_struct sq ≃ lift_struct sq.op :=
{ to_fun := op,
  inv_fun := unop,
  left_inv := by tidy,
  right_inv := by tidy, }

/-- Equivalences of `lift_struct` for a square in the oppositive category and
the corresponding square in the original category. -/
def unop_equiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  (sq : comm_sq f i p g) : lift_struct sq ≃ lift_struct sq.unop :=
{ to_fun := unop,
  inv_fun := op,
  left_inv := by tidy,
  right_inv := by tidy, }

end lift_struct

instance subsingleton_lift_struct_of_epi (sq : comm_sq f i p g) [epi i] :
  subsingleton (lift_struct sq) :=
⟨λ l₁ l₂, by { ext, simp only [← cancel_epi i, lift_struct.fac_left], }⟩

instance subsingleton_lift_struct_of_mono (sq : comm_sq f i p g) [mono p] :
  subsingleton (lift_struct sq) :=
⟨λ l₁ l₂, by { ext, simp only [← cancel_mono p, lift_struct.fac_right], }⟩

variable (sq : comm_sq f i p g)

/-- The assertion that a square has a `lift_struct`. -/
class has_lift : Prop := (exists_lift : nonempty sq.lift_struct)

namespace has_lift

variable {sq}

lemma mk' (l : sq.lift_struct) : has_lift sq := ⟨nonempty.intro l⟩

variable (sq)

lemma iff : has_lift sq ↔ nonempty sq.lift_struct :=
by { split, exacts [λ h, h.exists_lift, λ h, mk h], }

lemma iff_op : has_lift sq ↔ has_lift sq.op :=
begin
  rw [iff, iff],
  exact nonempty.congr (lift_struct.op_equiv sq).to_fun (lift_struct.op_equiv sq).inv_fun,
end

lemma iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  (sq : comm_sq f i p g) : has_lift sq ↔ has_lift sq.unop :=
begin
  rw [iff, iff],
  exact nonempty.congr (lift_struct.unop_equiv sq).to_fun (lift_struct.unop_equiv sq).inv_fun,
end

end has_lift

/-- A choice of a diagonal morphism that is part of a `lift_struct` when
the square has a lift. -/
noncomputable
def lift [hsq : has_lift sq] : B ⟶ X :=
hsq.exists_lift.some.l

@[simp, reassoc]
lemma fac_left [hsq : has_lift sq] : i ≫ sq.lift = f :=
hsq.exists_lift.some.fac_left

@[simp, reassoc]
lemma fac_right [hsq : has_lift sq] : sq.lift ≫ p = g :=
hsq.exists_lift.some.fac_right

end comm_sq

end category_theory
