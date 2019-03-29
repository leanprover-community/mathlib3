/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton

Defines a category, as a typeclass parametrised by the type of objects.
Introduces notations
  `X ⟶ Y` for the morphism spaces,
  `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/

import tactic.restate_axiom
import tactic.replacer
import tactic.interactive
import tactic.tidy

namespace category_theory

universes v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

/-
The propositional fields of `category` are annotated with the auto_param `obviously`,
which is defined here as a
[`replacer` tactic](https://github.com/leanprover/mathlib/blob/master/docs/tactics.md#def_replacer).
We then immediately set up `obviously` to call `tidy`. Later, this can be replaced with more
powerful tactics.
-/
def_replacer obviously
@[obviously] meta def obviously' := tactic.tidy

class has_hom (obj : Sort u) : Sort (max u (v+1)) :=
(hom : obj → obj → Sort v)

infixr ` ⟶ `:10 := has_hom.hom -- type as \h

class category_struct (obj : Sort u)
extends has_hom.{v} obj : Sort (max u (v+1)) :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation `𝟙` := category_struct.id -- type as \b1
infixr ` ≫ `:80 := category_struct.comp -- type as \gg

/--
The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{v} C`. (See also `large_category` and `small_category`.)
-/
class category (obj : Sort u)
extends category_struct.{v} obj : Sort (max u (v+1)) :=
(id_comp' : ∀ {X Y : obj} (f : hom X Y), 𝟙 X ≫ f = f . obviously)
(comp_id' : ∀ {X Y : obj} (f : hom X Y), f ≫ 𝟙 Y = f . obviously)
(assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  (f ≫ g) ≫ h = f ≫ (g ≫ h) . obviously)

-- `restate_axiom` is a command that creates a lemma from a structure field,
-- discarding any auto_param wrappers from the type.
-- (It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".)
restate_axiom category.id_comp'
restate_axiom category.comp_id'
restate_axiom category.assoc'
attribute [simp] category.id_comp category.comp_id category.assoc
attribute [trans] category_struct.comp

lemma category.assoc_symm {C : Type u} [category.{v} C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
  f ≫ (g ≫ h) = (f ≫ g) ≫ h :=
by rw ←category.assoc

/--
A `large_category` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbreviation large_category (C : Sort (u+1)) : Sort (u+1) := category.{u} C
/--
A `small_category` has objects and morphisms in the same universe level.
-/
abbreviation small_category (C : Sort u)     : Sort (u+1) := category.{u} C

section
variables {C : Sort u} [𝒞 : category.{v} C] {X Y Z : C}
include 𝒞

class epi  (f : X ⟶ Y) : Prop :=
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class mono (f : X ⟶ Y) : Prop :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

@[simp] lemma cancel_epi  (f : X ⟶ Y) [epi f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h :=
⟨ λ p, epi.left_cancellation g h p, begin intro a, subst a end ⟩
@[simp] lemma cancel_mono (f : X ⟶ Y) [mono f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h :=
⟨ λ p, mono.right_cancellation g h p, begin intro a, subst a end ⟩
end

section
variable (C : Type u)
variable [category.{v} C]

universe u'

instance ulift_category : category.{v} (ulift.{u'} C) :=
{ hom  := λ X Y, (X.down ⟶ Y.down),
  id   := λ X, 𝟙 X.down,
  comp := λ _ _ _ f g, f ≫ g }

-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [small_category D] : large_category (ulift.{u+1} D) := by apply_instance
end

variables (α : Type u)

instance [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans f.down.down g.down.down ⟩ ⟩ }

section
variables {C : Type u}

def End [has_hom.{v} C] (X : C) := X ⟶ X

instance End.has_one [category_struct.{v+1} C] {X : C} : has_one (End X) := by refine { one := 𝟙 X }
instance End.has_mul [category_struct.{v+1} C] {X : C} : has_mul (End X) := by refine { mul := λ x y, x ≫ y }
instance End.monoid [category.{v+1} C] {X : C} : monoid (End X) :=
by refine { .. End.has_one, .. End.has_mul, .. }; dsimp [has_mul.mul,has_one.one]; obviously

@[simp] lemma End.one_def {C : Type u} [category_struct.{v+1} C] {X : C} : (1 : End X) = 𝟙 X := rfl

@[simp] lemma End.mul_def {C : Type u} [category_struct.{v+1} C] {X : C} (xs ys : End X) : xs * ys = xs ≫ ys := rfl

end

end category_theory
