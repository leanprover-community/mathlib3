/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import tactic.basic
import tactic.tidy

/-!
# Categories

Defines a category, as a type class parametrised by the type of objects.

## Notations

Introduces notations
* `X ⟶ Y` for the morphism spaces,
* `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```lean
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/

-- The order in this declaration matters: v often needs to be explicitly specified while u often
-- can be omitted
universes v u

namespace category_theory

/-
The propositional fields of `category` are annotated with the auto_param `obviously`,
which is defined here as a
[`replacer` tactic](https://leanprover-community.github.io/mathlib_docs/commands.html#def_replacer).
We then immediately set up `obviously` to call `tidy`. Later, this can be replaced with more
powerful tactics.
-/
def_replacer obviously
@[obviously] meta def obviously' := tactic.tidy

class has_hom (obj : Type u) : Type (max u (v+1)) :=
(hom : obj → obj → Type v)

infixr ` ⟶ `:10 := has_hom.hom -- type as \h

section prio
set_option default_priority 100 -- see Note [default priority]
class category_struct (obj : Type u)
extends has_hom.{v} obj : Type (max u (v+1)) :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation `𝟙` := category_struct.id -- type as \b1
infixr ` ≫ `:80 := category_struct.comp -- type as \gg

/--
The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{v} C`. (See also `large_category` and `small_category`.)
-/
class category (obj : Type u)
extends category_struct.{v} obj : Type (max u (v+1)) :=
(id_comp' : ∀ {X Y : obj} (f : hom X Y), 𝟙 X ≫ f = f . obviously)
(comp_id' : ∀ {X Y : obj} (f : hom X Y), f ≫ 𝟙 Y = f . obviously)
(assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  (f ≫ g) ≫ h = f ≫ (g ≫ h) . obviously)
end prio

-- `restate_axiom` is a command that creates a lemma from a structure field,
-- discarding any auto_param wrappers from the type.
-- (It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".)
restate_axiom category.id_comp'
restate_axiom category.comp_id'
restate_axiom category.assoc'
attribute [simp] category.id_comp category.comp_id category.assoc
attribute [trans] category_struct.comp

/--
A `large_category` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbreviation large_category (C : Type (u+1)) : Type (u+1) := category.{u} C
/--
A `small_category` has objects and morphisms in the same universe level.
-/
abbreviation small_category (C : Type u) : Type (u+1) := category.{u} C

section
variables {C : Type u} [category.{v} C] {X Y Z : C}

/-- postcompose an equation between morphisms by another morphism -/
lemma eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h :=
by rw w
/-- precompose an equation between morphisms by another morphism -/
lemma whisker_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h :=
by rw w

infixr ` =≫ `:80 := eq_whisker
infixr ` ≫= `:80 := whisker_eq

lemma eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g :=
by { convert w (𝟙 Y), tidy }
lemma eq_of_comp_right_eq {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g :=
by { convert w (𝟙 Y), tidy }

lemma eq_of_comp_left_eq' (f g : X ⟶ Y)
  (w : (λ {Z : C} (h : Y ⟶ Z), f ≫ h) = (λ {Z : C} (h : Y ⟶ Z), g ≫ h)) : f = g :=
eq_of_comp_left_eq (λ Z h, by convert congr_fun (congr_fun w Z) h)
lemma eq_of_comp_right_eq' (f g : Y ⟶ Z)
  (w : (λ {X : C} (h : X ⟶ Y), h ≫ f) = (λ {X : C} (h : X ⟶ Y), h ≫ g)) : f = g :=
eq_of_comp_right_eq (λ X h, by convert congr_fun (congr_fun w X) h)

lemma id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X :=
by { convert w (𝟙 X), tidy }
lemma id_of_comp_right_id (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X :=
by { convert w (𝟙 X), tidy }

lemma comp_dite {P : Prop} [decidable P]
  {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
  (f ≫ if h : P then g h else g' h) = (if h : P then f ≫ g h else f ≫ g' h) :=
by { split_ifs; refl }

lemma dite_comp {P : Prop} [decidable P]
  {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
  (if h : P then f h else f' h) ≫ g = (if h : P then f h ≫ g else f' h ≫ g) :=
by { split_ifs; refl }

class epi  (f : X ⟶ Y) : Prop :=
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class mono (f : X ⟶ Y) : Prop :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance (X : C) : epi (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩
instance (X : C) : mono (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩

lemma cancel_epi (f : X ⟶ Y) [epi f]  {g h : Y ⟶ Z} : (f ≫ g = f ≫ h) ↔ g = h :=
⟨ λ p, epi.left_cancellation g h p, begin intro a, subst a end ⟩
lemma cancel_mono (f : X ⟶ Y) [mono f] {g h : Z ⟶ X} : (g ≫ f = h ≫ f) ↔ g = h :=
⟨ λ p, mono.right_cancellation g h p, begin intro a, subst a end ⟩

lemma cancel_epi_id (f : X ⟶ Y) [epi f] {h : Y ⟶ Y} : (f ≫ h = f) ↔ h = 𝟙 Y :=
by { convert cancel_epi f, simp, }
lemma cancel_mono_id (f : X ⟶ Y) [mono f] {g : X ⟶ X} : (g ≫ f = f) ↔ g = 𝟙 X :=
by { convert cancel_mono f, simp, }

lemma epi_comp {X Y Z : C} (f : X ⟶ Y) [epi f] (g : Y ⟶ Z) [epi g] : epi (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_epi g).1,
  apply (cancel_epi f).1,
  simpa using w,
end
lemma mono_comp {X Y Z : C} (f : X ⟶ Y) [mono f] (g : Y ⟶ Z) [mono g] : mono (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_mono f).1,
  apply (cancel_mono g).1,
  simpa using w,
end

lemma mono_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono (f ≫ g)] : mono f :=
begin
  split, intros Z a b w,
  replace w := congr_arg (λ k, k ≫ g) w,
  dsimp at w,
  rw [category.assoc, category.assoc] at w,
  exact (cancel_mono _).1 w,
end

lemma mono_of_mono_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [mono h] (w : f ≫ g = h) :
  mono f :=
by { substI h, exact mono_of_mono f g, }

lemma epi_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [epi (f ≫ g)] : epi g :=
begin
  split, intros Z a b w,
  replace w := congr_arg (λ k, f ≫ k) w,
  dsimp at w,
  rw [←category.assoc, ←category.assoc] at w,
  exact (cancel_epi _).1 w,
end

lemma epi_of_epi_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [epi h] (w : f ≫ g = h) :
  epi g :=
by substI h; exact epi_of_epi f g
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

end category_theory

open category_theory

namespace preorder

variables (α : Type u)

@[priority 100] -- see Note [lower instance priority]
instance small_category [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans _ _ _ f.down.down g.down.down ⟩ ⟩ }

end preorder
