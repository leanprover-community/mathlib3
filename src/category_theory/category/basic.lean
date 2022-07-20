/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import combinatorics.quiver.basic
import tactic.basic

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

/--
The typeclass `category C` describes morphisms associated to objects of type `C : Type u`.

The universe levels of the objects and morphisms are independent, and will often need to be
specified explicitly, as `category.{v} C`.

Typically any concrete example will either be a `small_category`, where `v = u`,
which can be introduced as
```
universes u
variables {C : Type u} [small_category C]
```
or a `large_category`, where `u = v+1`, which can be introduced as
```
universes u
variables {C : Type (u+1)} [large_category C]
```

In order for the library to handle these cases uniformly,
we generally work with the unconstrained `category.{v u}`,
for which objects live in `Type u` and morphisms live in `Type v`.

Because the universe parameter `u` for the objects can be inferred from `C`
when we write `category C`, while the universe parameter `v` for the morphisms
can not be automatically inferred, through the category theory library
we introduce universe parameters with morphism levels listed first,
as in
```
universes v u
```
or
```
universes v₁ v₂ u₁ u₂
```
when multiple independent universes are needed.

This has the effect that we can simply write `category.{v} C`
(that is, only specifying a single parameter) while `u` will be inferred.

Often, however, it's not even necessary to include the `.{v}`.
(Although it was in earlier versions of Lean.)
If it is omitted a "free" universe will be used.
-/
library_note "category_theory universes"

universes v u

namespace category_theory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
class category_struct (obj : Type u)
extends quiver.{v+1} obj : Type (max u (v+1)) :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation `𝟙` := category_struct.id -- type as \b1
infixr ` ≫ `:80 := category_struct.comp -- type as \gg

/--
The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{v} C`. (See also `large_category` and `small_category`.)

See <https://stacks.math.columbia.edu/tag/0014>.
-/
class category (obj : Type u)
extends category_struct.{v} obj : Type (max u (v+1)) :=
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

initialize_simps_projections category (to_category_struct_to_quiver_hom → hom,
  to_category_struct_comp → comp, to_category_struct_id → id, -to_category_struct)

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

lemma comp_ite {P : Prop} [decidable P]
  {X Y Z : C} (f : X ⟶ Y) (g g' : (Y ⟶ Z)) :
  (f ≫ if P then g else g') = (if P then f ≫ g else f ≫ g') :=
by { split_ifs; refl }

lemma ite_comp {P : Prop} [decidable P]
  {X Y Z : C} (f f' : (X ⟶ Y))  (g : Y ⟶ Z) :
  (if P then f else f') ≫ g = (if P then f ≫ g else f' ≫ g) :=
by { split_ifs; refl }

lemma comp_dite {P : Prop} [decidable P]
  {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
  (f ≫ if h : P then g h else g' h) = (if h : P then f ≫ g h else f ≫ g' h) :=
by { split_ifs; refl }

lemma dite_comp {P : Prop} [decidable P]
  {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
  (if h : P then f h else f' h) ≫ g = (if h : P then f h ≫ g else f' h ≫ g) :=
by { split_ifs; refl }

/--
A morphism `f` is an epimorphism if it can be "cancelled" when precomposed:
`f ≫ g = f ≫ h` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class epi (f : X ⟶ Y) : Prop :=
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)

/--
A morphism `f` is a monomorphism if it can be "cancelled" when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class mono (f : X ⟶ Y) : Prop :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance (X : C) : epi (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩
instance (X : C) : mono (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩

lemma cancel_epi (f : X ⟶ Y) [epi f] {g h : Y ⟶ Z} : (f ≫ g = f ≫ h) ↔ g = h :=
⟨λ p, epi.left_cancellation g h p, congr_arg _⟩
lemma cancel_mono (f : X ⟶ Y) [mono f] {g h : Z ⟶ X} : (g ≫ f = h ≫ f) ↔ g = h :=
⟨λ p, mono.right_cancellation g h p, congr_arg _⟩

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

/--
Many proofs in the category theory library use the `dsimp, simp` pattern,
which typically isn't necessary elsewhere.

One would usually hope that the same effect could be achieved simply with `simp`.

The essential issue is that composition of morphisms involves dependent types.
When you have a chain of morphisms being composed, say `f : X ⟶ Y` and `g : Y ⟶ Z`,
then `simp` can operate succesfully on the morphisms
(e.g. if `f` is the identity it can strip that off).

However if we have an equality of objects, say `Y = Y'`,
then `simp` can't operate because it would break the typing of the composition operations.
We rarely have interesting equalities of objects
(because that would be "evil" --- anything interesting should be expressed as an isomorphism
and tracked explicitly),
except of course that we have plenty of definitional equalities of objects.

`dsimp` can apply these safely, even inside a composition.

After `dsimp` has cleared up the object level, `simp` can resume work on the morphism level ---
but without the `dsimp` step, because `simp` looks at expressions syntactically,
the relevant lemmas might not fire.

There's no bound on how many times you potentially could have to switch back and forth,
if the `simp` introduced new objects we again need to `dsimp`.
In practice this does occur, but only rarely, because `simp` tends to shorten chains of compositions
(i.e. not introduce new objects at all).
-/
library_note "dsimp, simp"
