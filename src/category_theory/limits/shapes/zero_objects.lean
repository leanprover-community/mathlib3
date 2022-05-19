/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import category_theory.limits.shapes.products
import category_theory.limits.shapes.images
import category_theory.isomorphism_classes

/-!
# Zero objects

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object;
see `category_theory.limits.shapes.zero_morphisms`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

noncomputable theory

universes v u v' u'

open category_theory
open category_theory.category

variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v'} D]

namespace category_theory

namespace limits

/-- An object `X` in a category is a *zero object* if for every object `Y`
there is a unique morphism `to : X → Y` and a unique morphism `from : Y → X`.

This is a characteristic predicate for `has_zero_object`. -/
structure is_zero (X : C) : Prop :=
(unique_to   : ∀ Y, nonempty (unique (X ⟶ Y)))
(unique_from : ∀ Y, nonempty (unique (Y ⟶ X)))

namespace is_zero

variables {X Y : C}

/-- If `h : is_zero X`, then `h.to Y` is a choice of unique morphism `X → Y`. -/
protected def «to» (h : is_zero X) (Y : C) : X ⟶ Y :=
@default (X ⟶ Y) $ @unique.inhabited _ $ (h.unique_to Y).some

lemma eq_to (h : is_zero X) (f : X ⟶ Y) : f = h.to Y :=
@unique.eq_default _ (id _) _

lemma to_eq (h : is_zero X) (f : X ⟶ Y) : h.to Y = f :=
(h.eq_to f).symm

/-- If `h : is_zero X`, then `h.from Y` is a choice of unique morphism `Y → X`. -/
protected def «from» (h : is_zero X) (Y : C) : Y ⟶ X :=
@default (Y ⟶ X) $ @unique.inhabited _ $ (h.unique_from Y).some

lemma eq_from (h : is_zero X) (f : Y ⟶ X) : f = h.from Y :=
@unique.eq_default _ (id _) _

lemma from_eq (h : is_zero X) (f : Y ⟶ X) : h.from Y = f :=
(h.eq_from f).symm

lemma eq_of_src (hX : is_zero X) (f g : X ⟶ Y) : f = g :=
(hX.eq_to f).trans (hX.eq_to g).symm

lemma eq_of_tgt (hX : is_zero X) (f g : Y ⟶ X) : f = g :=
(hX.eq_from f).trans (hX.eq_from g).symm

/-- Any two zero objects are isomorphic. -/
def iso (hX : is_zero X) (hY : is_zero Y) : X ≅ Y :=
{ hom := hX.to Y,
  inv := hX.from Y,
  hom_inv_id' := hX.eq_of_src _ _,
  inv_hom_id' := hY.eq_of_src _ _, }

/-- A zero object is in particular initial. -/
protected def is_initial (hX : is_zero X) : is_initial X :=
@is_initial.of_unique _ _ X $ λ Y, (hX.unique_to Y).some

/-- A zero object is in particular terminal. -/
protected def is_terminal (hX : is_zero X) : is_terminal X :=
@is_terminal.of_unique _ _ X $ λ Y, (hX.unique_from Y).some

/-- The (unique) isomorphism between any initial object and the zero object. -/
def iso_is_initial (hX : is_zero X) (hY : is_initial Y) : X ≅ Y :=
hX.is_initial.unique_up_to_iso hY

/-- The (unique) isomorphism between any terminal object and the zero object. -/
def iso_is_terminal (hX : is_zero X) (hY : is_terminal Y) : X ≅ Y :=
hX.is_terminal.unique_up_to_iso hY

lemma of_iso (hY : is_zero Y) (e : X ≅ Y) : is_zero X :=
begin
  refine ⟨λ Z, ⟨⟨⟨e.hom ≫ hY.to Z⟩, λ f, _⟩⟩, λ Z, ⟨⟨⟨hY.from Z ≫ e.inv⟩, λ f, _⟩⟩⟩,
  { rw ← cancel_epi e.inv, apply hY.eq_of_src, },
  { rw ← cancel_mono e.hom, apply hY.eq_of_tgt, },
end

end is_zero

end limits

open category_theory.limits

lemma iso.is_zero_iff {X Y : C} (e : X ≅ Y) :
  is_zero X ↔ is_zero Y :=
⟨λ h, h.of_iso e.symm, λ h, h.of_iso e⟩

lemma functor.is_zero (F : C ⥤ D) (hF : ∀ X, is_zero (F.obj X)) :
  is_zero F :=
begin
  split; intros G; refine ⟨⟨⟨_⟩, _⟩⟩,
  { refine { app := λ X, (hF _).to _, naturality' := _ },
    intros, exact (hF _).eq_of_src _ _ },
  { intro f, ext, apply (hF _).eq_of_src _ _ },
  { refine { app := λ X, (hF _).from _, naturality' := _ },
    intros, exact (hF _).eq_of_tgt _ _ },
  { intro f, ext, apply (hF _).eq_of_tgt _ _ },
end

namespace limits

variables (C)

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class has_zero_object : Prop :=
(zero : ∃ X : C, is_zero X)

instance has_zero_object_punit : has_zero_object (discrete punit) :=
{ zero := ⟨punit.star, by tidy, by tidy⟩, }

section

variables [has_zero_object C]

/--
Construct a `has_zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `has_zero C` typeclass search.
-/
protected def has_zero_object.has_zero : has_zero C :=
{ zero := has_zero_object.zero.some }

localized "attribute [instance] category_theory.limits.has_zero_object.has_zero" in zero_object

lemma is_zero_zero : is_zero (0 : C) :=
has_zero_object.zero.some_spec

end

open_locale zero_object

variables {C}

lemma is_zero.has_zero_object {X : C} (hX : is_zero X) : has_zero_object C := ⟨⟨X, hX⟩⟩

/-- Every zero object is isomorphic to *the* zero object. -/
def is_zero.iso_zero [has_zero_object C] {X : C} (hX : is_zero X) : X ≅ 0 :=
hX.iso (is_zero_zero C)

lemma is_zero.obj [has_zero_object D] {F : C ⥤ D} (hF : is_zero F) (X : C) :
  is_zero (F.obj X) :=
begin
  let G : C ⥤ D := (category_theory.functor.const C).obj 0,
  have hG : is_zero G := functor.is_zero _ (λ X, is_zero_zero _),
  let e : F ≅ G := hF.iso hG,
  exact (is_zero_zero _).of_iso (e.app X),
end

namespace has_zero_object
variables [has_zero_object C]

/-- There is a unique morphism from the zero object to any object `X`. -/
protected def unique_to (X : C) : unique (0 ⟶ X) :=
((is_zero_zero C).unique_to X).some

/-- There is a unique morphism from any object `X` to the zero object. -/
protected def unique_from (X : C) : unique (X ⟶ 0) :=
((is_zero_zero C).unique_from X).some

localized "attribute [instance] category_theory.limits.has_zero_object.unique_to" in zero_object
localized "attribute [instance] category_theory.limits.has_zero_object.unique_from" in zero_object

@[ext]
lemma to_zero_ext {X : C} (f g : X ⟶ 0) : f = g :=
(is_zero_zero C).eq_of_tgt _ _

@[ext]
lemma from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g :=
(is_zero_zero C).eq_of_src _ _

instance (X : C) : subsingleton (X ≅ 0) := by tidy

instance {X : C} (f : 0 ⟶ X) : mono f :=
{ right_cancellation := λ Z g h w, by ext, }

instance {X : C} (f : X ⟶ 0) : epi f :=
{ left_cancellation := λ Z g h w, by ext, }

instance zero_to_zero_is_iso (f : (0 : C) ⟶ 0) :
  is_iso f :=
by convert (show is_iso (𝟙 (0 : C)), by apply_instance)

/-- A zero object is in particular initial. -/
def zero_is_initial : is_initial (0 : C) :=
(is_zero_zero C).is_initial

/-- A zero object is in particular terminal. -/
def zero_is_terminal : is_terminal (0 : C) :=
(is_zero_zero C).is_terminal

/-- A zero object is in particular initial. -/
@[priority 10]
instance has_initial : has_initial C :=
has_initial_of_unique 0

/-- A zero object is in particular terminal. -/
@[priority 10]
instance has_terminal : has_terminal C :=
has_terminal_of_unique 0

/-- The (unique) isomorphism between any initial object and the zero object. -/
def zero_iso_is_initial {X : C} (t : is_initial X) : 0 ≅ X :=
zero_is_initial.unique_up_to_iso t

/-- The (unique) isomorphism between any terminal object and the zero object. -/
def zero_iso_is_terminal {X : C} (t : is_terminal X) : 0 ≅ X :=
zero_is_terminal.unique_up_to_iso t

/-- The (unique) isomorphism between the chosen initial object and the chosen zero object. -/
def zero_iso_initial [has_initial C] : 0 ≅ ⊥_ C :=
zero_is_initial.unique_up_to_iso initial_is_initial

/-- The (unique) isomorphism between the chosen terminal object and the chosen zero object. -/
def zero_iso_terminal [has_terminal C] : 0 ≅ ⊤_ C :=
zero_is_terminal.unique_up_to_iso terminal_is_terminal

@[priority 100]
instance has_strict_initial : initial_mono_class C :=
initial_mono_class.of_is_initial zero_is_initial (λ X, category_theory.mono _)

end has_zero_object

end limits

open category_theory.limits
open_locale zero_object

lemma functor.is_zero_iff [has_zero_object D] (F : C ⥤ D) :
  is_zero F ↔ ∀ X, is_zero (F.obj X) :=
⟨λ hF X, hF.obj X, functor.is_zero _⟩

end category_theory
