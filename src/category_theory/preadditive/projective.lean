/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import algebra.homology.exact
import category_theory.types

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/--
An object `P` is called projective if every morphism out of `P` factors through every epimorphism.
-/
class projective (P : C) : Prop :=
(factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [epi e], ∃ f', f' ≫ e = f)

section

/--
A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
@[nolint has_inhabited_instance]
structure projective_presentation (X : C) :=
(P : C)
(projective : projective P . tactic.apply_instance)
(f : P ⟶ X)
(epi : epi f . tactic.apply_instance)

variables (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class enough_projectives : Prop :=
(presentation : ∀ (X : C), nonempty (projective_presentation X))

end

namespace projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
def factor_thru {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] : P ⟶ E :=
(projective.factors f e).some

@[simp] lemma factor_thru_comp {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] :
  factor_thru f e ≫ e = f :=
(projective.factors f e).some_spec

section
open_locale zero_object

instance zero_projective [has_zero_object C] [has_zero_morphisms C] : projective (0 : C) :=
{ factors := λ E X f e epi, by { use 0, ext, }}

end

lemma of_iso {P Q : C} (i : P ≅ Q) (hP : projective P) : projective Q :=
begin
  fsplit,
  introsI E X f e e_epi,
  obtain ⟨f', hf'⟩ := projective.factors (i.hom ≫ f) e,
  exact ⟨i.inv ≫ f', by simp [hf']⟩
end

lemma iso_iff {P Q : C} (i : P ≅ Q) : projective P ↔ projective Q :=
⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : projective X :=
{ factors := λ E X' f e epi,
  ⟨λ x, ((epi_iff_surjective _).mp epi (f x)).some,
  by { ext x, exact ((epi_iff_surjective _).mp epi (f x)).some_spec, }⟩ }

instance Type.enough_projectives : enough_projectives (Type u) :=
{ presentation := λ X, ⟨{ P := X, f := 𝟙 X, }⟩, }

instance {P Q : C} [has_binary_coproduct P Q] [projective P] [projective Q] :
  projective (P ⨿ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨coprod.desc (factor_thru (coprod.inl ≫ f) e) (factor_thru (coprod.inr ≫ f) e), by tidy⟩, }

instance {β : Type v} (g : β → C) [has_coproduct g] [∀ b, projective (g b)] :
  projective (∐ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨sigma.desc (λ b, factor_thru (sigma.ι g b ≫ f) e), by tidy⟩, }

instance {P Q : C} [has_zero_morphisms C] [has_binary_biproduct P Q]
  [projective P] [projective Q] :
  projective (P ⊞ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biprod.desc (factor_thru (biprod.inl ≫ f) e) (factor_thru (biprod.inr ≫ f) e), by tidy⟩, }

instance {β : Type v} [decidable_eq β] (g : β → C) [has_zero_morphisms C] [has_biproduct g]
  [∀ b, projective (g b)] : projective (⨁ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biproduct.desc (λ b, factor_thru (biproduct.ι g b ≫ f) e), by tidy⟩, }

section enough_projectives
variables [enough_projectives C]

/--
`projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `projective.π : projective.over X ⟶ X`.
-/
def over (X : C) : C :=
(enough_projectives.presentation X).some.P

instance projective_over (X : C) : projective (over X) :=
(enough_projectives.presentation X).some.projective

/--
The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
(enough_projectives.presentation X).some.f

instance π_epi (X : C) : epi (π X) :=
(enough_projectives.presentation X).some.epi

section
variables [has_zero_morphisms C] {X Y : C} (f : X ⟶ Y) [has_kernel f]

/--
When `C` has enough projectives, the object `projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/
@[derive projective]
def syzygies : C := over (kernel f)

/--
When `C` has enough projectives,
`projective.d f : projective.syzygies f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact (projective.d f) f`.)
-/
abbreviation d : syzygies f ⟶ X :=
π (kernel f) ≫ kernel.ι f

end

end enough_projectives

end projective

open projective

section
variables [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
Given a projective object `P` mapping via `h` into
the middle object `R` of a pair of exact morphisms `f : Q ⟶ R` and `g : R ⟶ S`,
such that `h ≫ g = 0`, there is a lift of `h` to `Q`.
-/
def exact.lift {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
  [exact f g] (w : h ≫ g = 0) : P ⟶ Q :=
factor_thru
  (factor_thru
    (factor_thru_kernel_subobject g h w)
    (image_to_kernel f g (by simp)))
  (factor_thru_image_subobject f)

@[simp] lemma exact.lift_comp {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
  [exact f g] (w : h ≫ g = 0) : exact.lift h f g w ≫ f = h :=
begin
  simp [exact.lift],
  conv_lhs { congr, skip, rw ← image_subobject_arrow_comp f, },
  rw [←category.assoc, factor_thru_comp, ←image_to_kernel_arrow,
    ←category.assoc, category_theory.projective.factor_thru_comp,
    factor_thru_kernel_subobject_comp_arrow],
end

end

end category_theory
