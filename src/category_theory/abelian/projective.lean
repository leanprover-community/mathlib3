/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.exact

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
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
structure projective_presentation (X : C) :=
(P : C)
(projective : projective P)
(f : P ⟶ X)
(epi : epi f)

variables (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class enough_projectives : Prop :=
(presentation : ∀ (X : C), nonempty (projective_presentation X))

end

namespace projective

lemma of_iso {P Q : C} (i : P ≅ Q) (hP : projective P) : projective Q :=
begin
  fsplit,
  introsI E X f e e_epi,
  obtain ⟨f', hf'⟩ := projective.factors (i.hom ≫ f) e,
  exact ⟨i.inv ≫ f', by simp [hf']⟩
end

lemma iso_iff {P Q : C} (i : P ≅ Q) : projective P ↔ projective Q :=
⟨of_iso i, of_iso i.symm⟩

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

instance (X : C) : epi (π X) :=
(enough_projectives.presentation X).some.epi

section
variables [has_zero_morphisms C] {X Y : C} (f : X ⟶ Y) [has_kernel f]

/-- When `C` has enough projectives, the object `projective.left f` is
the arbitrarily chosen projective object over `kernel f`. -/
@[derive projective]
def left : C := over (kernel f)

/-- When `C` has enough projectives,
`projective.d f : projective.left f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.
-/
abbreviation d : left f ⟶ X :=
π (kernel f) ≫ kernel.ι f

end

variables [abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
lemma exact_d_f {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

end enough_projectives

end projective

end category_theory
