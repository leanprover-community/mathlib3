/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.exact

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/-- An object `P` is called projective if every morphism out of `P` factors through every
    equivalence. -/
def projective (P : C) : Prop :=
∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [epi e], ∃ f', f' ≫ e = f

section

structure projective_presentation (X : C) :=
(P : C)
(projective : projective P)
(f : P ⟶ X)
(epi : epi f)

variables (C)

/-- A category has enough projective if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class enough_projectives :=
(presentation : Π (X : C), projective_presentation X)
--∀ (X : C), ∃ (P : C) (f : P ⟶ X), projective P ∧ epi f

end

namespace projective

lemma of_iso {P Q : C} (i : P ≅ Q) (hP : projective P) : projective Q :=
begin
  introsI E X f e e_epi,
  rcases hP (i.hom ≫ f) e with ⟨f', hf'⟩,
  exact ⟨i.inv ≫ f', by simp [hf']⟩
end

lemma iso_iff {P Q : C} (i : P ≅ Q) : projective P ↔ projective Q :=
⟨of_iso i, of_iso i.symm⟩

section enough_projectives
variables [enough_projectives C]

def over (X : C) : C :=
(enough_projectives.presentation X).P

lemma projective_over (X : C) : projective (over X) :=
(enough_projectives.presentation X).projective

def π (X : C) : over X ⟶ X :=
(enough_projectives.presentation X).f

instance (X : C) : epi (π X) :=
(enough_projectives.presentation X).epi

variables [abelian C]

def left {X Y : C} (f : X ⟶ Y) : C := over (kernel f)

lemma projective_left {X Y : C} (f : X ⟶ Y) : projective (left f) :=
by apply projective_over

abbreviation d {X Y : C} (f : X ⟶ Y) : left f ⟶ X :=
π (kernel f) ≫ kernel.ι f

lemma exact_d_f {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

end enough_projectives

end projective


end category_theory
