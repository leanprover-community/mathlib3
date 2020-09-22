/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.basic

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/-- An object `P` is called projective if every morphism out of `P` factors through every
    equivalence. -/
def projective (P : C) : Prop :=
∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [epi e], ∃ f', f' ≫ e = f

section
variables (C)

/-- A category has enough projective if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
@[class] def enough_projectives : Prop :=
∀ (X : C), ∃ (P : C) (f : P ⟶ X), projective P ∧ epi f

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

end projective



end category_theory
