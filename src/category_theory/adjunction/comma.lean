/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction.basic
import category_theory.limits.constructions.weakly_initial
import category_theory.limits.preserves.basic
import category_theory.limits.creates
import category_theory.limits.comma
import category_theory.punit

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition (`category_theory/adjunction/limits` already shows it preserves limits).

We define the solution set condition for the functor `G : D ⥤ C` to mean, for every object `A : C`,
there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X` factors
through one of the `f_i`.

-/
universes v u₁ u₂

noncomputable theory

namespace category_theory
open limits

variables {C : Type u₁} {D : Type u₂} [category.{v} C] [category.{v} D] (G : D ⥤ C)

-- TODO: consider showing the converse
-- This section proves that if each comma category (A ↓ G) has an initial object then `G` has a
-- left adjoint

section of_initials
variables [∀ A, has_initial (structured_arrow A G)]

@[simps]
def initials_equivalence (A : C) (B : D) :
  ((⊥_ (structured_arrow A G)).right ⟶ B) ≃ (A ⟶ G.obj B) :=
{ to_fun := λ g, (⊥_ (structured_arrow A G)).hom ≫ G.map g,
  inv_fun := λ f, comma_morphism.right (initial.to (structured_arrow.mk f)),
  left_inv := λ g,
  begin
    let B' : structured_arrow A G :=
      structured_arrow.mk ((⊥_ (structured_arrow A G)).hom ≫ G.map g),
    let g' : ⊥_ (structured_arrow A G) ⟶ B' := structured_arrow.hom_mk g rfl,
    have : initial.to _ = g',
    { apply colimit.hom_ext, rintro ⟨⟩ },
    change comma_morphism.right (initial.to B') = _,
    rw this,
    refl
  end,
  right_inv := λ f,
  begin
    let B' : structured_arrow A G := { right := B, hom := f },
    apply (comma_morphism.w (initial.to B')).symm.trans (category.id_comp _),
  end }

def left_adjoint_of_structured_arrow_initials : C ⥤ D :=
adjunction.left_adjoint_of_equiv (initials_equivalence G) (λ _ _, by simp)

def is_right_adjoint_of_structured_arrow_initials : is_right_adjoint G :=
{ left := left_adjoint_of_structured_arrow_initials G,
  adj := adjunction.adjunction_of_equiv_left _ _ }

end of_initials

section of_terminals
variables [∀ A, has_terminal (costructured_arrow G A)]

@[simps]
def terminals_equivalence (B : D) (A : C) :
  (G.obj B ⟶ A) ≃ (B ⟶ (⊤_ (costructured_arrow G A)).left) :=
{ to_fun := λ g, comma_morphism.left (terminal.from (costructured_arrow.mk g)),
  inv_fun := λ g, G.map g ≫ (⊤_ (costructured_arrow G A)).hom,
  left_inv := by tidy,
  right_inv := λ g,
  begin
    let B' : costructured_arrow G A :=
      costructured_arrow.mk (G.map g ≫ (⊤_ (costructured_arrow G A)).hom),
    let g' : B' ⟶ ⊤_ (costructured_arrow G A) := costructured_arrow.hom_mk g rfl,
    have : terminal.from _ = g',
    { apply limit.hom_ext, rintro ⟨⟩ },
    change comma_morphism.left (terminal.from B') = _,
    rw this,
    refl
  end }

def right_adjoint_of_costructured_arrow_terminals : C ⥤ D :=
adjunction.right_adjoint_of_equiv (terminals_equivalence G)
  (λ B₁ B₂ A f g, by { rw ←equiv.eq_symm_apply, simp })

def is_right_adjoint_of_costructured_arrow_terminals : is_left_adjoint G :=
{ right := right_adjoint_of_costructured_arrow_terminals G,
  adj := adjunction.adjunction_of_equiv_right _ _ }

end of_terminals

section
variables {F : C ⥤ D}

def mk_initial (h : F ⊣ G) (A : C) :
  is_initial (structured_arrow.mk (h.unit.app A) : structured_arrow A G) :=
{ desc := λ B, structured_arrow.hom_mk ((h.hom_equiv _ _).symm B.X.hom)
                 (by { dsimp, rw ←h.hom_equiv_unit, simp }),
  uniq' := λ s m w,
  begin
    ext,
    dsimp,
    rw [equiv.eq_symm_apply, adjunction.hom_equiv_unit],
    apply structured_arrow.w m,
  end }

end

end category_theory
