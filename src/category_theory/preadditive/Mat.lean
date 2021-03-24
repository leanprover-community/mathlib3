/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.default
import category_theory.preadditive.single_obj
import algebra.big_operators.basic
import data.matrix.dmatrix

/-!
# Matrices over a category.

When `C` is a preadditive category, `Mat C` is the preadditive categoriy
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.

-/

open category_theory category_theory.preadditive
open_locale classical big_operators
noncomputable theory

universes v u
variables (C : Type u) [category.{v} C] [preadditive C]

/--
An object in `Mat C` is a finite tuple of objects in `C`.
-/
structure Mat :=
(ι : Type u)
[F : fintype ι]
(X : ι → C)

attribute [instance] Mat.F

namespace Mat

variables {C}

/-- A morphism in `Mat C` is a dependently typed matrix of morphisms. -/
def hom (M N : Mat C) := dmatrix M.ι N.ι (λ i j, M.X i ⟶ N.X j)

namespace hom

/-- The identity matrix consists of identity morphisms on the diagonal, and zeros elsewhere. -/
def id (M : Mat C) : hom M M := λ i j, if h : i = j then eq_to_hom (congr_arg M.X h) else 0

/-- Composition of matrices using matrix multiplication. -/
def comp {M N K : Mat C} (f : hom M N) (g : hom N K) : hom M K :=
λ i k, ∑ j : N.ι, f i j ≫ g j k

end hom

section
local attribute [simp] hom.id hom.comp

instance : category (Mat C) :=
{ hom := hom,
  id := hom.id,
  comp := λ M N K f g, f.comp g,
  id_comp' := λ M N f, by simp [dite_comp],
  comp_id' := λ M N f, by simp [comp_dite],
  assoc' := λ M N K L f g h, begin
    ext i k,
    simp_rw [hom.comp, sum_comp, comp_sum, category.assoc],
    rw finset.sum_comm,
  end, }.

@[simp] lemma id_apply_self (M : Mat C) (i : M.ι) :
  (𝟙 M : hom M M) i i = 𝟙 _ :=
begin
  change dite _ _ _ = _,
  simp,
end

lemma id_apply (M : Mat C) (i j : M.ι) :
  (𝟙 M : hom M M) i j = if h : i = j then eq_to_hom (congr_arg M.X h) else 0 :=
rfl

@[simp] lemma comp_apply {M N K : Mat C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
  (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k := rfl

instance : preadditive (Mat C) :=
{ hom_group := λ M N, by { change add_comm_group (dmatrix M.ι N.ι _), apply_instance, },
  add_comp' := λ M N K f f' g, by { ext, simp [finset.sum_add_distrib], },
  comp_add' := λ M N K f g g', by { ext, simp [finset.sum_add_distrib], }, }

@[simp] lemma add_apply {M N : Mat C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j := rfl

end

/--
Check that we have a preadditive category of integer-valued matrices:
-/
example : preadditive (Mat (single_obj ℤ)) := infer_instance

end Mat
