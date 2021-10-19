/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.sums.basic

/-!
# Associator for binary disjoint union of categories.

The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/

universes v u

open category_theory
open sum

namespace category_theory.sum

variables (C : Type u) [category.{v} C]
          (D : Type u) [category.{v} D]
          (E : Type u) [category.{v} E]

/--
The associator functor `(C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E)` for sums of categories.
-/
def associator : (C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E) :=
{ obj := λ X, match X with
  | inl (inl X) := inl X
  | inl (inr X) := inr (inl X)
  | inr X := inr (inr X)
  end,
  map := λ X Y f, match X, Y, f with
  | inl (inl X), inl (inl Y), f := f
  | inl (inr X), inl (inr Y), f := f
  | inr X, inr Y, f := f
  end }

@[simp] lemma associator_obj_inl_inl (X) : (associator C D E).obj (inl (inl X)) = inl X := rfl
@[simp] lemma associator_obj_inl_inr (X) : (associator C D E).obj (inl (inr X)) = inr (inl X) := rfl
@[simp] lemma associator_obj_inr (X) : (associator C D E).obj (inr X) = inr (inr X) := rfl
@[simp] lemma associator_map_inl_inl {X Y : C} (f : inl (inl X) ⟶ inl (inl Y)) :
  (associator C D E).map f = f := rfl
@[simp] lemma associator_map_inl_inr {X Y : D} (f : inl (inr X) ⟶ inl (inr Y)) :
  (associator C D E).map f = f := rfl
@[simp] lemma associator_map_inr {X Y : E} (f : inr X ⟶ inr Y) :
  (associator C D E).map f = f := rfl

/--
The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categories.
-/
def inverse_associator : C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E :=
{ obj := λ X, match X with
  | inl X := inl (inl X)
  | inr (inl X) := inl (inr X)
  | inr (inr X) := inr X
  end,
  map := λ X Y f, match X, Y, f with
  | inl X, inl Y, f := f
  | inr (inl X), inr (inl Y), f := f
  | inr (inr X), inr (inr Y), f := f
  end }

@[simp] lemma inverse_associator_obj_inl (X) :
  (inverse_associator C D E).obj (inl X) = inl (inl X) := rfl
@[simp] lemma inverse_associator_obj_inr_inl (X) :
  (inverse_associator C D E).obj (inr (inl X)) = inl (inr X) := rfl
@[simp] lemma inverse_associator_obj_inr_inr (X) :
  (inverse_associator C D E).obj (inr (inr X)) = inr X := rfl
@[simp] lemma inverse_associator_map_inl {X Y : C} (f : inl X ⟶ inl Y) :
  (inverse_associator C D E).map f = f := rfl
@[simp] lemma inverse_associator_map_inr_inl {X Y : D} (f : inr (inl X) ⟶ inr (inl Y)) :
  (inverse_associator C D E).map f = f := rfl
@[simp] lemma inverse_associator_map_inr_inr {X Y : E} (f : inr (inr X) ⟶ inr (inr Y)) :
  (inverse_associator C D E).map f = f := rfl

/--
The equivalence of categories expressing associativity of sums of categories.
-/
def associativity : (C ⊕ D) ⊕ E ≌ C ⊕ (D ⊕ E) :=
equivalence.mk (associator C D E) (inverse_associator C D E)
  (nat_iso.of_components (λ X, eq_to_iso (by tidy)) (by tidy))
  (nat_iso.of_components (λ X, eq_to_iso (by tidy)) (by tidy))

instance associator_is_equivalence : is_equivalence (associator C D E) :=
(by apply_instance : is_equivalence (associativity C D E).functor)

instance inverse_associator_is_equivalence : is_equivalence (inverse_associator C D E) :=
(by apply_instance : is_equivalence (associativity C D E).inverse)

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end category_theory.sum
