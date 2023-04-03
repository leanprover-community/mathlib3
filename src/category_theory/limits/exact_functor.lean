/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.preserves.finite

/-!
# Bundled exact functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/

universes v₁ v₂ u₁ u₂

open category_theory.limits

namespace category_theory
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

section
variables (C) (D)

/-- Bundled left-exact functors. -/
@[derive category, nolint has_nonempty_instance]
def LeftExactFunctor :=
full_subcategory (λ F : C ⥤ D, nonempty (preserves_finite_limits F))

infixr ` ⥤ₗ `:26 := LeftExactFunctor

/-- A left exact functor is in particular a functor. -/
@[derive full, derive faithful]
def LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ (C ⥤ D) :=
full_subcategory_inclusion _

/-- Bundled right-exact functors. -/
@[derive category, nolint has_nonempty_instance]
def RightExactFunctor :=
full_subcategory (λ F : C ⥤ D, nonempty (preserves_finite_colimits F))

infixr ` ⥤ᵣ `:26 := RightExactFunctor

/-- A right exact functor is in particular a functor. -/
@[derive full, derive faithful]
def RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ (C ⥤ D) :=
full_subcategory_inclusion _

/-- Bundled exact functors. -/
@[derive category, nolint has_nonempty_instance]
def ExactFunctor := full_subcategory
  (λ F : C ⥤ D, nonempty (preserves_finite_limits F) ∧ nonempty (preserves_finite_colimits F))

infixr ` ⥤ₑ `:26 := ExactFunctor

/-- An exact functor is in particular a functor. -/
@[derive full, derive faithful]
def ExactFunctor.forget : (C ⥤ₑ D) ⥤ (C ⥤ D) :=
full_subcategory_inclusion _

/-- Turn an exact functor into a left exact functor. -/
@[derive full, derive faithful]
def LeftExactFunctor.of_exact : (C ⥤ₑ D) ⥤ (C ⥤ₗ D) :=
full_subcategory.map (λ X, and.left)

/-- Turn an exact functor into a left exact functor. -/
@[derive full, derive faithful]
def RightExactFunctor.of_exact : (C ⥤ₑ D) ⥤ (C ⥤ᵣ D) :=
full_subcategory.map (λ X, and.right)

variables {C D}

@[simp] lemma LeftExactFunctor.of_exact_obj (F : C ⥤ₑ D) :
  (LeftExactFunctor.of_exact C D).obj F = ⟨F.1, F.2.1⟩ := rfl
@[simp] lemma RightExactFunctor.of_exact_obj (F : C ⥤ₑ D) :
  (RightExactFunctor.of_exact C D).obj F = ⟨F.1, F.2.2⟩ := rfl

@[simp] lemma LeftExactFunctor.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
  (LeftExactFunctor.of_exact C D).map α = α := rfl
@[simp] lemma RightExactFunctor.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
  (RightExactFunctor.of_exact C D).map α = α := rfl

@[simp] lemma LeftExactFunctor.forget_obj (F : C ⥤ₗ D) :
  (LeftExactFunctor.forget C D).obj F = F.1 := rfl
@[simp] lemma RightExactFunctor.forget_obj (F : C ⥤ᵣ D) :
  (RightExactFunctor.forget C D).obj F = F.1 := rfl
@[simp] lemma ExactFunctor.forget_obj (F : C ⥤ₑ D) :
  (ExactFunctor.forget C D).obj F = F.1 := rfl

@[simp] lemma LeftExactFunctor.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
  (LeftExactFunctor.forget C D).map α = α := rfl
@[simp] lemma RightExactFunctor.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
  (RightExactFunctor.forget C D).map α = α := rfl
@[simp] lemma ExactFunctor.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
  (ExactFunctor.forget C D).map α = α := rfl

/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
def LeftExactFunctor.of (F : C ⥤ D) [preserves_finite_limits F] : C ⥤ₗ D := ⟨F, ⟨infer_instance⟩⟩
/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
def RightExactFunctor.of (F : C ⥤ D) [preserves_finite_colimits F] : C ⥤ᵣ D :=
⟨F, ⟨infer_instance⟩⟩
/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
def ExactFunctor.of (F : C ⥤ D) [preserves_finite_limits F] [preserves_finite_colimits F] :
  C ⥤ₑ D := ⟨F, ⟨⟨infer_instance⟩, ⟨infer_instance⟩⟩⟩

@[simp] lemma LeftExactFunctor.of_fst (F : C ⥤ D) [preserves_finite_limits F] :
  (LeftExactFunctor.of F).obj = F := rfl
@[simp] lemma RightExactFunctor.of_fst (F : C ⥤ D) [preserves_finite_colimits F] :
  (RightExactFunctor.of F).obj = F := rfl
@[simp] lemma ExactFunctor.of_fst (F : C ⥤ D) [preserves_finite_limits F]
  [preserves_finite_colimits F] : (ExactFunctor.of F).obj = F := rfl

lemma LeftExactFunctor.forget_obj_of (F : C ⥤ D) [preserves_finite_limits F] :
  (LeftExactFunctor.forget C D).obj (LeftExactFunctor.of F) = F := rfl
lemma RightExactFunctor.forget_obj_of (F : C ⥤ D) [preserves_finite_colimits F] :
  (RightExactFunctor.forget C D).obj (RightExactFunctor.of F) = F := rfl
lemma ExactFunctor.forget_obj_of (F : C ⥤ D) [preserves_finite_limits F]
  [preserves_finite_colimits F] : (ExactFunctor.forget C D).obj (ExactFunctor.of F) = F := rfl

noncomputable instance (F : C ⥤ₗ D) : preserves_finite_limits F.obj := F.property.some
noncomputable instance (F : C ⥤ᵣ D) : preserves_finite_colimits F.obj := F.property.some
noncomputable instance (F : C ⥤ₑ D) : preserves_finite_limits F.obj := F.property.1.some
noncomputable instance (F : C ⥤ₑ D) : preserves_finite_colimits F.obj := F.property.2.some

end

end category_theory
