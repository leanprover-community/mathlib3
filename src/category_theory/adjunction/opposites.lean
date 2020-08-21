/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.adjunction.basic
import category_theory.opposites

open category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

namespace adjunction

/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def op_equiv' (A : C) (B : Cᵒᵖ) : (opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
op_equiv _ _

def op_equiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ opposite.op B) ≃ (B ⟶ A.unop) :=
op_equiv _ _

def op_equiv''' (A B : C) : (opposite.op A ⟶ opposite.op B) ≃ (B ⟶ A) :=
op_equiv _ _
```
-/
def op_equiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) :=
{ to_fun := λ f, f.unop,
  inv_fun := λ g, g.op,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

-- These two are made by hand rather than by simps because simps generates
-- `(op_equiv _ _).to_fun f = ...` rather than the coercion version.
@[simp]
lemma op_equiv_apply (A B : Cᵒᵖ) (f : A ⟶ B) : op_equiv _ _ f = f.unop :=
rfl
@[simp]
lemma op_equiv_symm_apply (A B : Cᵒᵖ) (f : B.unop ⟶ A.unop) : (op_equiv _ _).symm f = f.op :=
rfl

-- TODO: add the other variants of these; I only needed these two for now.
def adjoint_op {F : C ⥤ D} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F.op) : F ⊣ G.unop :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  ((h.hom_equiv (opposite.op Y) (opposite.op X)).trans (op_equiv _ _)).symm.trans (op_equiv _ _) }

def adjunction_op {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : G.op ⊣ F.op :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  (op_equiv _ _).trans ((adj.hom_equiv _ _).symm.trans (op_equiv _ (opposite.op _)).symm) }

end adjunction
