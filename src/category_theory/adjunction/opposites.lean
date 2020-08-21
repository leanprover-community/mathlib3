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
def adjoint_of_op_adjoint (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  ((h.hom_equiv (opposite.op Y) (opposite.op X)).trans (op_equiv _ _)).symm.trans (op_equiv _ _) }

def adjoint_op (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
adjoint_of_op_adjoint F G.unop (h.of_nat_iso_left G.op_unop_iso.symm)

def adjoint_op'' (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
adjoint_of_op_adjoint _ _ (h.of_nat_iso_right F.op_unop_iso.symm)

def adjoint_op' (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
adjoint_op F.unop G (h.of_nat_iso_right F.op_unop_iso.symm)

def op_adjoint_of_adjoint (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  (op_equiv _ Y).trans ((h.hom_equiv _ _).symm.trans (op_equiv X (opposite.op _)).symm) }

def adjoint_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
(op_adjoint_of_adjoint F.unop _ h).of_nat_iso_left F.op_unop_iso

def adjoint_unop' (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
(op_adjoint_of_adjoint _ G.unop h).of_nat_iso_right G.op_unop_iso

def adjoint_unop'' (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
(adjoint_unop _ _ h).of_nat_iso_right G.op_unop_iso

end adjunction
