/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach, Joël Riou
-/
import category_theory.comm_sq

/-!
# Lifting properties

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the lifting property of two morphisms in a category and
shows basic properties of this notion.

## Main results
- `has_lifting_property`: the definition of the lifting property

## Tags
lifting property

@TODO :
1) define llp/rlp with respect to a `morphism_property`
2) retracts, direct/inverse images, (co)products, adjunctions

-/

universe v

namespace category_theory

open category

variables {C : Type*} [category C] {A B B' X Y Y' : C}
  (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y) (p' : Y ⟶ Y')

/-- `has_lifting_property i p` means that `i` has the left lifting
property with respect to `p`, or equivalently that `p` has
the right lifting property with respect to `i`. -/
class has_lifting_property : Prop :=
(sq_has_lift : ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : comm_sq f i p g), sq.has_lift)

@[priority 100]
instance sq_has_lift_of_has_lifting_property {f : A ⟶ X} {g : B ⟶ Y} (sq : comm_sq f i p g)
  [hip : has_lifting_property i p] : sq.has_lift := by apply hip.sq_has_lift

namespace has_lifting_property

variables {i p}

lemma op (h : has_lifting_property i p) : has_lifting_property p.op i.op :=
⟨λ f g sq, begin
  simp only [comm_sq.has_lift.iff_unop, quiver.hom.unop_op],
  apply_instance,
end⟩

lemma unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y}
  (h : has_lifting_property i p) : has_lifting_property p.unop i.unop :=
⟨λ f g sq, begin
  rw comm_sq.has_lift.iff_op,
  simp only [quiver.hom.op_unop],
  apply_instance,
end⟩

lemma iff_op : has_lifting_property i p ↔ has_lifting_property p.op i.op := ⟨op, unop⟩

lemma iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
  has_lifting_property i p ↔ has_lifting_property p.unop i.unop := ⟨unop, op⟩

variables (i p)

@[priority 100]
instance of_left_iso [is_iso i] : has_lifting_property i p :=
⟨λ f g sq, comm_sq.has_lift.mk'
  { l := inv i ≫ f,
    fac_left' := by simp only [is_iso.hom_inv_id_assoc],
    fac_right' := by simp only [sq.w, assoc, is_iso.inv_hom_id_assoc], }⟩

@[priority 100]
instance of_right_iso [is_iso p] : has_lifting_property i p :=
⟨λ f g sq, comm_sq.has_lift.mk'
  { l := g ≫ inv p,
    fac_left' := by simp only [← sq.w_assoc, is_iso.hom_inv_id, comp_id],
    fac_right' := by simp only [assoc, is_iso.inv_hom_id, comp_id], }⟩

instance of_comp_left [has_lifting_property i p] [has_lifting_property i' p] :
  has_lifting_property (i ≫ i') p :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw assoc at fac,
  exact comm_sq.has_lift.mk'
    { l := (comm_sq.mk (comm_sq.mk fac).fac_right).lift,
      fac_left' := by simp only [assoc, comm_sq.fac_left],
      fac_right' := by simp only [comm_sq.fac_right], },
end⟩

instance of_comp_right [has_lifting_property i p] [has_lifting_property i p'] :
  has_lifting_property i (p ≫ p') :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw ← assoc at fac,
  let sq₂ := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
  exact comm_sq.has_lift.mk'
    { l := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
      fac_left' := by simp only [comm_sq.fac_left],
      fac_right' := by simp only [comm_sq.fac_right_assoc, comm_sq.fac_right], },
end⟩

lemma of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  (e : arrow.mk i ≅ arrow.mk i') (p : X ⟶ Y)
  [hip : has_lifting_property i p] : has_lifting_property i' p :=
by { rw arrow.iso_w' e, apply_instance, }

lemma of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (e : arrow.mk p ≅ arrow.mk p')
  [hip : has_lifting_property i p] : has_lifting_property i p' :=
by { rw arrow.iso_w' e, apply_instance, }

lemma iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  (e : arrow.mk i ≅ arrow.mk i') (p : X ⟶ Y) :
  has_lifting_property i p ↔ has_lifting_property i' p :=
by { split; introI, exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p], }

lemma iff_of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (e : arrow.mk p ≅ arrow.mk p') :
  has_lifting_property i p ↔ has_lifting_property i p' :=
by { split; introI, exacts [of_arrow_iso_right i e, of_arrow_iso_right i e.symm], }

end has_lifting_property

end category_theory
