/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import algebra.category.Group.basic
import algebra.category.Module.abelian
import category_theory.derived
import category_theory.linear.yoneda
import category_theory.abelian.opposite
import category_theory.abelian.projective

/-!
# Ext

We define `Ext R C n : Cᵒᵖ ⥤ C ⥤ Module R` for any `R`-linear abelian category `C`
by deriving in the first argument of the bifunctor `(X, Y) ↦ Module.of R (unop X ⟶ Y)`.

## Implementation

It's not actually necessary here to assume `C` is abelian,
but the hypotheses, involving both `C` and `Cᵒᵖ`, are quite lengthy,
and in practice the abelian case is hopefully enough.

PROJECT we don't yet have injective resolutions and right derived functors
(although this is only a copy-and-paste dualisation)
so we can't even state the alternative definition
in terms of right-deriving in the first argument,
let alone start the harder project of showing they agree.
-/

noncomputable theory

open category_theory

variables (R : Type*) [ring R] (C : Type*) [category C] [abelian C] [linear R C]
  [enough_projectives C]

/--
`Ext R C n` is defined by deriving in the frst argument of `(X, Y) ↦ Module.of R (unop X ⟶ Y)`
(which is the second argument of `linear_yoneda`).
-/
@[simps]
def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ Module R :=
functor.flip
{ obj := λ Y, (((linear_yoneda R C).obj Y).right_op.left_derived n).left_op,
  map := λ Y Y' f, (nat_trans.left_derived ((linear_yoneda R C).map f).right_op n).left_op,
  map_id' := begin
    intros X,
    ext Y : 2,
    dsimp only [nat_trans.id_app, nat_trans.left_op_app,
      nat_trans.right_op_app, functor.left_op_obj, functor.right_op_obj],
    rw [(linear_yoneda R C).map_id, ← unop_id, nat_trans.right_op_id, nat_trans.left_derived_id],
    refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    rw [(linear_yoneda R C).map_comp, nat_trans.right_op_comp, nat_trans.left_derived_comp],
    refl,
  end }.

open_locale zero_object

/-- If `X : C` is projective and `n : ℕ`, then `Ext^n X Y ≅ 0` for any `Y`. -/
def ext_projective_succ (X Y : C) [projective X] (n : ℕ) :
  ((Ext R C (n+1)).obj (opposite.op X)).obj Y ≅ 0 :=
let E := (((linear_yoneda R C).obj Y).right_op.left_derived_obj_projective_succ n X).unop.symm in
E ≪≫
{ hom := 0,
  inv := 0,
  hom_inv_id' := begin
    let Z : (Module R)ᵒᵖ := 0,
    rw [← (0 : 0 ⟶ Z.unop).unop_op, ← (0 : Z.unop ⟶ 0).unop_op,
      ← unop_id, ← unop_comp],
    congr' 1,
    dsimp,
    dec_trivial,
  end }
