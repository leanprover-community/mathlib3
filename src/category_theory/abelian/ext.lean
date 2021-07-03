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

TODO: Fix this docstring

We define `Ext R C n : Cᵒᵖ ⥤ C ⥤ Module R`
for any `R`-linear abelian category `C`
by left-deriving in the second argument of
the `linear_yoneda` bifunctor `(X, Y) ↦ Module.of R (unop X ⟶ Y)`

## Implementation
It's not actually necessary here to assume `C` is abelian,
but the hypotheses, involving both `C` and `Cᵒᵖ`, are quite lengthy,
and in practice the abelian case is hopefully enough.
-/

noncomputable theory

open category_theory

variables (R : Type*) [ring R] (C : Type*) [category C] [abelian C] [linear R C]
  [enough_projectives C] -- When we have injective resolutions, just `[enough_injectives C]`

/--
TODO: Fix this docstring
`Ext R C n` is defined by left-deriving in the second argument of the `linear_yoneda` bifunctor.
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
    rw [(linear_yoneda R C).map_id, ← unop_id],
    -- TODO: Make the following a separate lemma
    have : nat_trans.right_op (𝟙 ((linear_yoneda R C).obj X)) = 𝟙 _, refl,
    rw [this, nat_trans.left_derived_id],
    refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    rw (linear_yoneda R C).map_comp,
    -- TODO: Make the following a separate lemma
    have : nat_trans.right_op ((linear_yoneda R C).map f ≫ (linear_yoneda R C).map g) =
      ((linear_yoneda R C).map g).right_op ≫ ((linear_yoneda R C).map f).right_op,
      by refl,
    rw [this, nat_trans.left_derived_comp],
    refl,
  end }

-- PROJECT we don't yet have injective resolutions and right derived functors
-- (although this is only a copy-and-paste dualisation)
-- so we can't even state the alternative definition
-- in terms of right-deriving in the first argument,
-- let alone start the harder project of showing they agree.
