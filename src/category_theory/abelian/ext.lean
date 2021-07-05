/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import algebra.category.Module.abelian
import category_theory.derived
import category_theory.linear.yoneda
import category_theory.abelian.opposite
import category_theory.abelian.projective

/-!
# Ext

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
  [enough_projectives Cᵒᵖ] -- When we have injective resolutions, just `[enough_injectives C]`

/--
`Ext R C n` is defined by left-deriving in the second argument of the `linear_yoneda` bifunctor.
-/
@[simps]
def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ Module R :=
functor.flip
{ obj := λ Y, functor.left_derived ((linear_yoneda R C).obj Y) n,
  map := λ Y Y' f, nat_trans.left_derived ((linear_yoneda R C).map f) n,
  map_id' := λ Y, by { rw category_theory.functor.map_id, apply nat_trans.left_derived_id, },
  map_comp' := λ Y Y' Y'' f g, by { rw functor.map_comp, apply nat_trans.left_derived_comp, } }

section sanity_check

/-- This shows that the above definition of `Ext` is flawed. -/
def this_is_bad (X : Cᵒᵖ) [projective X] (Y : C) (n : ℕ) :
  ((Ext R C (n+1)).obj X).obj Y ≅ 0 :=
((linear_yoneda R C).obj Y).left_derived_obj_projective_succ _ _

end sanity_check

-- PROJECT we don't yet have injective resolutions and right derived functors
-- (although this is only a copy-and-paste dualisation)
-- so we can't even state the alternative definition
-- in terms of right-deriving in the first argument,
-- let alone start the harder project of showing they agree.
