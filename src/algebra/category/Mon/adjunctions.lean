/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import algebra.category.Mon.basic
import algebra.category.Semigroup.basic
import algebra.group.with_one

/-!
# Adjunctions regarding the category of (commutative) monoids

-/

universe u

open category_theory

/-- The functor of adjoining a neutral element `one` to a semigroup.
 -/
@[simps]
def adjoin_one : Semigroup.{u} ⥤ Mon.{u} :=
{ obj := λ S, Mon.of (with_one S),
  map := λ X Y, with_one.map,
  map_id' := λ X, with_one.map_id,
  map_comp' := λ X Y Z, with_one.map_comp }

@[to_additive has_forget_to_AddSemigroup]
instance has_forget_to_Semigroup : has_forget₂ Mon Semigroup :=
{ forget₂ :=
  { obj := λ M, Semigroup.of M,
    map := λ M N, monoid_hom.to_mul_hom },
}

/-- The adjoin_one-forgetful adjunction from `Semigroup` to `Mon`.-/
def adjoin_one_adj : adjoin_one ⊣ forget₂ Mon.{u} Semigroup.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ S M, with_one.lift.symm,
  hom_equiv_naturality_left_symm' := begin intros, ext1, simp, sorry end }
