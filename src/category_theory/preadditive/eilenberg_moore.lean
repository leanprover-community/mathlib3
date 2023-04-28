/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/

import category_theory.preadditive.basic
import category_theory.monad.algebra
import category_theory.preadditive.additive_functor

/-!
# Preadditive structure on algebras over a monad

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `C` is a preadditive categories and `T` is an additive monad on `C` then `algebra T` is also
preadditive. Dually, if `U` is an additive comonad on `C` then `coalgebra U` is preadditive as well.

-/

universes v₁ u₁ -- morphism levels before object levels. See note [category_theory universes].

namespace category_theory
variables (C : Type u₁) [category.{v₁} C] [preadditive C] (T : monad C)
  [functor.additive (T : C ⥤ C)]

open category_theory.limits preadditive

/-- The category of algebras over an additive monad on a preadditive category is preadditive. -/
@[simps]
instance monad.algebra_preadditive : preadditive (monad.algebra T) :=
{ hom_group := λ F G,
  { add := λ α β,
    { f := α.f + β.f,
      h' := by simp only [functor.map_add, add_comp, monad.algebra.hom.h, comp_add] },
    zero :=
    { f := 0,
      h' := by simp only [functor.map_zero, zero_comp, comp_zero] },
    nsmul := λ n α,
    { f := n • α.f,
      h' := by rw [functor.map_nsmul, nsmul_comp, monad.algebra.hom.h, comp_nsmul] },
    neg := λ α,
    { f := -α.f,
      h' := by simp only [functor.map_neg, neg_comp, monad.algebra.hom.h, comp_neg] },
    sub := λ α β,
    { f := α.f - β.f,
      h' := by simp only [functor.map_sub, sub_comp, monad.algebra.hom.h, comp_sub] },
    zsmul := λ r α,
    { f := r • α.f,
      h' := by rw [functor.map_zsmul, zsmul_comp, monad.algebra.hom.h, comp_zsmul] },
    add_assoc := by { intros, ext, apply add_assoc },
    zero_add := by { intros, ext, apply zero_add },
    add_zero := by { intros, ext, apply add_zero },
    nsmul_zero' := by { intros, ext, apply zero_smul },
    nsmul_succ' := by { intros, ext, apply succ_nsmul },
    sub_eq_add_neg := by { intros, ext, apply sub_eq_add_neg },
    zsmul_zero' := by { intros, ext, apply zero_smul },
    zsmul_succ' := by { intros, ext, dsimp, simp only [coe_nat_zsmul, succ_nsmul], refl, },
    zsmul_neg' := by { intros, ext, simp only [zsmul_neg_succ_of_nat, neg_inj,
                       nsmul_eq_smul_cast ℤ] },
    add_left_neg := by { intros, ext, apply add_left_neg },
    add_comm := by { intros, ext, apply add_comm } },
  add_comp' := by { intros, ext, apply add_comp },
  comp_add' := by { intros, ext, apply comp_add } }

instance monad.forget_additive : (monad.forget T).additive := {}

variables (U : comonad C) [functor.additive (U : C ⥤ C)]

/-- The category of coalgebras over an additive comonad on a preadditive category is preadditive. -/
@[simps]
instance comonad.coalgebra_preadditive : preadditive (comonad.coalgebra U) :=
{ hom_group := λ F G,
  { add := λ α β,
    { f := α.f + β.f,
      h' := by simp only [functor.map_add, comp_add, comonad.coalgebra.hom.h, add_comp] },
    zero :=
    { f := 0,
      h' := by simp only [functor.map_zero, comp_zero, zero_comp] },
    nsmul := λ n α,
    { f := n • α.f,
      h' := by rw [functor.map_nsmul, comp_nsmul, comonad.coalgebra.hom.h, nsmul_comp] },
    neg := λ α,
    { f := -α.f,
      h' := by simp only [functor.map_neg, comp_neg, comonad.coalgebra.hom.h, neg_comp] },
    sub := λ α β,
    { f := α.f - β.f,
      h' := by simp only [functor.map_sub, comp_sub, comonad.coalgebra.hom.h, sub_comp] },
    zsmul := λ r α,
    { f := r • α.f,
      h' := by rw [functor.map_zsmul, comp_zsmul, comonad.coalgebra.hom.h, zsmul_comp] },
    add_assoc := by { intros, ext, apply add_assoc },
    zero_add := by { intros, ext, apply zero_add },
    add_zero := by { intros, ext, apply add_zero },
    nsmul_zero' := by { intros, ext, apply zero_smul },
    nsmul_succ' := by { intros, ext, apply succ_nsmul },
    sub_eq_add_neg := by { intros, ext, apply sub_eq_add_neg },
    zsmul_zero' := by { intros, ext, apply zero_smul },
    zsmul_succ' := by { intros, ext, dsimp, simp only [coe_nat_zsmul, succ_nsmul], refl, },
    zsmul_neg' := by { intros, ext, simp only [zsmul_neg_succ_of_nat, neg_inj,
                       nsmul_eq_smul_cast ℤ] },
    add_left_neg := by { intros, ext, apply add_left_neg },
    add_comm := by { intros, ext, apply add_comm } },
  add_comp' := by { intros, ext, apply add_comp },
  comp_add' := by { intros, ext, apply comp_add } }

instance comonad.forget_additive : (comonad.forget U).additive := {}

end category_theory
