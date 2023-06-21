/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.functor_category
import category_theory.linear.basic

/-!
# Linear structure on functor categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `C` and `D` are categories and `D` is `R`-linear,
then `C ⥤ D` is also `R`-linear.

-/

open_locale big_operators

namespace category_theory
open category_theory.limits linear

variables {R : Type*} [semiring R]
variables {C D : Type*} [category C] [category D] [preadditive D] [linear R D]

instance functor_category_linear : linear R (C ⥤ D) :=
{ hom_module := λ F G,
  { smul := λ r α,
    { app := λ X, r • α.app X,
      naturality' := by { intros, rw [comp_smul, smul_comp, α.naturality] } },
    one_smul := by { intros, ext, apply one_smul },
    zero_smul := by { intros, ext, apply zero_smul },
    smul_zero := by { intros, ext, apply smul_zero },
    add_smul := by { intros, ext, apply add_smul },
    smul_add := by { intros, ext, apply smul_add },
    mul_smul := by { intros, ext, apply mul_smul } },
  smul_comp' := by { intros, ext, apply smul_comp },
  comp_smul' := by { intros, ext, apply comp_smul } }

namespace nat_trans

variables {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps] def app_linear_map (X : C) : (F ⟶ G) →ₗ[R] (F.obj X ⟶ G.obj X) :=
{ to_fun := λ α, α.app X,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl, }

@[simp] lemma app_smul (X : C) (r : R) (α : F ⟶ G) : (r • α).app X = r • α.app X := rfl

end nat_trans

end category_theory
