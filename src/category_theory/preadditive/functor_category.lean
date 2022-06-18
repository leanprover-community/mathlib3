/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import category_theory.preadditive.default

/-!
# Preadditive structure on functor categories

If `C` and `D` are categories and `D` is preadditive,
then `C ⥤ D` is also preadditive.

-/

open_locale big_operators

namespace category_theory
open category_theory.limits preadditive

variables {C D : Type*} [category C] [category D] [preadditive D]

instance functor_category_preadditive : preadditive (C ⥤ D) :=
{ hom_group := λ F G,
  { add := λ α β,
    { app := λ X, α.app X + β.app X,
      naturality' := by { intros, rw [comp_add, add_comp, α.naturality, β.naturality] } },
    zero := { app := λ X, 0, naturality' := by { intros, rw [zero_comp, comp_zero] } },
    neg := λ α,
    { app := λ X, -α.app X,
      naturality' := by { intros, rw [comp_neg, neg_comp, α.naturality] } },
    sub := λ α β,
    { app := λ X, α.app X - β.app X,
      naturality' := by { intros, rw [comp_sub, sub_comp, α.naturality, β.naturality] } },
    add_assoc := by { intros, ext, apply add_assoc },
    zero_add := by { intros, ext, apply zero_add },
    add_zero := by { intros, ext, apply add_zero },
    sub_eq_add_neg := by { intros, ext, apply sub_eq_add_neg },
    add_left_neg := by { intros, ext, apply add_left_neg },
    add_comm := by { intros, ext, apply add_comm } },
  add_comp' := by { intros, ext, apply add_comp },
  comp_add' := by { intros, ext, apply comp_add } }

namespace nat_trans

variables {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps] def app_hom (X : C) : (F ⟶ G) →+ (F.obj X ⟶ G.obj X) :=
{ to_fun := λ α, α.app X,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simp] lemma app_zero (X : C) : (0 : F ⟶ G).app X = 0 := rfl

@[simp] lemma app_add (X : C) (α β : F ⟶ G) : (α + β).app X = α.app X + β.app X := rfl

@[simp] lemma app_sub (X : C) (α β : F ⟶ G) : (α - β).app X = α.app X - β.app X := rfl

@[simp] lemma app_neg (X : C) (α : F ⟶ G) : (-α).app X = -α.app X := rfl

@[simp] lemma app_nsmul (X : C) (α : F ⟶ G) (n : ℕ) : (n • α).app X = n • α.app X :=
(app_hom X).map_nsmul α n

@[simp] lemma app_zsmul (X : C) (α : F ⟶ G) (n : ℤ) : (n • α).app X = n • α.app X :=
(app_hom X : (F ⟶ G) →+ (F.obj X ⟶ G.obj X)).map_zsmul α n

@[simp] lemma app_sum {ι : Type*} (s : finset ι) (X : C) (α : ι → (F ⟶ G)) :
  (∑ i in s, α i).app X = ∑ i in s, ((α i).app X) :=
by { rw [← app_hom_apply, add_monoid_hom.map_sum], refl }

end nat_trans

end category_theory
