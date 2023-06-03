/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import category_theory.monoidal.braided
import algebra.category.Module.monoidal.basic

/-!
# The symmetric monoidal structure on `Module R`.
-/

universes v w x u

open category_theory

namespace Module

variables {R : Type u} [comm_ring R]

/-- (implementation) the braiding for R-modules -/
def braiding (M N : Module.{u} R) : (M ⊗ N) ≅ (N ⊗ M) :=
linear_equiv.to_Module_iso (tensor_product.comm R M N)

namespace monoidal_category

@[simp] lemma braiding_naturality {X₁ X₂ Y₁ Y₂ : Module.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  (f ⊗ g) ≫ (Y₁.braiding Y₂).hom =
    (X₁.braiding X₂).hom ≫ (g ⊗ f) :=
begin
  apply tensor_product.ext',
  intros x y,
  refl
end

@[simp] lemma hexagon_forward (X Y Z : Module.{u} R) :
  (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom =
  ((braiding X Y).hom ⊗ 𝟙 Z) ≫ (α_ Y X Z).hom ≫ (𝟙 Y ⊗ (braiding X Z).hom) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  refl,
end

@[simp] lemma hexagon_reverse (X Y Z : Module.{u} R) :
  (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv =
  (𝟙 X ⊗ (Y.braiding Z).hom) ≫ (α_ X Z Y).inv ≫ ((X.braiding Z).hom ⊗ 𝟙 Y) :=
begin
  apply (cancel_epi (α_ X Y Z).hom).1,
  apply tensor_product.ext_threefold,
  intros x y z,
  refl,
end

local attribute [ext] tensor_product.ext

/-- The symmetric monoidal structure on `Module R`. -/
instance symmetric_category : symmetric_category (Module.{u} R) :=
{ braiding := braiding,
  braiding_naturality' := λ X₁ X₂ Y₁ Y₂ f g, braiding_naturality f g,
  hexagon_forward' := hexagon_forward,
  hexagon_reverse' := hexagon_reverse, }

@[simp] lemma braiding_hom_apply {M N : Module.{u} R} (m : M) (n : N) :
  ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m := rfl

@[simp] lemma braiding_inv_apply {M N : Module.{u} R} (m : M) (n : N) :
  ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n := rfl

end monoidal_category

end Module
