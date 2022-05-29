/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.monoidal
import algebra.category.Algebra.basic
import category_theory.monoidal.Mon_


/-!
# `Mon_ (Module R) ≌ Algebra R`

The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.

Moreover, this equivalence is compatible with the forgetful functors to `Module R`.
-/

universes v u

open category_theory
open linear_map

open_locale tensor_product
local attribute [ext] tensor_product.ext

namespace Module

variables {R : Type u} [comm_ring R]

namespace Mon_Module_equivalence_Algebra

@[simps]
instance (A : Mon_ (Module.{u} R)) : ring A.X :=
{ one := A.one (1 : R),
  mul := λ x y, A.mul (x ⊗ₜ y),
  one_mul := λ x, by { convert linear_map.congr_fun A.one_mul ((1 : R) ⊗ₜ x), simp, },
  mul_one := λ x, by { convert linear_map.congr_fun A.mul_one (x ⊗ₜ (1 : R)), simp, },
  mul_assoc := λ x y z, by convert linear_map.congr_fun A.mul_assoc ((x ⊗ₜ y) ⊗ₜ z),
  left_distrib := λ x y z,
  begin
    convert A.mul.map_add (x ⊗ₜ y) (x ⊗ₜ z),
    rw ←tensor_product.tmul_add,
    refl,
  end,
  right_distrib := λ x y z,
  begin
    convert A.mul.map_add (x ⊗ₜ z) (y ⊗ₜ z),
    rw ←tensor_product.add_tmul,
    refl,
  end,
  ..(by apply_instance : add_comm_group A.X) }

instance (A : Mon_ (Module.{u} R)) : algebra R A.X :=
{ map_zero' := A.one.map_zero,
  map_one' := rfl,
  map_mul' := λ x y,
  begin
    have h := linear_map.congr_fun A.one_mul.symm (x ⊗ₜ (A.one y)),
    rwa [monoidal_category.left_unitor_hom_apply, ←A.one.map_smul] at h,
  end,
  commutes' := λ r a,
  begin dsimp,
    have h₁ := linear_map.congr_fun A.one_mul (r ⊗ₜ a),
    have h₂ := linear_map.congr_fun A.mul_one (a ⊗ₜ r),
    exact h₁.trans h₂.symm,
  end,
  smul_def' := λ r a, by { convert (linear_map.congr_fun A.one_mul (r ⊗ₜ a)).symm, simp, },
  ..A.one }

@[simp] lemma algebra_map (A : Mon_ (Module.{u} R)) (r : R) : algebra_map R A.X r = A.one r := rfl

/--
Converting a monoid object in `Module R` to a bundled algebra.
-/
@[simps]
def functor : Mon_ (Module.{u} R) ⥤ Algebra R :=
{ obj := λ A, Algebra.of R A.X,
  map := λ A B f,
  { to_fun := f.hom,
    map_one' := linear_map.congr_fun f.one_hom (1 : R),
    map_mul' := λ x y, linear_map.congr_fun f.mul_hom (x ⊗ₜ y),
    commutes' := λ r, linear_map.congr_fun f.one_hom r,
    ..(f.hom.to_add_monoid_hom) }, }.

/--
Converting a bundled algebra to a monoid object in `Module R`.
-/
@[simps]
def inverse_obj (A : Algebra.{u} R) : Mon_ (Module.{u} R) :=
{ X := Module.of R A,
  one := algebra.linear_map R A,
  mul := @algebra.lmul' R A _ _ _,
  one_mul' :=
  begin
    ext x,
    dsimp only [Algebra.id_apply, tensor_product.mk_apply,
      algebra.linear_map_apply, linear_map.compr₂_apply, function.comp_app,
      ring_hom.map_one, Module.monoidal_category.hom_apply, Algebra.coe_comp,
      Module.monoidal_category.left_unitor_hom_apply],
    rw [algebra.lmul'_apply, monoidal_category.left_unitor_hom_apply, ← algebra.smul_def]
  end,
  mul_one' :=
  begin
    ext x,
    dsimp only [Algebra.id_apply, tensor_product.mk_apply, algebra.linear_map_apply,
      linear_map.compr₂_apply, function.comp_app, Module.monoidal_category.hom_apply,
      Algebra.coe_comp],
    rw [algebra.lmul'_apply, Module.monoidal_category.right_unitor_hom_apply,
        ← algebra.commutes, ← algebra.smul_def]
  end,
  mul_assoc' :=
  begin
    ext x y z,
    dsimp only [Algebra.id_apply, tensor_product.mk_apply, linear_map.compr₂_apply,
      function.comp_app, Module.monoidal_category.hom_apply,
      Algebra.coe_comp, monoidal_category.associator_hom_apply],
    simp only [algebra.lmul'_apply, mul_assoc]
  end }

/--
Converting a bundled algebra to a monoid object in `Module R`.
-/
@[simps]
def inverse : Algebra.{u} R ⥤ Mon_ (Module.{u} R) :=
{ obj := inverse_obj,
  map := λ A B f,
  { hom := f.to_linear_map,
    one_hom' :=
      by { ext, dsimp, simp only [ring_hom.map_one, alg_hom.map_one] },
    mul_hom' :=
      by { ext, dsimp, simp only [algebra.lmul'_apply, ring_hom.map_mul, alg_hom.map_mul] } } }.

end Mon_Module_equivalence_Algebra

open Mon_Module_equivalence_Algebra

/--
The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.
-/
def Mon_Module_equivalence_Algebra : Mon_ (Module.{u} R) ≌ Algebra R :=
{ functor := functor,
  inverse := inverse,
  unit_iso := nat_iso.of_components
    (λ A,
    { hom := { hom := { to_fun := id, map_add' := λ x y, rfl, map_smul' := λ r a, rfl, },
               mul_hom' := by { ext, dsimp at *,
                                simp only [algebra.lmul'_apply, Mon_.X.ring_mul] } },
      inv := { hom := { to_fun := id, map_add' := λ x y, rfl, map_smul' := λ r a, rfl, },
               mul_hom' := by { ext, dsimp at *,
                                simp only [algebra.lmul'_apply, Mon_.X.ring_mul]} } })
    (by tidy),
  counit_iso := nat_iso.of_components (λ A,
  { hom :=
    { to_fun := id,
      map_zero' := rfl,
      map_add' := λ x y, rfl,
      map_one' := (algebra_map R A).map_one,
      map_mul' := λ x y, algebra.lmul'_apply,
      commutes' := λ r, rfl, },
    inv :=
    { to_fun := id,
      map_zero' := rfl,
      map_add' := λ x y, rfl,
      map_one' := (algebra_map R A).map_one.symm,
      map_mul' := λ x y, algebra.lmul'_apply.symm,
      commutes' := λ r, rfl } }) (by { intros, refl }), }.

/--
The equivalence `Mon_ (Module R) ≌ Algebra R`
is naturally compatible with the forgetful functors to `Module R`.
-/
def Mon_Module_equivalence_Algebra_forget :
  Mon_Module_equivalence_Algebra.functor ⋙ forget₂ (Algebra.{u} R) (Module.{u} R) ≅
    Mon_.forget (Module.{u} R):=
nat_iso.of_components (λ A,
{ hom :=
  { to_fun := id,
    map_add' := λ x y, rfl,
    map_smul' := λ c x, rfl },
  inv :=
  { to_fun := id,
    map_add' := λ x y, rfl,
    map_smul' := λ c x, rfl }, }) (by tidy)

end Module
