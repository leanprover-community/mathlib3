/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import algebra.category.Module.basic

/-!
The functor of forming finitely supported functions on a type with values in a `[ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/

noncomputable theory

universe u

open category_theory

/-- Scalar multiplication as an (additively) bilinear map. -/
def smul_bilinear
  {R : Type*} [semiring R] {M : Type*} [add_comm_monoid M] [semimodule R M]  :
  R →+ (M →+ M) :=
{ to_fun := λ r,
  { to_fun := λ m, r • m,
    map_zero' := by simp,
    map_add' := by simp [smul_add], },
  map_zero' := by { ext, simp, },
  map_add' := λ r s, by { ext, simp [add_smul] }, }

/-- Scalar multiplication as an additive map in its first argument (with second argument fixed). -/
def smul_linear_left
  {R : Type*} [semiring R] {M : Type*} [add_comm_monoid M] [semimodule R M] (m : M) :
  R →+ M :=
{ to_fun := λ r, r • m,
  map_zero' := by simp,
  map_add' := by simp [add_smul], }

/-- `finsupp.map_domain` as an `R`-linear map, whenever `R` is a semiring. -/
def finsupp.lmap_domain (R : Type*) [semiring R] {X Y : Type*} (f : X ⟶ Y) :
  linear_map R (X →₀ R) (Y →₀ R) :=
{ to_fun := finsupp.map_domain f,
  map_add' := λ _ _, finsupp.map_domain_add,
  map_smul' := λ _ _, finsupp.map_domain_smul _ _ }

@[simp] lemma finsupp.coe_lmap_domain (R : Type*) [semiring R] {X Y : Type*} (f : X ⟶ Y) :
  (finsupp.lmap_domain R f : (X →₀ R) → (Y →₀ R)) = finsupp.map_domain f := rfl

@[simp]
lemma finsupp.map_domain_sum_index {X Y : Type*} (f : X ⟶ Y)
  {M N : Type*} [add_comm_monoid M] [add_comm_monoid N]
  (g : X →₀ M) (h : Y → M →+ N) :
  (finsupp.map_domain f g).sum (λ y m, h y m) = g.sum (λ x m, h (f x) m) :=
begin
  dsimp [finsupp.map_domain],
  apply finsupp.induction_linear g,
  { simp, },
  { intros g₁ g₂ h₁ h₂,
    rw [finsupp.sum_add_index, finsupp.sum_add_index, finsupp.sum_add_index, h₁, h₂];
    simp, },
  { simp, }
end

section
variables (R : Type u) [ring R] (X : Type*) (M : Type*) [add_comm_group M] [module R M]

/-- The bijection underlying the free-forgetful adjunction for R-modules. -/
def finsupp.hom_equiv : ((X →₀ R) →ₗ[R] M) ≃ (X → M) :=
{ to_fun := λ f x, f (finsupp.single x 1),
  inv_fun := λ f,
  { to_fun := λ g, g.sum (λ x r, r • f x),
    map_add' := λ g₁ g₂, by { rw [finsupp.sum_add_index], simp, simp [add_smul], },
    map_smul' := λ c g, begin
      rw [finsupp.sum_smul_index, finsupp.smul_sum],
      { congr, funext, rw [mul_smul], },
      { simp, },
    end, },
  left_inv := λ f, begin
    ext g,
    apply finsupp.induction_linear g,
    { simp, },
    { intros g₁ g₂ h₁ h₂, rw [f.map_add, ←h₁, ←h₂], simp, },
    { intros x r, simp [←f.map_smul], },
  end,
  right_inv := λ f, funext $ (λ x, (by simp)) }

@[simp]
lemma finsupp.hom_equiv_apply (f) (x) : ((finsupp.hom_equiv R X M) f) x = f (finsupp.single x 1) :=
rfl
@[simp]
lemma finsupp.hom_equiv_symm_apply (f) (g) :
  ((finsupp.hom_equiv R X M).symm f) g = g.sum (λ x r, r • f x) :=
rfl

end

namespace Module

open_locale classical

variables (R : Type u) [ring R]

/--
The free functor `Type u ⥤ Module R` sending a type `X` to the
free `R`-module with generators `x : X`.
-/
@[simps]
def free : Type u ⥤ Module R :=
{ obj := λ X, Module.of R (X →₀ R),
  map := λ X Y f, finsupp.lmap_domain R f,
  map_id' := by { intros, ext1 v, exact finsupp.map_domain_id },
  map_comp' := by { intros, ext1 v,
    simp only [finsupp.coe_lmap_domain, function.comp_app, coe_comp],
    exact finsupp.map_domain_comp } }

/--
The free-forgetful adjunction for R-modules.
-/
def adj : free R ⊣ forget (Module.{u} R) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X M, finsupp.hom_equiv R X M,
  hom_equiv_naturality_left_symm' :=
  begin
    intros _ _ _ f g, ext h,
    exact (finsupp.map_domain_sum_index f h (λ y, smul_linear_left (g y))).symm,
  end }

end Module
