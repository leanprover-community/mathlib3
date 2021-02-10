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

def finsupp.lmap_domain (R : Type*) [semiring R] {X Y : Type*} (f : X ⟶ Y) :
  linear_map R (X →₀ R) (Y →₀ R) :=
{ to_fun := finsupp.map_domain f,
  map_add' := λ _ _, finsupp.map_domain_add,
  map_smul' := λ _ _, finsupp.map_domain_smul _ _ }

@[simp] lemma finsupp.coe_lmap_domain (R : Type*) [semiring R] {X Y : Type*} (f : X ⟶ Y) :
  (finsupp.lmap_domain R f : (X →₀ R) → (Y →₀ R)) = finsupp.map_domain f := rfl

section
variables (R : Type u) [ring R] (X : Type*) (M : Type*) [add_comm_group M] [module R M]

/-- The bijection underlying the free-forgetful adjunction for R-modules. -/
def finsupp.hom_equiv : ((X →₀ R) →ₗ[R] M) ≃ (X → M) :=
{ to_fun := λ f x, f (finsupp.single x 1),
  inv_fun := λ f,
  { to_fun := λ g, g.sum (λ x r, r • f x),
    map_add' := λ g₁ g₂, by { rw [finsupp.sum_add_index], simp, simp [add_smul], },
    map_smul' := λ c g, begin sorry, end, },
  left_inv := λ f, begin ext g, simp, sorry, end,
  right_inv := λ f, funext $ sorry }

@[simp]
lemma finsupp.hom_equiv_apply (f) (x) : ((finsupp.hom_equiv R X M) f) x = f (finsupp.single x 1) :=
rfl
@[simp]
lemma finsupp.hom_equiv_symm_apply (f) (x) : ((finsupp.hom_equiv R X M).symm f) x = sorry :=
sorry

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
  by { intros, ext, sorry, } }

end Module
