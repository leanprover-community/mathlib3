/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
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
{ hom_equiv := λ X M, finsupp.hom_equiv R M X,
  hom_equiv_naturality_left_symm' :=
  begin
    intros _ _ _ f g, ext h,
    exact (finsupp.map_domain_sum_index f h (λ y, smul_add_hom_left R (g y))).symm,
  end }

end Module
