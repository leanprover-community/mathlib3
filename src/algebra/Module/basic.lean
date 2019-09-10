/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import algebra.module
import algebra.punit_instances
import category_theory.types
import linear_algebra.basic
open category_theory

universe u

variables (R : Type u) [ring R]

/-- The category of R-modules and their morphisms. -/
structure Module :=
  (carrier : Type u)
  [is_add_comm_group : add_comm_group carrier]
  [is_module : module R carrier]

attribute [instance] Module.is_add_comm_group Module.is_module

namespace Module

instance : has_coe_to_sort (Module R) :=
  { S := Type u, coe := Module.carrier }

def of (X : Type u) [add_comm_group X] [module R X] : Module R := ⟨R, X⟩

instance : has_zero (Module R) := ⟨ of R punit ⟩

variables (M N U : Module R)

instance : category (Module R) := {
  hom := λ M N, M →ₗ[R] N,
  id := λ M, 1,
  comp := λ A B C f g, g.comp f
}

@[simp] lemma id_apply (m : M) : (𝟙 M : M → M) m = m := rfl

@[simp] lemma module_hom_comp (f : M ⟶ N) (g : N ⟶ U) :
  ((f ≫ g) : M → U) = g ∘ f := rfl

@[extensionality] lemma hom_ext  {f g : M ⟶ N} : (f : M → N) = g → f = g :=
  λ w, linear_map.ext (function.funext_iff.1 w)

instance hom_is_module_hom {M₁ M₂ : Module R} (f : M₁ ⟶ M₂) :
  is_linear_map R (f : M₁ → M₂) := linear_map.is_linear _

end Module

instance (M : Type u) [add_comm_group M] [module R M] : has_coe (submodule R M) (Module R) :=
⟨ λ N, Module.of R N ⟩
