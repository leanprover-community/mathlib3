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
  (carrier : Type)
  (prop_add_comm_group : add_comm_group carrier)
  (prop_module : module R carrier)

namespace Module
  instance : has_coe_to_sort (Module R) :=
    { S := Type, coe := Module.carrier}

  instance add_comm_group (M : Module R) : add_comm_group M := M.prop_add_comm_group
  instance R_module (M : Module R) : module R M := M.prop_module

  def of (X : Type) [h₁ : add_comm_group X] [h₂ : module R X] : Module R := ⟨ X , h₁ , h₂⟩

  instance : has_zero (Module R) := ⟨ of R punit ⟩

  variables (M N U : Module R)

  instance : category (Module R) := {
    hom := λ M N, M →ₗ[R] N,
    id := λ M, 1 ,
    comp := λ A B C f g, g.comp f ,
  }

  @[simp] lemma module_id : linear_map.to_fun (𝟙 M) = id := rfl

  @[simp] lemma module_hom_comp (f : M ⟶ N) (g : N ⟶ U) :
    ((f ≫ g) : M → U) = g.to_fun ∘ f.to_fun := rfl

  instance : has_coe_to_fun (M ⟶ N) :=
    { F   := λ f, M → N,
      coe := λ f, (f : M → N) }

  @[extensionality] lemma hom_ext  {f g : M ⟶ N} : (∀ x : M, f x = g x) → f = g :=
    λ w, linear_map.ext w

  @[extensionality] lemma hom_ext'  {f g : M ⟶ N} : (f : M → N) = g → f = g :=
    λ w, hom_ext R M N (function.funext_iff.1 w)

  @[simp] lemma coe_id {M : Module R} : ((𝟙 M) : M → M) = id := rfl

  instance hom_is_module_hom {M₁ M₂ : Module R} (f : M₁ ⟶ M₂) :
    is_linear_map R (f : M₁ → M₂) := linear_map.is_linear _

end Module

instance (M : Type) [add_comm_group M] [module R M] : has_coe (submodule R M) (Module R) :=
⟨ λ N, Module.of R N ⟩
