/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import algebra.module
import algebra.punit_instances
import category_theory.concrete_category
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

-- TODO consider removing this after #1438 merges?
instance : has_coe_to_sort (Module R) :=
{ S := Type u, coe := Module.carrier }

instance : concrete_category (Module.{u} R) :=
{ to_category :=
  { hom   := λ M N, M →ₗ[R] N,
    id    := λ M, 1,
    comp  := λ A B C f g, g.comp f },
  forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

def of (X : Type u) [add_comm_group X] [module R X] : Module R := ⟨R, X⟩

-- TODO: Once #1445 has merged, replace this with `has_zero_object (Module R)`
instance : has_zero (Module R) := ⟨of R punit⟩

variables (M N U : Module R)

@[simp] lemma id_apply (m : M) : (𝟙 M : M → M) m = m := rfl

@[simp] lemma coe_comp (f : M ⟶ N) (g : N ⟶ U) :
  ((f ≫ g) : M → U) = g ∘ f := rfl

instance hom_is_module_hom {M₁ M₂ : Module R} (f : M₁ ⟶ M₂) :
  is_linear_map R (f : M₁ → M₂) := linear_map.is_linear _

end Module

instance (M : Type u) [add_comm_group M] [module R M] : has_coe (submodule R M) (Module R) :=
⟨ λ N, Module.of R N ⟩
