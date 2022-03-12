/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import category_theory.simple
import algebra.category.Module.abelian
import ring_theory.simple_module

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are simple objects in the category of `R`-modules.
TODO : prove that reciprocally, a simple object in the category of `R`-modules is indeed
a simple module.
-/

section category
variables {R M : Type*} [ring R] [add_comm_group M] [module R M]
open category_theory
open Module

instance is_simple_module_of [H : is_simple_module R M] : is_simple_module R (of R M) := H

/-- A simple module is a simple object in the category of modules. -/
instance simple_of_is_simple_module [is_simple_module R M] : simple (of R M) :=
{ mono_is_iso_iff_nonzero := λ N f inj, begin
    split,
    { unfreezingI { rintro h rfl },
      haveI : unique M := unique_of_epi_zero N,
      haveI : nontrivial M := is_simple_module.nontrivial R M,
      exact false_of_nontrivial_of_subsingleton M },
    { intro h,
      haveI : epi f,
      { rw epi_iff_range_eq_top,
        refine (eq_bot_or_eq_top f.range).resolve_left _,
        exact (mt linear_map.range_eq_bot.mp h)},
      exact is_iso_of_mono_of_epi _ }
  end }

end category
