/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin, Scott Morrison
-/
import category_theory.simple
import algebra.category.Module.abelian
import algebra.category.Module.subobject
import ring_theory.simple_module

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]
open category_theory Module

lemma simple_iff_is_simple_module : simple (of R M) ↔ is_simple_module R M :=
(simple_iff_subobject_is_simple_order _).trans (subobject_Module (of R M)).is_simple_order_iff

/-- A simple module is a simple object in the category of modules. -/
instance simple_of_is_simple_module [is_simple_module R M] : simple (of R M) :=
simple_iff_is_simple_module.mpr ‹_›

/-- A simple object in the category of modules is a simple module. -/
instance is_simple_module_of_simple (M : Module R) [simple M] : is_simple_module R M :=
simple_iff_is_simple_module.mp (simple.of_iso (of_self_iso M))
