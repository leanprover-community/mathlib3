/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin, Scott Morrison
-/
import category_theory.simple
import algebra.category.Module.subobject
import algebra.category.Module.algebra
import ring_theory.simple_module
import linear_algebra.finite_dimensional

/-!
# Simple objects in the category of `R`-modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]
open category_theory Module

lemma simple_iff_is_simple_module : simple (of R M) ↔ is_simple_module R M :=
(simple_iff_subobject_is_simple_order _).trans (subobject_Module (of R M)).is_simple_order_iff

lemma simple_iff_is_simple_module' (M : Module R) : simple M ↔ is_simple_module R M :=
(simple.iff_of_iso (of_self_iso M).symm).trans simple_iff_is_simple_module

/-- A simple module is a simple object in the category of modules. -/
instance simple_of_is_simple_module [is_simple_module R M] : simple (of R M) :=
simple_iff_is_simple_module.mpr ‹_›

/-- A simple object in the category of modules is a simple module. -/
instance is_simple_module_of_simple (M : Module R) [simple M] : is_simple_module R M :=
simple_iff_is_simple_module.mp (simple.of_iso (of_self_iso M))

open finite_dimensional

local attribute [instance] module_of_algebra_Module is_scalar_tower_of_algebra_Module

/-- Any `k`-algebra module which is 1-dimensional over `k` is simple. -/
lemma simple_of_finrank_eq_one {k : Type*} [field k] [algebra k R]
  {V : Module R} (h : finrank k V = 1) : simple V :=
(simple_iff_is_simple_module' V).mpr (is_simple_module_of_finrank_eq_one h)
