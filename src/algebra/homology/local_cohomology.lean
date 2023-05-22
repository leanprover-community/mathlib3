/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison
-/
import ring_theory.ideal.basic
import algebra.category.Module.colimits
import algebra.category.Module.projective
import category_theory.abelian.ext

/-!
# Local cohomology.

We just give one definition, deferring for later the other equivalent definitions,
and basic properties.
-/

open opposite
open category_theory
open category_theory.limits

noncomputable theory

variables (R : Type) [comm_ring R] (I : ideal R) (M : Module.{0} R)

local attribute [ext] quiver.hom.unop_inj

/-- The functor from the natural numbers that gives the R-modules R/I^t -/
def ring_mod_powers : ℕ ⥤ (Module.{0} R)ᵒᵖ :=
{ obj := λ t, op (Module.of R (R ⧸ I^t)),
  map := λ s t w, quiver.hom.op
    (submodule.mapq (I^t) (I^s) (linear_map.id) (ideal.pow_le_pow w.down.down)), }

/-- The diagram we will take the colimit of to define local cohomology -/
def local_cohomology_diagram (i : ℕ) : ℕ ⥤ Module.{0} R ⥤ Module.{0} R :=
ring_mod_powers R I ⋙ Ext R (Module.{0} R) i

/-- The `i`-th local cohomology module of an `R`-module `M` with support in `I`,
where``R` is a commutative ring and `I` is an ideal of `R`, expressed as a functor in `M` -/
def local_cohomology (i : ℕ) : Module.{0} R ⥤ Module R :=
colimit (local_cohomology_diagram R I i)
