/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import algebra.tropical.basic
import order.conditionally_complete_lattice.basic

/-!

# Order on tropical algebraic structure

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the orders induced on tropical algebraic structures by the underlying type.

## Main declarations

* `conditionally_complete_lattice (tropical R)`
* `conditionally_complete_linear_order (tropical R)`

## Implementation notes

The order induced is the definitionally equal underlying order, which makes the proofs and
constructions quicker to implement.

-/

variables {R S : Type*}

open tropical

instance [has_sup R] : has_sup (tropical R) :=
{ sup := λ x y, trop (untrop x ⊔ untrop y) }

instance [has_inf R] : has_inf (tropical R) :=
{ inf := λ x y, trop (untrop x ⊓ untrop y) }

instance [semilattice_inf R] : semilattice_inf (tropical R) :=
{ le_inf := λ _ _ _, le_inf,
  inf_le_left := λ _ _, inf_le_left,
  inf_le_right := λ _ _, inf_le_right,
  ..tropical.has_inf,
  ..tropical.partial_order }

instance [semilattice_sup R] : semilattice_sup (tropical R) :=
{ sup_le := λ _ _ _, sup_le,
  le_sup_left := λ _ _, le_sup_left,
  le_sup_right := λ _ _, le_sup_right,
  ..tropical.has_sup,
  ..tropical.partial_order }

instance [lattice R] : lattice (tropical R) :=
{ ..tropical.semilattice_inf, ..tropical.semilattice_sup }

instance [has_Sup R] : has_Sup (tropical R) :=
{ Sup := λ s, trop (Sup (untrop '' s)) }

instance [has_Inf R] : has_Inf (tropical R) :=
{ Inf := λ s, trop (Inf (untrop '' s)) }

instance [conditionally_complete_lattice R] : conditionally_complete_lattice (tropical R) :=
{ le_cSup := λ s x hs hx, le_cSup
    (untrop_monotone.map_bdd_above hs)
    (set.mem_image_of_mem untrop hx),
  cSup_le := λ s x hs hx, cSup_le
    (hs.image untrop)
    (untrop_monotone.mem_upper_bounds_image hx),
  le_cInf := λ s x hs hx, le_cInf
    (hs.image untrop)
    (untrop_monotone.mem_lower_bounds_image hx),
  cInf_le := λ s x hs hx, cInf_le
    (untrop_monotone.map_bdd_below hs)
    (set.mem_image_of_mem untrop hx),
  ..tropical.has_Sup,
  ..tropical.has_Inf,
  ..tropical.lattice }

instance [conditionally_complete_linear_order R] :
  conditionally_complete_linear_order (tropical R) :=
{ ..tropical.conditionally_complete_lattice,
  ..tropical.linear_order }
