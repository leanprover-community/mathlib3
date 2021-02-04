/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group
import category_theory.limits.shapes.kernels

noncomputable theory

open category_theory
open category_theory.limits

/-!
Some small examples of using limits and colimits in `Ab`, the category of additive commutative
groups.
-/

example (G H : Ab) (f : G ⟶ H) : Ab := kernel f
example (G H : Ab) (f : G ⟶ H) [epi f] : kernel (cokernel.π f) ≅ H :=
as_iso (kernel.ι (cokernel.π f))

-- TODO no images yet...
