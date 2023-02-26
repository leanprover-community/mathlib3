/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.order.basic
import algebra.order.archimedean

/-!
# Rational numbers are dense in a linear ordered archimedean field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that coercion from `ℚ` to a linear ordered archimedean field has dense range.
This lemma is in a separate file because `topology.order.basic` does not import
`algebra.order.archimedean`.
-/

variables {𝕜 : Type*} [linear_ordered_field 𝕜] [topological_space 𝕜] [order_topology 𝕜]
  [archimedean 𝕜]

/-- Rational numbers are dense in a linear ordered archimedean field. -/
lemma rat.dense_range_cast : dense_range (coe : ℚ → 𝕜) :=
dense_of_exists_between $ λ a b h, set.exists_range_iff.2 $ exists_rat_btwn h
