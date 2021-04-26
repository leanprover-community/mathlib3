/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.algebra.ring
import topology.algebra.group_with_zero

/-!
A topological field is usually described via
`{𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜] [has_continuous_inv 𝕜]`.

The only construction in this file doesn't need to assume `[has_continuous_inv 𝕜]`.
-/

variables {𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affine_homeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 :=
{ to_fun := λ x, a * x + b,
  inv_fun := λ y, (y - b) / a,
  left_inv := λ x, by { simp only [add_sub_cancel], exact mul_div_cancel_left x h, },
  right_inv := λ y, by { simp [mul_div_cancel' _ h], }, }
