/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import algebra.order.absolute_value
import topology.uniform_space.basic

/-!
# Uniform structure induced by an absolute value

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/

open set function filter uniform_space
open_locale filter

namespace is_absolute_value
variables {𝕜 : Type*} [linear_ordered_field 𝕜]
variables {R : Type*} [comm_ring R] (abv : R → 𝕜) [is_absolute_value abv]

/-- The uniformity coming from an absolute value. -/
def uniform_space_core : uniform_space.core R :=
uniform_space.core.of_fun (λ x y, abv (y - x)) (by simp [abv_zero abv]) (λ x y, abv_sub abv y x)
  (λ x y z,
    calc abv (z - x) = abv ((y - x) + (z - y)) : by rw [add_comm, sub_add_sub_cancel]
    ... ≤ abv (y - x) + abv (z - y) : abv_add _ _ _) $
  λ ε ε0, ⟨ε / 2, half_pos ε0, λ _ h₁ _ h₂, (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩

/-- The uniform structure coming from an absolute value. -/
def uniform_space : uniform_space R :=
uniform_space.of_core (uniform_space_core abv)

theorem mem_uniformity {s : set (R×R)} :
  s ∈ (uniform_space_core abv).uniformity ↔ (∃ ε > 0, ∀ {a b : R}, abv (b - a) < ε → (a, b) ∈ s) :=
((uniform_space.core.has_basis_of_fun (exists_gt _) _ _ _ _ _).1 s).trans $
  by simp only [subset_def, prod.forall]; refl

end is_absolute_value
