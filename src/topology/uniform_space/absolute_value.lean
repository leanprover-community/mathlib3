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
open_locale filter topology

namespace absolute_value

variables {𝕜 : Type*} [linear_ordered_field 𝕜]
variables {R : Type*} [comm_ring R] (abv : absolute_value R 𝕜)

/-- The uniform space structure coming from an absolute value. -/
protected def uniform_space : uniform_space R :=
uniform_space.of_fun (λ x y, abv (y - x)) (by simp) (λ x y, abv.map_sub y x)
  (λ x y z, (abv.sub_le _ _ _).trans_eq (add_comm _ _)) $
  λ ε ε0, ⟨ε / 2, half_pos ε0, λ _ h₁ _ h₂, (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩

theorem has_basis_uniformity :
  𝓤[abv.uniform_space].has_basis (λ ε : 𝕜, 0 < ε) (λ ε, {p : R × R | abv (p.2 - p.1) < ε}) :=
uniform_space.has_basis_of_fun (exists_gt _) _ _ _ _ _

end absolute_value
