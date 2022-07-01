/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.operator_norm

/-!
# Compact operators

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open function set filter bornology

structure compact_operator {R R₂} [semiring R] [semiring R₂] (σ₁₂ : R →+* R₂) (E E₂ : Type*)
  [semi_normed_group E] [semi_normed_group E₂] [module R E] [module R₂ E₂] extends E →SL[σ₁₂] E₂ :=
(comap_cocompact_le' : (cocompact E₂).comap to_continuous_linear_map ≤ cobounded E)

set_option old_structure_cmd true

class compact_operator_class (F : Type*) {R R₂ : out_param Type*} [semiring R] [semiring R₂]
  (σ₁₂ : out_param $ R →+* R₂) (E : out_param Type*) [metric_space E] [add_comm_monoid E]
  (E₂ : out_param Type*) [topological_space E₂] [add_comm_monoid E₂] [module R E] [module R₂ E₂]
  extends continuous_semilinear_map_class F σ₁₂ E E₂ :=
(comap_cocompact_le' : ∀ f, (cocompact E₂).comap f ≤ cobounded E)

set_option old_structure_cmd false
