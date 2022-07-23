/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.trace_class

/-!
# Hilbert-Schmidt operators

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

open_locale inner_product

namespace continuous_linear_map

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
  [complete_space E] [complete_space F]

def is_HS (T : E →L[𝕜] F) : Prop := (T† ∘L T).is_trace_class

@[simp] lemma is_HS_def {T : E →L[𝕜] F} : T.is_HS ↔ (T† ∘L T).is_trace_class := iff.rfl

end continuous_linear_map
