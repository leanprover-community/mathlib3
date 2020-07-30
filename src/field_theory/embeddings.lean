/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.adjoin_root
import ring_theory.algebra_tower
import ring_theory.polynomial
import field_theory.minimal_polynomial

/-!
# Theorems about embeddings

This file contains important lemmas for `field_theory/splitting_field` such as (TODO).
-/

noncomputable theory
open_locale classical

variables (F : Type*) [field F]

#check ring_hom.injective

/-- The bottom subalgebra is isomorphic to the field. -/
def ring_equiv.of_bot (R : Type*) [field R] [algebra F R] : (⊥ : subalgebra F R) ≃+* F :=
ring_equiv.symm $ ring_equiv.of_bijective (algebra_map F _)
⟨(ring_hom.injective_iff _).2 $ λ x hx, _, _⟩

#check ring_hom.injective
#check monoid_hom.map_eq_zero

/-- If the minimal polynomial of each `ai` splits in `L` then `F(a1, ..., an)` embeds in `L`. -/
theorem lift_of_splits {F K L : Type*} [field F] [comm_ring K] [field L]
  [algebra F K] [algebra F L] (s : finset K) :
  (∀ x ∈ s, ∃ H : is_integral F x, splits (algebra_map F L) (minimal_polynomial H)) →
  nonempty (algebra.adjoin F (↑s : set K) →ₐ[F] L) :=
begin
end
