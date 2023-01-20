/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.basic

/-!
# Invariant submodules

In this file, we define and prove some basic results on invaraint submodules.
-/

/-- `U` is `T` invariant: `∀ u : V`, if `u ∈ U` then `T u ∈ U` -/
def submodule.invariant_under {V K : Type*} [semiring K] [add_comm_monoid V] [module K V]
   (U : submodule K V) (T : V →ₗ[K] V) : Prop := U ≤ U.comap T

/-- `U` is `T` invariant is equivalent to saying `T(U) ⊆ U` -/
lemma submodule.invariant_under_iff {V K : Type*} [semiring K] [add_comm_monoid V] [module K V]
  (U : submodule K V) (T : V →ₗ[K] V) : U.invariant_under T ↔ T '' U ⊆ U :=
by simp only [set.image_subset_iff]; refl
