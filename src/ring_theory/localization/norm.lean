/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.localization.module
import ring_theory.norm

/-!

# Field/algebra norm and localization

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results on the combination of `algebra.norm` and `is_localization`.

## Main results

 * `algebra.norm_localization`: let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M`
  of `R S` respectively. Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R`
  if `S` is free as `R`-module

## Tags

field norm, algebra norm, localization

-/

open_locale non_zero_divisors

variables (R : Type*) {S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
variables {Rₘ Sₘ : Type*} [comm_ring Rₘ] [algebra R Rₘ] [comm_ring Sₘ] [algebra S Sₘ]
variables (M : submonoid R)
variables [is_localization M Rₘ] [is_localization (algebra.algebra_map_submonoid S M) Sₘ]
variables [algebra Rₘ Sₘ] [algebra R Sₘ] [is_scalar_tower R Rₘ Sₘ] [is_scalar_tower R S Sₘ]
include M

/-- Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` respectively.
Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R` if `S` is free as `R`-module.
-/
lemma algebra.norm_localization [module.free R S] [module.finite R S] (a : S) :
  algebra.norm Rₘ (algebra_map S Sₘ a) = algebra_map R Rₘ (algebra.norm R a) :=
begin
  casesI subsingleton_or_nontrivial R,
  { haveI : subsingleton Rₘ := module.subsingleton R Rₘ,
    simp },
  let b := module.free.choose_basis R S,
  letI := classical.dec_eq (module.free.choose_basis_index R S),
  rw [algebra.norm_eq_matrix_det (b.localization_localization Rₘ M Sₘ),
      algebra.norm_eq_matrix_det b, ring_hom.map_det],
  congr,
  ext i j,
  simp only [matrix.map_apply, ring_hom.map_matrix_apply, algebra.left_mul_matrix_eq_repr_mul,
      basis.localization_localization_apply, ← _root_.map_mul],
  apply basis.localization_localization_repr_algebra_map
end
