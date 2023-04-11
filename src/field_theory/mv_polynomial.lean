/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.mv_polynomial.comm_ring
import linear_algebra.dimension
import ring_theory.ideal.quotient
import ring_theory.mv_polynomial.basic

/-!
# Multivariate polynomials over fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains basic facts about multivariate polynomials over fields, for example that the
dimension of the space of multivariate polynomials over a field is equal to the cardinality of
finitely supported functions from the indexing set to `ℕ`.
-/

noncomputable theory

open_locale classical

open set linear_map submodule
open_locale big_operators

namespace mv_polynomial
universes u v
variables {σ : Type u} {K : Type v}
variables (σ K) [field K]

lemma quotient_mk_comp_C_injective (I : ideal (mv_polynomial σ K)) (hI : I ≠ ⊤) :
  function.injective ((ideal.quotient.mk I).comp mv_polynomial.C) :=
begin
  refine (injective_iff_map_eq_zero _).2 (λ x hx, _),
  rw [ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem] at hx,
  refine classical.by_contradiction (λ hx0, absurd (I.eq_top_iff_one.2 _) hI),
  have := I.mul_mem_left (mv_polynomial.C x⁻¹) hx,
  rwa [← mv_polynomial.C.map_mul, inv_mul_cancel hx0, mv_polynomial.C_1] at this,
end

end mv_polynomial



namespace mv_polynomial

universe u
variables {σ : Type u} {K : Type u} [field K]

open_locale classical

lemma rank_mv_polynomial : module.rank K (mv_polynomial σ K) = cardinal.mk (σ →₀ ℕ) :=
by rw [← cardinal.lift_inj, ← (basis_monomials σ K).mk_eq_rank]

end mv_polynomial
