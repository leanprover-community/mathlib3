/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import algebra.algebra.tower
import data.mv_polynomial.basic

/-!
# Algebra towers for multivariate polynomial

This file proves some basic results about the algebra tower structure for the type
`mv_polynomial σ R`.

This structure itself is provided elsewhere as `mv_polynomial.is_scalar_tower`

When you update this file, you can also try to make a corresponding update in
`ring_theory.polynomial.tower`.
-/

variables (R A B : Type*) {σ : Type*}

namespace mv_polynomial

section semiring
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B]
variables [is_scalar_tower R A B]

variables {R B}

theorem aeval_map_algebra_map (x : σ → B) (p : mv_polynomial σ R) :
  aeval x (map (algebra_map R A) p) = aeval x p :=
by rw [aeval_def, aeval_def, eval₂_map, is_scalar_tower.algebra_map_eq R A B]

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

variables {R A}

lemma aeval_algebra_map_apply (x : σ → A) (p : mv_polynomial σ R) :
  aeval (algebra_map A B ∘ x) p = algebra_map A B (mv_polynomial.aeval x p) :=
by rw [aeval_def, aeval_def, ← coe_eval₂_hom, ← coe_eval₂_hom, map_eval₂_hom,
  ←is_scalar_tower.algebra_map_eq]

lemma aeval_algebra_map_eq_zero_iff [no_zero_smul_divisors A B] [nontrivial B]
  (x : σ → A) (p : mv_polynomial σ R) :
  aeval (algebra_map A B ∘ x) p = 0 ↔ aeval x p = 0 :=
by rw [aeval_algebra_map_apply, algebra.algebra_map_eq_smul_one, smul_eq_zero,
  iff_false_intro (one_ne_zero' B), or_false]

lemma aeval_algebra_map_eq_zero_iff_of_injective
  {x : σ → A} {p : mv_polynomial σ R}
  (h : function.injective (algebra_map A B)) :
  aeval (algebra_map A B ∘ x) p = 0 ↔ aeval x p = 0 :=
by rw [aeval_algebra_map_apply, ← (algebra_map A B).map_zero, h.eq_iff]

end comm_semiring

end mv_polynomial

namespace subalgebra

open mv_polynomial

section comm_semiring

variables {R A} [comm_semiring R] [comm_semiring A] [algebra R A]

@[simp] lemma mv_polynomial_aeval_coe (S : subalgebra R A) (x : σ → S) (p : mv_polynomial σ R) :
  aeval (λ i, (x i : A)) p = aeval x p :=
by convert aeval_algebra_map_apply A x p

end comm_semiring

end subalgebra
