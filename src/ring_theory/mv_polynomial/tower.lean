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

variables (R S A B : Type*) {σ : Type*}

namespace mv_polynomial

section semiring
variables [comm_semiring R] [comm_semiring S] [comm_semiring A]
variables [algebra R S] [algebra S A] [algebra R A]
variables [is_scalar_tower R S A]

variables {B}
theorem aeval_apply (x : σ → A) (p : mv_polynomial σ R) : aeval x p =
  aeval x (map (algebra_map R S) p) :=
by rw [mv_polynomial.aeval_def, mv_polynomial.aeval_def, mv_polynomial.eval₂_map,
  is_scalar_tower.algebra_map_eq R S A]

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

lemma algebra_map_aeval (x : σ → A) (p : mv_polynomial σ R) :
  algebra_map A B (mv_polynomial.aeval x p) = aeval (algebra_map A B ∘ x) p :=
by rw [mv_polynomial.aeval_def, mv_polynomial.aeval_def, ← mv_polynomial.coe_eval₂_hom,
  mv_polynomial.map_eval₂_hom, ←is_scalar_tower.algebra_map_eq, mv_polynomial.coe_eval₂_hom]

lemma aeval_eq_zero_of_aeval_algebra_map_eq_zero {x : σ → A} {p : mv_polynomial σ R}
  (h : function.injective (algebra_map A B))
  (hp : aeval (algebra_map A B ∘ x) p = 0) :
  aeval x p = 0 :=
begin
  rw [← algebra_map_aeval, ← (algebra_map A B).map_zero] at hp,
  exact h hp,
end

lemma aeval_eq_zero_of_aeval_algebra_map_eq_zero_field {R A B : Type*} [comm_semiring R] [field A]
  [comm_semiring B] [nontrivial B] [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]
  {x : σ → A} {p : mv_polynomial σ R} (h : aeval (algebra_map A B ∘ x) p = 0) :
  aeval x p = 0 :=
aeval_eq_zero_of_aeval_algebra_map_eq_zero R A B (algebra_map A B).injective h

end comm_semiring

end mv_polynomial

namespace subalgebra

namespace mv_polynomial

section comm_semiring

variables {R A} [comm_semiring R] [comm_semiring S] [comm_semiring A] [algebra R A]

@[simp] lemma aeval_coe (S : subalgebra R A) (x : σ → S) (p : mv_polynomial σ R) :
  mv_polynomial.aeval (λ i, (x i : A)) p = mv_polynomial.aeval x p :=
(mv_polynomial.algebra_map_aeval R S A x p).symm

end comm_semiring

end mv_polynomial

end subalgebra
