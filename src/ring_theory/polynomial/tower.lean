/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.algebra.tower
import data.polynomial.algebra_map

/-!
# Algebra towers for polynomial

This file proves some basic results about the algebra tower structure for the type `polynomial R`.

This structure itself is provided elsewhere as `polynomial.is_scalar_tower`
-/

universes u v w u₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace is_scalar_tower

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

variables (R S A) {B}
theorem aeval_apply (x : A) (p : polynomial R) : polynomial.aeval x p =
  polynomial.aeval x (polynomial.map (algebra_map R S) p) :=
by rw [polynomial.aeval_def, polynomial.aeval_def, polynomial.eval₂_map, algebra_map_eq R S A]

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

lemma algebra_map_aeval (x : A) (p : polynomial R) :
  algebra_map A B (polynomial.aeval x p) = polynomial.aeval (algebra_map A B x) p :=
by rw [polynomial.aeval_def, polynomial.aeval_def, polynomial.hom_eval₂,
  ←is_scalar_tower.algebra_map_eq]

lemma aeval_eq_zero_of_aeval_algebra_map_eq_zero {x : A} {p : polynomial R}
  (h : function.injective (algebra_map A B)) (hp : polynomial.aeval (algebra_map A B x) p = 0) :
  polynomial.aeval x p = 0 :=
begin
  rw [← algebra_map_aeval, ← (algebra_map A B).map_zero] at hp,
  exact h hp,
end

lemma aeval_eq_zero_of_aeval_algebra_map_eq_zero_field {R A B : Type*} [comm_semiring R] [field A]
  [comm_semiring B] [nontrivial B] [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]
  {x : A} {p : polynomial R} (h : polynomial.aeval (algebra_map A B x) p = 0) :
  polynomial.aeval x p = 0 :=
aeval_eq_zero_of_aeval_algebra_map_eq_zero R A B (algebra_map A B).injective h

end comm_semiring

end is_scalar_tower

namespace subalgebra

open is_scalar_tower

section comm_semiring

variables (R) {S A} [comm_semiring R] [comm_semiring S] [comm_semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

@[simp] lemma aeval_coe {S : subalgebra R A} {x : S} {p : polynomial R} :
  polynomial.aeval (x : A) p = polynomial.aeval x p :=
(algebra_map_aeval R S A x p).symm

end comm_semiring

end subalgebra
