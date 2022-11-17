/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yuyang Zhao
-/

import algebra.algebra.tower
import data.polynomial.algebra_map

/-!
# Algebra towers for polynomial

This file proves some basic results about the algebra tower structure for the type `R[X]`.

This structure itself is provided elsewhere as `polynomial.is_scalar_tower`

When you update this file, you can also try to make a corresponding update in
`ring_theory.mv_polynomial.tower`.
-/

open_locale polynomial

variables (R A B : Type*)

namespace polynomial

section semiring
variables [comm_semiring R] [comm_semiring A] [semiring B]
variables [algebra R A] [algebra A B] [algebra R B]
variables [is_scalar_tower R A B]

variables {R B}

@[simp] theorem aeval_map_algebra_map (x : B) (p : R[X]) :
  aeval x (map (algebra_map R A) p) = aeval x p :=
by rw [aeval_def, aeval_def, eval₂_map, is_scalar_tower.algebra_map_eq R A B]

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

variables {R A}

lemma aeval_algebra_map_apply (x : A) (p : R[X]) :
  aeval (algebra_map A B x) p = algebra_map A B (aeval x p) :=
by rw [aeval_def, aeval_def, hom_eval₂, ←is_scalar_tower.algebra_map_eq]

@[simp] lemma aeval_algebra_map_eq_zero_iff [no_zero_smul_divisors A B] [nontrivial B]
  (x : A) (p : R[X]) :
  aeval (algebra_map A B x) p = 0 ↔ aeval x p = 0 :=
by rw [aeval_algebra_map_apply, algebra.algebra_map_eq_smul_one, smul_eq_zero,
  iff_false_intro (one_ne_zero' B), or_false]

variables {B}

lemma aeval_algebra_map_eq_zero_iff_of_injective
  {x : A} {p : R[X]}
  (h : function.injective (algebra_map A B)) :
  aeval (algebra_map A B x) p = 0 ↔ aeval x p = 0 :=
by rw [aeval_algebra_map_apply, ← (algebra_map A B).map_zero, h.eq_iff]

end comm_semiring

end polynomial

namespace subalgebra

open polynomial

section comm_semiring

variables {R A} [comm_semiring R] [comm_semiring A] [algebra R A]

@[simp] lemma aeval_coe (S : subalgebra R A) (x : S) (p : R[X]) :
  aeval (x : A) p = aeval x p :=
aeval_algebra_map_apply A x p

end comm_semiring

end subalgebra
