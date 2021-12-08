/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import ring_theory.adjoin.basic
import data.mv_polynomial.rename
import data.polynomial.algebra_map

/-!
# Adjoining elements to form subalgebras: relation to polynomials

In this file we prove a few results representing `algebra.adjoin R s` as the range of
`mv_polynomial.aeval`.

## Tags

adjoin, algebra, polynomials
-/

universes u v w

namespace algebra

open subsemiring submodule
variables (R : Type u) {A : Type v} (s : set A) [comm_semiring R] [comm_semiring A] [algebra R A]

lemma adjoin_range_eq_range_aeval {σ : Type*} (f : σ → A) :
  adjoin R (set.range f) = (mv_polynomial.aeval f).range :=
by simp only [← algebra.map_top, ← mv_polynomial.adjoin_range_X, alg_hom.map_adjoin,
  ← set.range_comp, (∘), mv_polynomial.aeval_X]

theorem adjoin_eq_range : adjoin R s = (mv_polynomial.aeval (coe : s → A)).range :=
by rw [← adjoin_range_eq_range_aeval, subtype.range_coe]

end algebra
