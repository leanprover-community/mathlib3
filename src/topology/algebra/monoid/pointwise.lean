/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.algebra.monoid.basic
import order.filter.pointwise

/-!
# Pointwise filter operations on a topological monoid

In this file we prove several lemmas about multiplication of filters on a topological monoid.
-/

open_locale filter topological_space pointwise
open filter

variables {M : Type*} [topological_space M]

@[to_additive] lemma le_nhds_mul [has_mul M] [has_continuous_mul M] (a b : M) :
  𝓝 a * 𝓝 b ≤ 𝓝 (a * b) :=
by { rw [← map₂_mul, ← map_uncurry_prod, ← nhds_prod_eq], exact continuous_mul.tendsto _ }

variables [mul_one_class M] [has_continuous_mul M]

@[simp, to_additive] lemma nhds_one_mul_nhds (a : M) : 𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
((le_nhds_mul _ _).trans_eq $ congr_arg _ (one_mul a)).antisymm $
  le_mul_of_one_le_left' $ pure_le_nhds 1

@[simp, to_additive] lemma nhds_mul_nhds_one (a : M) : 𝓝 a * 𝓝 1 = 𝓝 a :=
((le_nhds_mul _ _).trans_eq $ congr_arg _ (mul_one a)).antisymm $
  le_mul_of_one_le_right' $ pure_le_nhds 1
