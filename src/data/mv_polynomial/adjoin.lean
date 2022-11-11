/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro, Anne Baanen
-/

import data.mv_polynomial.basic
import ring_theory.adjoin.basic

/-!
# Multivariate polynomials and adjoining elements to an algebra

This file contains some results on the combination of `mv_polynomial` and `algebra.adjoin`:

 * `mv_polynomial.adjoin_range_X`: adjoining variables to a ring gives `mv_polynomial`
 * `algebra.adjoin_range_eq_range_aeval` and `algebra.adjoin_eq_range`:
   adjoining elements to a ring can be viewed as taking all multivariate polynomials over the ring
   and evaluating them at these elements
-/

universes u v w
variables {R : Type u} {S₁ : Type v} {σ : Type w} [comm_semiring R]

open mv_polynomial set

@[simp] lemma mv_polynomial.adjoin_range_X :
  algebra.adjoin R (range (X : σ → mv_polynomial σ R)) = ⊤ :=
begin
  set S := algebra.adjoin R (range (X : σ → mv_polynomial σ R)),
  refine top_unique (λ p hp, _), clear hp,
  induction p using mv_polynomial.induction_on,
  case h_C : { exact S.algebra_map_mem _ },
  case h_add : p q hp hq { exact S.add_mem hp hq },
  case h_X : p i hp { exact S.mul_mem hp (algebra.subset_adjoin $ mem_range_self _) }
end

variables (R) [comm_semiring S₁] [algebra R S₁] (f : σ → S₁)

lemma algebra.adjoin_range_eq_range_aeval :
  algebra.adjoin R (set.range f) = (mv_polynomial.aeval f).range :=
by simp only [← algebra.map_top, ← mv_polynomial.adjoin_range_X, alg_hom.map_adjoin,
  ← set.range_comp, (∘), mv_polynomial.aeval_X]

theorem algebra.adjoin_eq_range (s : set S₁) :
  algebra.adjoin R s = (mv_polynomial.aeval (coe : s → S₁)).range :=
by rw [← algebra.adjoin_range_eq_range_aeval, subtype.range_coe]
