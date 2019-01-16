/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Analytic facts about polynomials.
-/

import analysis.topology.topological_structures data.polynomial

lemma polynomial.continuous_eval {α} [comm_semiring α] [decidable_eq α] [topological_space α]
  [topological_semiring α] (p : polynomial α) : continuous (λ x, p.eval x) :=
begin
  apply p.induction,
  { convert continuous_const,
    ext, show polynomial.eval x 0 = 0, from rfl },
  { intros a b f haf hb hcts,
    simp only [polynomial.eval_add],
    refine continuous_add _ hcts,
    have : ∀ x, finsupp.sum (finsupp.single a b) (λ (e : ℕ) (a : α), a * x ^ e) = b * x ^a,
      from λ x, finsupp.sum_single_index (by simp),
    convert continuous_mul _ _,
    { ext, apply this },
    { apply_instance },
    { apply continuous_const },
    { apply continuous_pow }}
end