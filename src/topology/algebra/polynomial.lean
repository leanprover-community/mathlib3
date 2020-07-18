/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Analytic facts about polynomials.
-/
import topology.algebra.ring
import data.polynomial.div
import data.real.cau_seq

open polynomial is_absolute_value

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma polynomial.tendsto_infinity {α β : Type*} [comm_ring α] [discrete_linear_ordered_field β]
  (abv : α → β) [is_absolute_value abv] {p : polynomial α} (h : 0 < degree p) :
  ∀ x : β, ∃ r > 0, ∀ z : α, r < abv z → x < abv (p.eval z) :=
degree_pos_induction_on p h
  (λ a ha x, ⟨max (x / abv a) 1, (lt_max_iff.2 (or.inr zero_lt_one)), λ z hz,
    by simp [max_lt_iff, div_lt_iff' ((abv_pos abv).2 ha), abv_mul abv] at *; tauto⟩)
  (λ p hp ih x, let ⟨r, hr0, hr⟩ := ih x in
    ⟨max r 1, lt_max_iff.2 (or.inr zero_lt_one), λ z hz, by rw [eval_mul, eval_X, abv_mul abv];
        calc x < abv (p.eval z) : hr _ (max_lt_iff.1 hz).1
        ... ≤ abv (eval z p) * abv z : le_mul_of_ge_one_right
          (abv_nonneg _ _) (max_le_iff.1 (le_of_lt hz)).2⟩)
  (λ p a hp ih x, let ⟨r, hr0, hr⟩ := ih (x + abv a) in
    ⟨r, hr0, λ z hz, by rw [eval_add, eval_C, ← sub_neg_eq_add];
      exact lt_of_lt_of_le (lt_sub_iff_add_lt.2
        (by rw abv_neg abv; exact (hr z hz)))
        (le_trans (le_abs_self _) (abs_abv_sub_le_abv_sub _ _ _))⟩)

lemma polynomial.continuous_eval {α} [comm_semiring α] [topological_space α]
  [topological_semiring α] (p : polynomial α) : continuous (λ x, p.eval x) :=
begin
  apply p.induction,
  { convert continuous_const,
    ext, show polynomial.eval x 0 = 0, from rfl },
  { intros a b f haf hb hcts,
    simp only [polynomial.eval_add],
    refine continuous.add _ hcts,
    have : ∀ x, finsupp.sum (finsupp.single a b) (λ (e : ℕ) (a : α), a * x ^ e) = b * x ^a,
      from λ x, finsupp.sum_single_index (by simp),
    convert continuous.mul _ _,
    { ext, apply this },
    { apply_instance },
    { apply continuous_const },
    { apply continuous_pow }}
end
