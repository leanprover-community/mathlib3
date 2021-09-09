/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import data.polynomial.algebra_map
import data.polynomial.div
import topology.metric_space.cau_seq_filter

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `polynomial.continuous_eval₂: `polynomial.eval₂` defines a continuous function.
* `polynomial.continuous_aeval: `polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `polynomial.continuous_at_aeval`,
  `polynomial.continuous_within_at_aeval`, `polynomial.continuous_on_aeval`.
* `polynomial.continuous`:  `polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `polynomial.continuous_at`, `polynomial.continuous_within_at`,
  `polynomial.continuous_on`.
* `polynomial.tendsto_norm_at_top`: `λ x, ∥polynomial.eval (z x) p∥` tends to infinity provided that
  `λ x, ∥z x∥` tends to infinity and `0 < degree p`;
* `polynomial.tendsto_abv_eval₂_at_top`, `polynomial.tendsto_abv_at_top`,
  `polynomial.tendsto_abv_aeval_at_top`: a few versions of the previous statement for
  `is_absolute_value abv` instead of norm.

## Tags

polynomial, continuity
-/

open is_absolute_value filter

namespace polynomial

section topological_ring

variables {R S : Type*} [semiring R] [topological_space R] [topological_ring R]
  (p : polynomial R)

@[continuity]
protected lemma continuous_eval₂ [semiring S] (p : polynomial S) (f : S →+* R) :
  continuous (λ x, p.eval₂ f x) :=
begin
  dsimp only [eval₂_eq_sum, finsupp.sum],
  exact continuous_finset_sum _ (λ c hc, continuous_const.mul (continuous_pow _))
end

@[continuity]
protected lemma continuous : continuous (λ x, p.eval x) :=
p.continuous_eval₂ _

protected lemma continuous_at {a : R} : continuous_at (λ x, p.eval x) a :=
p.continuous.continuous_at

protected lemma continuous_within_at {s a} : continuous_within_at (λ x, p.eval x) s a :=
p.continuous.continuous_within_at

protected lemma continuous_on {s} : continuous_on (λ x, p.eval x) s :=
p.continuous.continuous_on

end topological_ring

section topological_algebra

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  [topological_space A] [topological_ring A]
  (p : polynomial R)

@[continuity]
protected lemma continuous_aeval : continuous (λ x : A, aeval x p) :=
p.continuous_eval₂ _

protected lemma continuous_at_aeval {a : A} : continuous_at (λ x : A, aeval x p) a :=
p.continuous_aeval.continuous_at

protected lemma continuous_within_at_aeval {s a} : continuous_within_at (λ x : A, aeval x p) s a :=
p.continuous_aeval.continuous_within_at

protected lemma continuous_on_aeval {s} : continuous_on (λ x : A, aeval x p) s :=
p.continuous_aeval.continuous_on

end topological_algebra

lemma tendsto_abv_eval₂_at_top {R S k α : Type*} [semiring R] [ring S] [linear_ordered_field k]
  (f : R →+* S) (abv : S → k) [is_absolute_value abv] (p : polynomial R) (hd : 0 < degree p)
  (hf : f p.leading_coeff ≠ 0) {l : filter α} {z : α → S} (hz : tendsto (abv ∘ z) l at_top) :
  tendsto (λ x, abv (p.eval₂ f (z x))) l at_top :=
begin
  revert hf, refine degree_pos_induction_on p hd _ _ _; clear hd p,
  { rintros c - hc,
    rw [leading_coeff_mul_X, leading_coeff_C] at hc,
    simpa [abv_mul abv] using hz.const_mul_at_top ((abv_pos abv).2 hc) },
  { intros p hpd ihp hf,
    rw [leading_coeff_mul_X] at hf,
    simpa [abv_mul abv] using  (ihp hf).at_top_mul_at_top hz },
  { intros p a hd ihp hf,
    rw [add_comm, leading_coeff_add_of_degree_lt (degree_C_le.trans_lt hd)] at hf,
    refine tendsto_at_top_of_add_const_right (abv (-f a)) _,
    refine tendsto_at_top_mono (λ _, abv_add abv _ _) _,
    simpa using ihp hf }
end

lemma tendsto_abv_at_top {R k α : Type*} [ring R] [linear_ordered_field k]
  (abv : R → k) [is_absolute_value abv] (p : polynomial R) (h : 0 < degree p)
  {l : filter α} {z : α → R} (hz : tendsto (abv ∘ z) l at_top) :
  tendsto (λ x, abv (p.eval (z x))) l at_top :=
tendsto_abv_eval₂_at_top _ _ _ h (mt leading_coeff_eq_zero.1 $ ne_zero_of_degree_gt h) hz

lemma tendsto_abv_aeval_at_top {R A k α : Type*} [comm_semiring R] [ring A] [algebra R A]
  [linear_ordered_field k] (abv : A → k) [is_absolute_value abv] (p : polynomial R)
  (hd : 0 < degree p) (h₀ : algebra_map R A p.leading_coeff ≠ 0)
  {l : filter α} {z : α → A} (hz : tendsto (abv ∘ z) l at_top) :
  tendsto (λ x, abv (aeval (z x) p)) l at_top :=
tendsto_abv_eval₂_at_top _ abv p hd h₀ hz

variables {α R : Type*} [normed_ring R] [is_absolute_value (norm : R → ℝ)]

lemma tendsto_norm_at_top (p : polynomial R) (h : 0 < degree p) {l : filter α} {z : α → R}
  (hz : tendsto (λ x, ∥z x∥) l at_top) :
  tendsto (λ x, ∥p.eval (z x)∥) l at_top :=
p.tendsto_abv_at_top norm h hz

lemma exists_forall_norm_le [proper_space R] (p : polynomial R) :
  ∃ x, ∀ y, ∥p.eval x∥ ≤ ∥p.eval y∥ :=
if hp0 : 0 < degree p
then p.continuous.norm.exists_forall_le $ p.tendsto_norm_at_top hp0 tendsto_norm_cocompact_at_top
else ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

end polynomial
