/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Analytic facts about polynomials.
-/
import data.polynomial.algebra_map
import data.polynomial.div
import topology.metric_space.cau_seq_filter

open is_absolute_value filter

namespace polynomial

section topological_semiring

variables {R : Type*} [semiring R] [topological_space R] [topological_semiring R]
  (p : polynomial R)

@[continuity]
protected lemma continuous : continuous (λ x, p.eval x) :=
begin
  dsimp only [eval_eq_sum, finsupp.sum],
  exact continuous_finset_sum _ (λ c hc, continuous_const.mul (continuous_pow _))
end

protected lemma continuous_at {a : R} : continuous_at (λ x, p.eval x) a :=
p.continuous.continuous_at

protected lemma continuous_within_at {s a} : continuous_within_at (λ x, p.eval x) s a :=
p.continuous.continuous_within_at

protected lemma continuous_on {s} : continuous_on (λ x, p.eval x) s :=
p.continuous.continuous_on

end topological_semiring

section topological_algebra

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  [topological_space A] [topological_semiring A]
  (p : polynomial R)

@[continuity]
protected lemma continuous_aeval : continuous (λ x : A, aeval x p) :=
begin
  dsimp only [aeval_def, eval₂_eq_sum, finsupp.sum],
  exact continuous_finset_sum _ (λ c hc, continuous_const.mul (continuous_pow _))
end

protected lemma continuous_at_aeval {a : A} : continuous_at (λ x : A, aeval x p) a :=
p.continuous_aeval.continuous_at

protected lemma continuous_within_at_aeval {s a} : continuous_within_at (λ x : A, aeval x p) s a :=
p.continuous_aeval.continuous_within_at

protected lemma continuous_on_aeval {s} : continuous_on (λ x : A, aeval x p) s :=
p.continuous_aeval.continuous_on

end topological_algebra

lemma abv_tendsto_at_top {R k : Type*} [comm_ring R] [discrete_linear_ordered_field k]
  (abv : R → k) [is_absolute_value abv] (p : polynomial R) (h : 0 < degree p) :
  tendsto (λ z, abv (p.eval z)) (comap abv at_top) at_top :=
begin
  have : tendsto abv (comap abv at_top) at_top := map_comap_le,
  apply degree_pos_induction_on p h; clear h p,
  { intros c hc,
    simpa [abv_mul abv] using tendsto_at_top_mul_left' ((abv_pos abv).2 hc) this },
  { intros p hpd ihp,
    simpa [abv_mul abv] using tendsto_at_top_mul_at_top ihp this },
  { intros p a hp ihp,
    refine tendsto_at_top_of_add_const_right (abv (-a)) _,
    refine tendsto_at_top_mono (λ _, abv_add abv _ _) _,
    simpa }
end

-- Lean fails to unify `normed_comm_ring → comm_ring → ring` with
--  `normed_comm_ring → normed_ring → ring`
local attribute [instance, priority 200] comm_ring.to_ring normed_comm_ring.to_comm_ring

variables {R : Type*} [normed_comm_ring R] [is_absolute_value (norm : R → ℝ)]

lemma norm_tendsto_at_top (p : polynomial R) (h : 0 < degree p) :
  tendsto (λ z, ∥p.eval z∥) (comap norm at_top) at_top :=
p.abv_tendsto_at_top norm h

lemma exists_forall_norm_le (p : polynomial R) :
  ∃ x, ∀ y, ∥p.eval x∥ ≤ ∥p.eval y∥ :=
if hp0 : 0 < degree p
then p.continuous.norm.exists_forall_le $ (p.norm_tendsto_at_top hp0).mono_left $
  tendsto_norm_cocompact_at_top.le_comap
else ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

end polynomial
