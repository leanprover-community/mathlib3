/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import topology.metric_space.hausdorff_distance

/-!
# Riesz's lemma

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace F of E, there is a nonzero x such that ∥x - F∥
is at least r * ∥x∥ for any r < 1.
-/

variables {𝕜 : Type*} [normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. -/
lemma riesz_lemma {F : subspace 𝕜 E} (hFc : is_closed (F : set E))
  (hF : ∃ x : E, x ∉ F) {r : ℝ} (hr : r < 1) :
  ∃ x₀ : E, x₀ ∉ F ∧ ∀ y ∈ F, r * ∥x₀∥ ≤ ∥x₀ - y∥ :=
begin
  classical,
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ F := hF,
  let d := metric.inf_dist x F,
  have hFn : (F : set E).nonempty, from ⟨_, F.zero_mem⟩,
  have hdp : 0 < d,
    from lt_of_le_of_ne metric.inf_dist_nonneg (λ heq, hx
    ((metric.mem_iff_inf_dist_zero_of_closed hFc hFn).2 heq.symm)),
  let r' := max r 2⁻¹,
  have hr' : r' < 1, by { simp [r', hr], norm_num },
  have hlt : 0 < r' := lt_of_lt_of_le (by norm_num) (le_max_right r 2⁻¹),
  have hdlt : d < d / r', from lt_div_of_mul_lt hlt ((mul_lt_iff_lt_one_right hdp).2 hr'),
  obtain ⟨y₀, hy₀F, hxy₀⟩ : ∃ y ∈ F, dist x y < d / r' :=
    metric.exists_dist_lt_of_inf_dist_lt hdlt hFn,
  have x_ne_y₀ : x - y₀ ∉ F,
  { by_contradiction h,
    have : (x - y₀) + y₀ ∈ F, from F.add_mem h hy₀F,
    simp only [neg_add_cancel_right, sub_eq_add_neg] at this,
    exact hx this },
  refine ⟨x - y₀, x_ne_y₀, λy hy, le_of_lt _⟩,
  have hy₀y : y₀ + y ∈ F, from F.add_mem hy₀F hy,
  calc
    r * ∥x - y₀∥ ≤ r' * ∥x - y₀∥ : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    ... < d : by { rw ←dist_eq_norm, exact (lt_div_iff' hlt).1 hxy₀ }
    ... ≤ dist x (y₀ + y) : metric.inf_dist_le_dist_of_mem hy₀y
    ... = ∥x - y₀ - y∥ : by { rw [sub_sub, dist_eq_norm] }
end
