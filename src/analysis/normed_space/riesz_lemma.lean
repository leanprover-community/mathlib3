/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo

Riesz's lemma on a normed space over a normed field.
-/
import analysis.normed_space.basic
import topology.metric_space.hausdorff_distance

variables {𝕜 : Type*} [normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. -/
lemma riesz_lemma {F : subspace 𝕜 E} (hFc : is_closed F.carrier)
  (hF : ∃ x : E, x ∉ F) {r : ℝ} (hr : r < 1) :
  ∃ x₀ : E, ∀ y : F, r * ∥x₀∥ ≤ ∥x₀ - y∥ :=
or.cases_on (le_or_lt r 0)
(λ hle, ⟨0, λ _, by {rw [norm_zero, mul_zero], exact norm_nonneg _}⟩)
(λ hlt,
let ⟨x, hx⟩ := hF in
let d := metric.inf_dist x F in
have hFn : F.carrier ≠ ∅, from set.ne_empty_of_mem (submodule.zero F),
have hdp : 0 < d,
  from lt_of_le_of_ne metric.inf_dist_nonneg $ λ heq, hx
  ((metric.mem_iff_inf_dist_zero_of_closed hFc hFn).2 heq.symm),
have hdlt : d < d / r,
  from lt_div_of_mul_lt hlt ((mul_lt_iff_lt_one_right hdp).2 hr),
let ⟨y₀, hy₀F, hxy₀⟩ := metric.exists_dist_lt_of_inf_dist_lt hdlt hFn in
⟨x - y₀, λ y,
have hy₀y : (y₀ + y) ∈ F.carrier, from F.add hy₀F y.property,
le_of_lt $ calc
∥x - y₀ - y∥ = dist x (y₀ + y) : by { rw [sub_sub, dist_eq_norm] }
...          ≥ d : metric.inf_dist_le_dist_of_mem hy₀y
...          > _ : by { rw ←dist_eq_norm, exact (lt_div_iff' hlt).1 hxy₀ }⟩)
