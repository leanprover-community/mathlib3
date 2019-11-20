/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/

import topology.metric_space.lipschitz analysis.specific_limits

/-!
# Contracting maps

A Lipschitz continuous self-map with Lipschitz constant `K < 1` is called a *contracting map*.
In this file we prove the Banach fixed point theorem, some explicit estimates on the rate
of convergence, and some properties of the map sending a contracting map to its fixed point.
-/

universes u v

open_locale nnreal topological_space
open filter

variables {α : Type u} {ι : Sort v}

/-- If the iterates `f^[n] x₀` converge to `x` and `f` is continuous at `x`,
then `x` is a fixed point for `f`. -/
lemma fixed_point_of_tendsto_iterate [topological_space α] [t2_space α] {f : α → α} {x : α}
  (hf : continuous_at f x) (hx : ∃ x₀ : α, tendsto (λ n, f^[n] x₀) at_top (𝓝 x)) :
  f x = x :=
begin
  rcases hx with ⟨x₀, hx⟩,
  refine tendsto_nhds_unique at_top_ne_bot _ hx,
  rw [← tendsto_add_at_top_iff_nat 1, funext (assume n, nat.iterate_succ' f n x₀)],
  exact tendsto.comp hf hx
end

/-- A map is said to be `contracting_with K`, if `K < 1` and `f` is `lipschitz_with K`. -/
def contracting_with [metric_space α] (K : ℝ≥0) (f : α → α) :=
(K < 1) ∧ lipschitz_with K f

namespace contracting_with

variables [metric_space α] {K : ℝ≥0} {f : α → α} (hf : contracting_with K f)

include hf

lemma to_lipschitz_with : lipschitz_with K f := hf.2

lemma one_sub_K_pos : (0:ℝ) < 1 - K := sub_pos_of_lt hf.1

lemma dist_inequality (x y) : dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y,
  by rwa [le_div_iff hf.one_sub_K_pos, mul_comm, sub_mul, one_mul, sub_le_iff_le_add],
calc dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) : dist_triangle4_right _ _ _ _
          ... ≤ dist x (f x) + dist y (f y) + K * dist x y :
  add_le_add_left (hf.to_lipschitz_with _ _) _

lemma dist_le_of_fixed_point (x) {y} (hy : f y = y) :
  dist x y ≤ (dist x (f x)) / (1 - K) :=
by simpa only [hy, dist_self, add_zero] using hf.dist_inequality x y

theorem fixed_point_unique' {x y} (hx : f x = x) (hy : f y = y) : x = y :=
dist_le_zero.1 $ by simpa only [hx, dist_self, add_zero, zero_div]
  using hf.dist_le_of_fixed_point x hy

/-- Banach fixed-point theorem, contraction mapping theorem -/
theorem exists_fixed_point [hα : nonempty α] [complete_space α] : ∃x, f x = x :=
let ⟨x₀⟩ := hα in
have cauchy_seq (λ n, f^[n] x₀),
from cauchy_seq_of_le_geometric K (dist x₀ (f x₀)) hf.1 $
  hf.to_lipschitz_with.dist_iterate_succ_le_geometric x₀,
let ⟨x, hx⟩ := cauchy_seq_tendsto_of_complete this in
⟨x, fixed_point_of_tendsto_iterate (hf.to_lipschitz_with.to_continuous.tendsto x) ⟨x₀, hx⟩⟩

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
lemma dist_fixed_point_fixed_point_of_dist_le' (g : α → α)
  {x y} (hx : f x = x) (hy : g y = y) {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) :
  dist x y ≤ C / (1 - K) :=
calc dist x y = dist y x : dist_comm x y
          ... ≤ (dist y (f y)) / (1 - K) : hf.dist_le_of_fixed_point y hx
          ... = (dist (f y) (g y)) / (1 - K) : by rw [hy, dist_comm]
          ... ≤ C / (1 - K) : (div_le_div_right hf.one_sub_K_pos).2 (hfg y)

noncomputable theory

variables [inhabited α] [complete_space α]

/-- The unique fixed point of a contracting map. -/
protected def fixed_point : α := classical.some hf.exists_fixed_point

/-- The point provided by `contracting_with.fixed_point` is actually a fixed point. -/
lemma fixed_point_is_fixed : f hf.fixed_point = hf.fixed_point :=
classical.some_spec hf.exists_fixed_point

lemma fixed_point_unique {x} (hx : f x = x) : x = hf.fixed_point :=
hf.fixed_point_unique' hx hf.fixed_point_is_fixed

lemma dist_fixed_point_le (x) : dist x hf.fixed_point ≤ (dist x (f x)) / (1 - K) :=
hf.dist_le_of_fixed_point x hf.fixed_point_is_fixed

/-- Aposteriori estimates on the convergence of iterates to the fixed point. -/
lemma aposteriori_dist_iterate_fixed_point_le (x n) :
  dist (f^[n] x) hf.fixed_point ≤ (dist (f^[n] x) (f^[n+1] x)) / (1 - K) :=
by { rw [nat.iterate_succ'], apply hf.dist_fixed_point_le }

lemma apriori_dist_iterate_fixed_point_le (x n) :
  dist (f^[n] x) hf.fixed_point ≤ (dist x (f x)) * K^n / (1 - K) :=
le_trans (hf.aposteriori_dist_iterate_fixed_point_le x n) $
  (div_le_div_right hf.one_sub_K_pos).2 $
    hf.to_lipschitz_with.dist_iterate_succ_le_geometric x n

lemma fixed_point_lipschitz_in_map {g : α → α} (hg : contracting_with K g)
  {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) :
  dist hf.fixed_point hg.fixed_point ≤ C / (1 - K) :=
hf.dist_fixed_point_fixed_point_of_dist_le' g hf.fixed_point_is_fixed hg.fixed_point_is_fixed hfg

end contracting_with
