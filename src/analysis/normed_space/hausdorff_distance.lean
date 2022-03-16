/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.hausdorff_distance

open_locale topological_space
open metric set

lemma closed_ball_inf_dist_compl_subset_closure' {E : Type*} [semi_normed_group E]
  [normed_space ℝ E] {x : E} {s : set E} (hx : s ∈ 𝓝 x) (hs : s ≠ univ) :
  closed_ball x (inf_dist x sᶜ) ⊆ closure s :=
begin
  have hne : sᶜ.nonempty, from nonempty_compl.2 hs,
  have hpos : 0 < inf_dist x sᶜ,
  { rwa [← inf_dist_eq_closure, ← is_closed_closure.not_mem_iff_inf_dist_pos hne.closure,
      closure_compl, mem_compl_iff, not_not, mem_interior_iff_mem_nhds] },
  rw ← closure_ball x hpos,
  apply closure_mono,
  rw [← le_eq_subset, ← is_compl_compl.disjoint_right_iff],
  exact disjoint_ball_inf_dist
end

lemma closed_ball_inf_dist_compl_subset_closure {E : Type*} [normed_group E] [normed_space ℝ E]
  {x : E} {s : set E} (hx : x ∈ s) (hs : s ≠ univ) :
  closed_ball x (inf_dist x sᶜ) ⊆ closure s :=
begin
  by_cases hx' : x ∈ closure sᶜ,
  { rw [mem_closure_iff_inf_dist_zero (nonempty_compl.2 hs)] at hx',
    simpa [hx'] using subset_closure hx },
  { rw [closure_compl, mem_compl_iff, not_not, mem_interior_iff_mem_nhds] at hx',
    exact closed_ball_inf_dist_compl_subset_closure' hx' hs }
end
