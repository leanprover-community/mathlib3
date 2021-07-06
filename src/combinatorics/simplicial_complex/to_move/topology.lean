/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.topology
import combinatorics.simplicial_complex.extreme
import topology.sequences

lemma interior_eq_closure_diff_frontier {X : Type _} [topological_space X] (s : set X) :
  interior s = closure s \ frontier s :=
by rw [frontier, set.diff_diff_right, set.diff_self, set.empty_union,
       set.inter_eq_self_of_subset_right interior_subset_closure]

lemma closure_eq_closure_interior {E : Type _} [add_comm_group E] [module ℝ E] [topological_space E]
  [sequential_space E] [topological_add_group E] [has_continuous_smul ℝ E] {A : set E}
  (hAconv : convex A) (hAnemp : (interior A).nonempty) :
  closure A = closure (interior A) :=
begin
  --have := hAconv.interior,
  refine set.subset.antisymm (λ x hx, _) (closure_mono interior_subset),
  obtain ⟨y, hy⟩ := hAnemp,
  rw mem_closure_iff_seq_limit at ⊢ hx,
  obtain ⟨z, hzA, hzx⟩ := hx,
  use λ n, (1/n.succ : ℝ) • y + (1 - 1/n.succ : ℝ) • z n,
  split,
  {
    rintro n,
    have := (frontier_extreme_to_closure hAconv).2 y (z n) (interior_subset hy) (hzA n),
    sorry
  },
  rw ←zero_add x,
  apply filter.tendsto.add,
  {
    sorry
  },
  rw ←one_smul _ x,
  refine filter.tendsto.smul _ hzx,
  rw ←zero_sub x,
  sorry
end
