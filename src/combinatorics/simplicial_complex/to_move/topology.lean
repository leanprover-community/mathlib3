import analysis.convex.basic
import topology.sequences

lemma interior_eq_closure_diff_frontier {X : Type _} [topological_space X] (s : set X) :
  interior s = closure s \ frontier s :=
by rw [frontier, set.diff_diff_right, set.diff_self, set.empty_union,
       set.inter_eq_self_of_subset_right interior_subset_closure]

lemma closure_eq_closure_interior {X : Type _} [topological_space X] [sequential_space X]
  [add_comm_group X] [module ℝ X] {A : set X} (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  closure A = closure (interior A) :=
begin
  refine set.subset.antisymm _ (closure_mono interior_subset),
  rintro x,
  obtain ⟨y, hy⟩ := hA₂,
  simp only [mem_closure_iff_seq_limit],
  rintro ⟨z, hzA, hzx⟩,
  use λ n, (1/n.succ : ℝ) • y + (n/n.succ : ℝ) • z n,
  split,
  {
    rintro n,
    --have := (frontier_extreme_to_closure hA₁).2 y (z n) (interior_subset hy) (hzA n),
    sorry
  },
  rw ←zero_add x,
  /-
  apply filter.tendsto.add,
  {
    sorry
  },
  rw ←one_smul _ x,
  refine filter.tendsto.smul _ hzx,-/
  sorry
end
