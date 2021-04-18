import topology.basic

lemma interior_eq_closure_diff_frontier {X : Type _} [topological_space X] (s : set X) :
  interior s = closure s \ frontier s :=
by rw [frontier, set.diff_diff_right, set.diff_self, set.empty_union,
       set.inter_eq_self_of_subset_right interior_subset_closure]
