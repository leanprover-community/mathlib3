/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.topology
import topology.sequences

lemma interior_eq_closure_diff_frontier {X : Type _} [topological_space X] (s : set X) :
  interior s = closure s \ frontier s :=
by rw [frontier, set.diff_diff_right, set.diff_self, set.empty_union,
       set.inter_eq_self_of_subset_right interior_subset_closure]
