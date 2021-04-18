import tactic
import analysis.convex.topology
import linear_algebra.affine_space.affine_subspace

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E}

lemma closure_eq_intrinsic_closure :
  closure A = coe '' (closure {x : affine_span ℝ A | ↑x ∈ A}) := sorry
