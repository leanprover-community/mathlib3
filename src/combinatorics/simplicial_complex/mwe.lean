import tactic
import analysis.convex.topology
import linear_algebra.affine_space.affine_subspace

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E}

def intrinsic_frontier (A : set E) :
  set E :=
coe '' (frontier {x : affine_span ℝ A | ↑x ∈ A})

def intrinsic_interior (A : set E) :
  set E :=
coe '' (interior {x : affine_span ℝ A | ↑x ∈ A})

def intrinsic_closure (A : set E) :
  set E :=
coe '' (closure {x : affine_span ℝ A | ↑x ∈ A})
