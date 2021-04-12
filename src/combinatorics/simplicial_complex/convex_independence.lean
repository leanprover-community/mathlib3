import data.finset.sort
import data.matrix.notation
import linear_algebra.basis
import linear_algebra.affine_space.basic
import linear_algebra.affine_space.combination
import linear_algebra.affine_space.independent
import analysis.convex.basic

open_locale affine

variables {E ι : Type*} [add_comm_group E] [vector_space ℝ E]

/-- An indexed family is said to be convex independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def convex_independent (p : ι → E) :
  Prop :=
∀ (s : finset ι) (x : ι), p x ∈ convex_hull (p '' s) → x ∈ s

lemma convex_independent_of_affine_independent {p : ι → E} (hp : affine_independent ℝ p) :
  convex_independent p := sorry
