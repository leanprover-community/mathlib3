import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import algebra.module.linear_map
import analysis.convex.topology

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}

namespace affine

def intrinsic_frontier (A : set E) :
  set E :=
frontier (A : set (affine_span ℝ A).carrier)

def intrinsic_interior (A : set E) :
  set

end affine
