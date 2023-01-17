import algebraic_geometry.projective_spectrum.scheme
import ring_theory.graded_algebra.polynomials

variables (R : Type*) [comm_ring R] (σ : Type*)

namespace algebraic_geometry

/--
Projective `σ`-space as a scheme.
-/
noncomputable def projective_space : Scheme :=
Proj.to_Scheme (λ n, mv_polynomial.homogeneous_submodule σ R n)

end algebraic_geometry
