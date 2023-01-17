/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import algebraic_geometry.projective_spectrum.scheme
import ring_theory.graded_algebra.polynomials

/-!
# Projective Space
This file defines projective space over a commutative ring.
-/


variables (R : Type*) [comm_ring R] (σ : Type*)

namespace algebraic_geometry

/--
Projective `σ`-space as a scheme.
-/
noncomputable def projective_space : Scheme :=
Proj.to_Scheme (λ n, mv_polynomial.homogeneous_submodule σ R n)

end algebraic_geometry
