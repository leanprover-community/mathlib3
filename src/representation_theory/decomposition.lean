/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import linear_algebra.direct_sum_module
import algebra.direct_sum

universes u v w
open_locale direct_sum classical big_operators direct_sum
open classical linear_map
noncomputable theory
/-!
# Decompositions of modules

This file defines the concept of a "decomposition" for modules.

-/


namespace module
variables (ι : Type u)
variables (R : Type v) [semiring R] (M : Type w) [add_comm_monoid M] [module R M]

structure decomposition : Type (max u v w) :=
(factors : ι → submodule R M)
(factors_ind : complete_lattice.independent factors)
(factors_supr : supr factors = ⊤)

namespace decomposition
variables {ι R M}

def equiv (D : decomposition ι R M) :
  (⨁ i : ι, D.factors i) ≃ₗ[R] M

end decomposition
end module
