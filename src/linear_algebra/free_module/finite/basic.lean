/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.dimension
import linear_algebra.free_module.basic
import ring_theory.finiteness

/-!
# Finite and free modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide some instances for finite and free modules.

## Main results

* `module.free.choose_basis_index.fintype` : If a free module is finite, then any basis is
  finite.
* `module.free.linear_map.free ` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `module.free.linear_map.module.finite` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

namespace module.free

section ring

variables [ring R] [add_comm_group M] [module R M] [module.free R M]

/-- If a free module is finite, then any basis is finite. -/
noncomputable
instance [nontrivial R] [module.finite R M] :
  fintype (module.free.choose_basis_index R M) :=
begin
  obtain ⟨h⟩ := id ‹module.finite R M›,
  choose s hs using h,
  exact basis_fintype_of_finite_spans ↑s hs (choose_basis _ _),
end

end ring

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M] [module.free R M]
variables [add_comm_group N] [module R N] [module.free R N]

variables {R}

/-- A free module with a basis indexed by a `fintype` is finite. -/
lemma _root_.module.finite.of_basis {R M ι : Type*} [comm_ring R] [add_comm_group M] [module R M]
  [finite ι] (b : basis ι R M) : module.finite R M :=
begin
  casesI nonempty_fintype ι,
  classical,
  refine ⟨⟨finset.univ.image b, _⟩⟩,
  simp only [set.image_univ, finset.coe_univ, finset.coe_image, basis.span_eq],
end

instance _root_.module.finite.matrix {ι₁ ι₂ : Type*} [finite ι₁] [finite ι₂] :
  module.finite R (matrix ι₁ ι₂ R) :=
by { casesI nonempty_fintype ι₁, casesI nonempty_fintype ι₂,
  exact module.finite.of_basis (pi.basis $ λ i, pi.basis_fun R _) }

end comm_ring

end module.free
