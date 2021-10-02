/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.free_module.basic
import linear_algebra.matrix.to_lin
import ring_theory.finiteness

/-!
# Finite and free modules

We provide some instances for finite and free modules.

## Main results

* `module.free.pi` : the product of finitely many free modules is free.
* `module.free.matrix` : the module of (finite) matrices is free.
* `module.free.choose_basis_index.fintype` : If a free module is finite, then any basis is
  finite.
* `module.free.linear_map.free ` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `module.finite.of_basis` : A free module with a basis indexed by a `fintype` is finite.
* `module.free.linear_map.module.finite` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

namespace module.free

section semiring

variables [semiring R]

instance pi {ι : Type*} [fintype ι] {M : ι → Type*} [Π (i : ι), add_comm_group (M i)]
  [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)] : module.free R (Π i, M i) :=
of_basis $ pi.basis $ λ i, choose_basis R (M i)

instance matrix {n : Type*} [fintype n] {m : Type*} [fintype m] :
  module.free R (matrix n m R) :=
of_basis $ matrix.std_basis R n m

end semiring

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

instance [nontrivial R] [module.finite R M] [module.finite R N] : module.free R (M →ₗ[R] N) :=
begin
  classical,
  exact of_equiv
    (linear_map.to_matrix (module.free.choose_basis R M) (module.free.choose_basis R N)).symm,
end

variables {R M}

/-- A free module with a basis indexed by a `fintype` is finite. -/
lemma _root_.module.finite.of_basis {R : Type*} {M : Type*} {ι : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [fintype ι] (b : basis ι R M) : module.finite R M :=
begin
  classical,
  refine ⟨⟨finset.univ.image b, _⟩⟩,
  simp only [set.image_univ, finset.coe_univ, finset.coe_image, basis.span_eq],
end

instance _root_.module.finite.matrix {ι₁ : Type*} [fintype ι₁] {ι₂ : Type*} [fintype ι₂] :
  module.finite R (matrix ι₁ ι₂ R) :=
module.finite.of_basis $ pi.basis $ λ i, pi.basis_fun R _

instance [nontrivial R] [module.finite R M] [module.finite R N] :
  module.finite R (M →ₗ[R] N) :=
begin
  classical,
  have f := (linear_map.to_matrix (choose_basis R M) (choose_basis R N)).symm,
  exact module.finite.of_surjective f.to_linear_map (linear_equiv.surjective f),
end

end comm_ring

section integer

variables [add_comm_group M] [module.finite ℤ M] [module.free ℤ M]
variables [add_comm_group N] [module.finite ℤ N] [module.free ℤ N]

instance : module.finite ℤ (M →+ N) :=
module.finite.equiv (add_monoid_hom_lequiv_int ℤ).symm

instance : module.free ℤ (M →+ N) :=
module.free.of_equiv (add_monoid_hom_lequiv_int ℤ).symm

end integer

end module.free
