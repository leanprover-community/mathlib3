/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.basis
import logic.small

/-!

# Free modules

TODO

-/

universes u v w z

variables (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [module R M]

/-- `finite_free R M` is the statement that the `R`-module `R` is free of finite rank.-/
class module.free : Prop :=
(exists_basis [] : nonempty (Σ (I : Type v), basis I R M))

lemma module.free_def [small.{w} M] : module.free R M ↔ ∃ (I : Type w), nonempty (basis I R M) :=
⟨ λ h, ⟨shrink (set.range h.exists_basis.some.2),
    ⟨(basis.reindex_range h.exists_basis.some.2).reindex (equiv_shrink _)⟩⟩,
  λ h, ⟨(nonempty_sigma.2 h).map $ λ ⟨i, b⟩, ⟨set.range b, b.reindex_range⟩⟩⟩

lemma module.free_iff_set : module.free R M ↔ ∃ (S : set M), nonempty (basis S R M) :=
⟨λ h, ⟨set.range h.exists_basis.some.2, ⟨basis.reindex_range h.exists_basis.some.2⟩⟩,
    λ ⟨S, hS⟩, ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

variables {R M}

lemma module.free.of_basis {ι : Type w} (b : basis ι R M) : module.free R M :=
(module.free_def R M).2 ⟨set.range b, ⟨b.reindex_range⟩⟩

namespace module.free

variables (R M) [module.free R M] (N : Type z) [add_comm_monoid N] [module R N]

/-- If `[finite_free R M]` then `choose_basis_index R M` is the `ι` which indexes the basis
  `ι → M`. -/
@[nolint has_inhabited_instance] def choose_basis_index := (exists_basis R M).some.1

/-- If `[finite_free R M]` then `choose_basis : ι → M` is the basis.
Here `ι = choose_basis_index R M`. -/
noncomputable def choose_basis : basis (choose_basis_index R M) R M := (exists_basis R M).some.2

/-- The isomorphism `M ≃ₗ[R] (choose_basis_index R M →₀ R)`. -/
noncomputable def repr : M ≃ₗ[R] (choose_basis_index R M →₀ R) := (choose_basis R M).repr

@[priority 100]
instance no_zero_smul_divisors [no_zero_divisors R] : no_zero_smul_divisors R M :=
basis.no_zero_smul_divisors $ choose_basis R M

variables {R M N}

lemma of_equiv (e : M ≃ₗ[R] N) : module.free R N :=
of_basis $ (choose_basis R M).map e

variables (R M N)

instance of_finsupp {ι : Type v} : module.free R (ι →₀ R) :=
of_basis (basis.of_repr (linear_equiv.refl _ _))

instance of_fun {ι : Type v} [fintype ι] : module.free R (ι → R) :=
of_equiv (basis.of_repr $ linear_equiv.refl _ _).equiv_fun

instance of_prod [module.free R N] : module.free R (M × N) :=
of_basis $ (choose_basis R M).prod (choose_basis R N)

instance of_self : module.free R R := of_basis $ basis.singleton unit R

lemma of_zero [subsingleton N] : module.free R N :=
of_basis $ basis.empty _ not_nonempty_pempty

instance of_vector_space (K : Type u) (V : Type v) [division_ring K] [add_comm_group V]
  [module K V] : module.free K V :=
of_basis (basis.of_vector_space K V)

end module.free
