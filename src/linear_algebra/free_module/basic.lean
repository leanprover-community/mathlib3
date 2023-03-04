/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.direct_sum.finsupp
import logic.small.basic
import linear_algebra.std_basis
import linear_algebra.finsupp_vector_space

/-!

# Free modules

We introduce a class `module.free R M`, for `R` a `semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `finsupp.total_id_surjective` to prove that any module is the quotient of a free module.

## Main definition

* `module.free R M` : the class of free `R`-modules.

-/

universes u v w z

variables {ι : Type*} (R : Type u) (M : Type v) (N : Type z)

open_locale tensor_product direct_sum big_operators

section basic

variables [semiring R] [add_comm_monoid M] [module R M]

/-- `module.free R M` is the statement that the `R`-module `M` is free.-/
class module.free : Prop :=
(exists_basis [] : nonempty (Σ (I : Type v), basis I R M))

/- If `M` fits in universe `w`, then freeness is equivalent to existence of a basis in that
universe.

Note that if `M` does not fit in `w`, the reverse direction of this implication is still true as
`module.free.of_basis`. -/
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

end basic

namespace module.free

section semiring

variables (R M) [semiring R] [add_comm_monoid M] [module R M] [module.free R M]
variables [add_comm_monoid N] [module R N]

/-- If `module.free R M` then `choose_basis_index R M` is the `ι` which indexes the basis
  `ι → M`. -/
def choose_basis_index := (exists_basis R M).some.1

/-- If `module.free R M` then `choose_basis : ι → M` is the basis.
Here `ι = choose_basis_index R M`. -/
noncomputable def choose_basis : basis (choose_basis_index R M) R M := (exists_basis R M).some.2

/-- The isomorphism `M ≃ₗ[R] (choose_basis_index R M →₀ R)`. -/
noncomputable def repr : M ≃ₗ[R] (choose_basis_index R M →₀ R) := (choose_basis R M).repr

/-- The universal property of free modules: giving a functon `(choose_basis_index R M) → N`, for `N`
an `R`-module, is the same as giving an `R`-linear map `M →ₗ[R] N`.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
See library note [bundled maps over different rings]. -/
noncomputable def constr {S : Type z} [semiring S] [module S N] [smul_comm_class R S N] :
  ((choose_basis_index R M) → N) ≃ₗ[S] M →ₗ[R] N := basis.constr (choose_basis R M) S

@[priority 100]
instance no_zero_smul_divisors [no_zero_divisors R] : no_zero_smul_divisors R M :=
let ⟨⟨_, b⟩⟩ := exists_basis R M in b.no_zero_smul_divisors

instance [nontrivial M] : nonempty (module.free.choose_basis_index R M) :=
(module.free.choose_basis R M).index_nonempty

variables {R M N}

lemma of_equiv (e : M ≃ₗ[R] N) : module.free R N :=
of_basis $ (choose_basis R M).map e

/-- A variation of `of_equiv`: the assumption `module.free R P` here is explicit rather than an
instance. -/
lemma of_equiv' {P : Type v} [add_comm_monoid P] [module R P] (h : module.free R P)
  (e : P ≃ₗ[R] N) : module.free R N :=
of_equiv e

variables (R M N)

/-- The module structure provided by `semiring.to_module` is free. -/
instance self : module.free R R := of_basis (basis.singleton unit R)

instance prod [module.free R N] : module.free R (M × N) :=
of_basis $ (choose_basis R M).prod (choose_basis R N)

/-- The product of finitely many free modules is free. -/
instance pi (M : ι → Type*) [finite ι] [Π (i : ι), add_comm_monoid (M i)]
  [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)] : module.free R (Π i, M i) :=
let ⟨_⟩ := nonempty_fintype ι in by exactI (of_basis $ pi.basis $ λ i, choose_basis R (M i))

/-- The module of finite matrices is free. -/
instance matrix {m n : Type*} [finite m] [finite n] : module.free R (matrix m n M) :=
module.free.pi R _

variables (ι)

/-- The product of finitely many free modules is free (non-dependent version to help with typeclass
search). -/
instance function [finite ι] : module.free R (ι → M) := free.pi _ _

instance finsupp : module.free R (ι →₀ M) :=
of_basis (finsupp.basis $ λ i, choose_basis R M)

variables {ι}

@[priority 100]
instance of_subsingleton [subsingleton N] : module.free R N :=
of_basis (basis.empty N : basis pempty R N)

@[priority 100]
instance of_subsingleton' [subsingleton R] : module.free R N :=
by letI := module.subsingleton R N; exact module.free.of_subsingleton R N

instance dfinsupp {ι : Type*} (M : ι → Type*) [Π (i : ι), add_comm_monoid (M i)]
  [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)] : module.free R (Π₀ i, M i) :=
of_basis $ dfinsupp.basis $ λ i, choose_basis R (M i)

instance direct_sum {ι : Type*} (M : ι → Type*) [Π (i : ι), add_comm_monoid (M i)]
  [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)] : module.free R (⨁ i, M i) :=
module.free.dfinsupp R M

end semiring

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M] [module.free R M]
variables [add_comm_group N] [module R N] [module.free R N]

instance tensor : module.free R (M ⊗[R] N) :=
of_equiv' (of_equiv' (free.finsupp _ R _) (finsupp_tensor_finsupp' R _ _).symm)
  (tensor_product.congr (choose_basis R M).repr (choose_basis R N).repr).symm

end comm_ring

section division_ring

variables [division_ring R] [add_comm_group M] [module R M]

@[priority 100]
instance of_division_ring : module.free R M :=
of_basis (basis.of_vector_space R M)

end division_ring

end module.free
