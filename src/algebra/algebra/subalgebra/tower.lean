/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import algebra.algebra.subalgebra.basic
import algebra.algebra.tower

/-!
# Subalgebras in towers of algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove facts about subalgebras in towers of algebra.

An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

## Main results

 * `is_scalar_tower.subalgebra`: if `A/S/R` is a tower and `S₀` is a subalgebra
   between `S` and `R`, then `A/S/S₀` is a tower
 * `is_scalar_tower.subalgebra'`: if `A/S/R` is a tower and `S₀` is a subalgebra
   between `S` and `R`, then `A/S₀/R` is a tower
 * `subalgebra.restrict_scalars`: turn an `S`-subalgebra of `A` into an `R`-subalgebra of `A`,
   given that `A/S/R` is a tower

-/

open_locale pointwise
universes u v w u₁ v₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace algebra

variables [comm_semiring R] [semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]

variables {A}

lemma lmul_algebra_map (x : R) :
  algebra.lmul R A (algebra_map R A x) = algebra.lsmul R A x :=
eq.symm $ linear_map.ext $ smul_def x

end algebra

namespace is_scalar_tower

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A]
variables [algebra R S] [algebra S A]

variables (R S A)

instance subalgebra (S₀ : subalgebra R S) : is_scalar_tower S₀ S A :=
of_algebra_map_eq $ λ x, rfl

variables [algebra R A] [is_scalar_tower R S A]

instance subalgebra' (S₀ : subalgebra R S) : is_scalar_tower R S₀ A :=
@is_scalar_tower.of_algebra_map_eq R S₀ A _ _ _ _ _ _ $ λ _,
(is_scalar_tower.algebra_map_apply R S A _ : _)

end semiring

end is_scalar_tower

namespace subalgebra

open is_scalar_tower

section semiring

variables (R) {S A B} [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra R A] [algebra S B] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

/-- Given a tower `A / ↥U / S / R` of algebras, where `U` is an `S`-subalgebra of `A`, reinterpret
`U` as an `R`-subalgebra of `A`. -/
def restrict_scalars (U : subalgebra S A) : subalgebra R A :=
{ algebra_map_mem' := λ x, by { rw algebra_map_apply R S A, exact U.algebra_map_mem _ },
  .. U }

@[simp] lemma coe_restrict_scalars {U : subalgebra S A} :
  (restrict_scalars R U : set A) = (U : set A) := rfl

@[simp] lemma restrict_scalars_top : restrict_scalars R (⊤ : subalgebra S A) = ⊤ :=
set_like.coe_injective rfl

@[simp] lemma restrict_scalars_to_submodule {U : subalgebra S A} :
  (U.restrict_scalars R).to_submodule = U.to_submodule.restrict_scalars R :=
set_like.coe_injective rfl

@[simp] lemma mem_restrict_scalars {U : subalgebra S A} {x : A} :
  x ∈ restrict_scalars R U ↔ x ∈ U := iff.rfl

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : subalgebra S A → subalgebra R A) :=
λ U V H, ext $ λ x, by rw [← mem_restrict_scalars R, H, mem_restrict_scalars]

/-- Produces an `R`-algebra map from `U.restrict_scalars R` given an `S`-algebra map from `U`.

This is a special case of `alg_hom.restrict_scalars` that can be helpful in elaboration. -/
@[simp]
def of_restrict_scalars (U : subalgebra S A) (f : U →ₐ[S] B) : U.restrict_scalars R →ₐ[R] B :=
f.restrict_scalars R

end semiring

end subalgebra

namespace is_scalar_tower

open subalgebra

variables [comm_semiring R] [comm_semiring S] [comm_semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

theorem adjoin_range_to_alg_hom (t : set A) :
  (algebra.adjoin (to_alg_hom R S A).range t).restrict_scalars R =
    (algebra.adjoin S t).restrict_scalars R :=
subalgebra.ext $ λ z,
show z ∈ subsemiring.closure (set.range (algebra_map (to_alg_hom R S A).range A) ∪ t : set A) ↔
  z ∈ subsemiring.closure (set.range (algebra_map S A) ∪ t : set A),
from suffices set.range (algebra_map (to_alg_hom R S A).range A) = set.range (algebra_map S A),
  by rw this,
by { ext z, exact ⟨λ ⟨⟨x, y, h1⟩, h2⟩, ⟨y, h2 ▸ h1⟩, λ ⟨y, hy⟩, ⟨⟨z, y, hy⟩, rfl⟩⟩ }

end is_scalar_tower
