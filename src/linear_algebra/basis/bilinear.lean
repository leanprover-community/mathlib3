/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import linear_algebra.basis
import linear_algebra.bilinear_map

/-!
# Lemmas about bilinear maps with a basis over each argument

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/
namespace linear_map

variables {ι₁ ι₂ : Type*}
variables {R R₂ S S₂ M N P : Type*}
variables {Mₗ Nₗ Pₗ : Type*}
variables [comm_semiring R] [comm_semiring S] [comm_semiring R₂] [comm_semiring S₂]

section add_comm_monoid

variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
variables [add_comm_monoid Mₗ] [add_comm_monoid Nₗ] [add_comm_monoid Pₗ]
variables [module R M] [module S N] [module R₂ P] [module S₂ P]
variables [module R Mₗ] [module R Nₗ] [module R Pₗ]
variables [smul_comm_class S₂ R₂ P]
variables {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}
variables (b₁ : basis ι₁ R M) (b₂ : basis ι₂ S N) (b₁' : basis ι₁ R Mₗ) (b₂' : basis ι₂ R Nₗ)


/-- Two bilinear maps are equal when they are equal on all basis vectors. -/
lemma ext_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P}
  (h : ∀ i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) : B = B' :=
b₁.ext $ λ i, b₂.ext $ λ j, h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for semi-bilinear maps, see `sum_repr_mul_repr_mul` for the bilinear version. -/
lemma sum_repr_mul_repr_mulₛₗ {B : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (x y) :
  (b₁.repr x).sum (λ i xi, (b₂.repr y).sum (λ j yj, (ρ₁₂ xi) • (σ₁₂ yj) • B (b₁ i) (b₂ j))) =
  B x y :=
begin
  conv_rhs { rw [← b₁.total_repr x, ← b₂.total_repr y] },
  simp_rw [finsupp.total_apply, finsupp.sum, map_sum₂, map_sum,
    linear_map.map_smulₛₗ₂, linear_map.map_smulₛₗ],
end

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for bilinear maps, see `sum_repr_mul_repr_mulₛₗ` for the semi-bilinear version. -/
lemma sum_repr_mul_repr_mul {B : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ} (x y) :
  (b₁'.repr x).sum (λ i xi, (b₂'.repr y).sum (λ j yj, xi • yj • B (b₁' i) (b₂' j))) =
  B x y :=
begin
  conv_rhs { rw [← b₁'.total_repr x, ← b₂'.total_repr y] },
  simp_rw [finsupp.total_apply, finsupp.sum, map_sum₂, map_sum,
    linear_map.map_smul₂, linear_map.map_smul],
end

end add_comm_monoid

end linear_map
