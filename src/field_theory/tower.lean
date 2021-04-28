/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.algebra_tower
import linear_algebra.matrix

/-!
# Tower of field extensions

In this file we prove the tower law for arbitrary extensions and finite extensions.
Suppose `L` is a field extension of `K` and `K` is a field extension of `F`.
Then `[L:F] = [L:K] [K:F]` where `[E₁:E₂]` means the `E₂`-dimension of `E₁`.

In fact we generalize it to vector spaces, where `L` is not necessarily a field,
but just a vector space over `K`.

## Implementation notes

We prove two versions, since there are two notions of dimensions: `vector_space.dim` which gives
the dimension of an arbitrary vector space as a cardinal, and `finite_dimensional.findim` which
gives the dimension of a finitely-dimensional vector space as a natural number.

## Tags

tower law

-/

universes u v w u₁ v₁ w₁
open_locale classical big_operators

section field

open cardinal

variables (F : Type u) (K : Type v) (A : Type w)
variables [field F] [field K] [add_comm_group A]
variables [algebra F K] [vector_space K A] [vector_space F A] [is_scalar_tower F K A]

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim' :
  (cardinal.lift.{v w} (vector_space.dim F K) *
      cardinal.lift.{w v} (vector_space.dim K A) : cardinal.{max w v}) =
  cardinal.lift.{w v} (vector_space.dim F A) :=
let ⟨b, hb⟩ := exists_is_basis F K, ⟨c, hc⟩ := exists_is_basis K A in
by rw [← (vector_space.dim F K).lift_id, ← hb.mk_eq_dim,
    ← (vector_space.dim K A).lift_id, ← hc.mk_eq_dim,
    ← lift_umax.{w v}, ← (hb.smul hc).mk_eq_dim, mk_prod, lift_mul,
    lift_lift, lift_lift, lift_lift, lift_lift, lift_umax]

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim (F : Type u) (K A : Type v) [field F] [field K] [add_comm_group A]
  [algebra F K] [vector_space K A] [vector_space F A] [is_scalar_tower F K A] :
  vector_space.dim F K * vector_space.dim K A = vector_space.dim F A :=
by convert dim_mul_dim' F K A; rw lift_id

namespace finite_dimensional

theorem trans [finite_dimensional F K] [finite_dimensional K A] : finite_dimensional F A :=
let ⟨b, hb⟩ := exists_is_basis_finset F K in
let ⟨c, hc⟩ := exists_is_basis_finset K A in
of_fintype_basis $ hb.smul hc

lemma right [hf : finite_dimensional F A] : finite_dimensional K A :=
let ⟨b, hb⟩ := iff_fg.1 hf in
iff_fg.2 ⟨b, submodule.restrict_scalars_injective F _ _ $
by { rw [submodule.restrict_scalars_top, eq_top_iff, ← hb, submodule.span_le],
  exact submodule.subset_span }⟩

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem findim_mul_findim [finite_dimensional F K] :
  findim F K * findim K A = findim F A :=
begin
  by_cases hA : finite_dimensional K A,
  { resetI,
    rcases exists_is_basis_finset F K with ⟨b, hb⟩,
    rcases exists_is_basis_finset K A with ⟨c, hc⟩,
    rw [findim_eq_card_basis hb, findim_eq_card_basis hc,
      findim_eq_card_basis (hb.smul hc), fintype.card_prod] },
  { rw [findim_of_infinite_dimensional hA, mul_zero, findim_of_infinite_dimensional],
    exact mt (@right F K A _ _ _ _ _ _ _) hA }
end

instance linear_map (F : Type u) (V : Type v) (W : Type w)
  [field F] [add_comm_group V] [vector_space F V] [add_comm_group W] [vector_space F W]
  [finite_dimensional F V] [finite_dimensional F W] :
  finite_dimensional F (V →ₗ[F] W) :=
let ⟨b, hb⟩ := exists_is_basis_finset F V in
let ⟨c, hc⟩ := exists_is_basis_finset F W in
(matrix.to_lin hb hc).finite_dimensional

lemma findim_linear_map (F : Type u) (V : Type v) (W : Type w)
  [field F] [add_comm_group V] [vector_space F V] [add_comm_group W] [vector_space F W]
  [finite_dimensional F V] [finite_dimensional F W] :
  findim F (V →ₗ[F] W) = findim F V * findim F W :=
let ⟨b, hb⟩ := exists_is_basis_finset F V in
let ⟨c, hc⟩ := exists_is_basis_finset F W in
by rw [linear_equiv.findim_eq (linear_map.to_matrix hb hc), matrix.findim_matrix,
      findim_eq_card_basis hb, findim_eq_card_basis hc, mul_comm]

-- TODO: generalize by removing [finite_dimensional F K]
-- V = ⊕F,
-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = ⊕K
instance linear_map' (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [algebra F K] [finite_dimensional F K]
  [add_comm_group V] [vector_space F V] [finite_dimensional F V] :
  finite_dimensional K (V →ₗ[F] K) :=
right F _ _

lemma findim_linear_map' (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [algebra F K] [finite_dimensional F K]
  [add_comm_group V] [vector_space F V] [finite_dimensional F V] :
  findim K (V →ₗ[F] K) = findim F V :=
(nat.mul_right_inj $ show 0 < findim F K, from findim_pos).1 $
calc  findim F K * findim K (V →ₗ[F] K)
    = findim F (V →ₗ[F] K) : findim_mul_findim _ _ _
... = findim F V * findim F K : findim_linear_map F V K
... = findim F K * findim F V : mul_comm _ _

end finite_dimensional

end field
