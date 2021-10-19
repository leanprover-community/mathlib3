/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.algebra_tower
import linear_algebra.matrix.finite_dimensional
import linear_algebra.matrix.to_lin

/-!
# Tower of field extensions

In this file we prove the tower law for arbitrary extensions and finite extensions.
Suppose `L` is a field extension of `K` and `K` is a field extension of `F`.
Then `[L:F] = [L:K] [K:F]` where `[E₁:E₂]` means the `E₂`-dimension of `E₁`.

In fact we generalize it to vector spaces, where `L` is not necessarily a field,
but just a vector space over `K`.

## Implementation notes

We prove two versions, since there are two notions of dimensions: `module.rank` which gives
the dimension of an arbitrary vector space as a cardinal, and `finite_dimensional.finrank` which
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
variables [algebra F K] [module K A] [module F A] [is_scalar_tower F K A]

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim' :
  (cardinal.lift.{w} (module.rank F K) * cardinal.lift.{v} (module.rank K A)) =
  cardinal.lift.{v} (module.rank F A) :=
let b := basis.of_vector_space F K, c := basis.of_vector_space K A in
by rw [← (module.rank F K).lift_id, ← b.mk_eq_dim,
    ← (module.rank K A).lift_id, ← c.mk_eq_dim,
    ← lift_umax.{w v}, ← (b.smul c).mk_eq_dim, mk_prod, lift_mul,
    lift_lift, lift_lift, lift_lift, lift_lift, lift_umax]

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim (F : Type u) (K A : Type v) [field F] [field K] [add_comm_group A]
  [algebra F K] [module K A] [module F A] [is_scalar_tower F K A] :
  module.rank F K * module.rank K A = module.rank F A :=
by convert dim_mul_dim' F K A; rw lift_id

namespace finite_dimensional

open is_noetherian

theorem trans [finite_dimensional F K] [finite_dimensional K A] : finite_dimensional F A :=
let b := basis.of_vector_space F K, c := basis.of_vector_space K A in
of_fintype_basis $ b.smul c

lemma right [hf : finite_dimensional F A] : finite_dimensional K A :=
let ⟨⟨b, hb⟩⟩ := iff_fg.1 hf in
iff_fg.2 ⟨⟨b, submodule.restrict_scalars_injective F _ _ $
by { rw [submodule.restrict_scalars_top, eq_top_iff, ← hb, submodule.span_le],
  exact submodule.subset_span }⟩⟩

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem finrank_mul_finrank [finite_dimensional F K] :
  finrank F K * finrank K A = finrank F A :=
begin
  by_cases hA : finite_dimensional K A,
  { resetI,
    let b := basis.of_vector_space F K,
    let c := basis.of_vector_space K A,
    rw [finrank_eq_card_basis b, finrank_eq_card_basis c,
      finrank_eq_card_basis (b.smul c), fintype.card_prod] },
  { rw [finrank_of_infinite_dimensional hA, mul_zero, finrank_of_infinite_dimensional],
    exact mt (@right F K A _ _ _ _ _ _ _) hA }
end

instance linear_map (F : Type u) (V : Type v) (W : Type w)
  [field F] [add_comm_group V] [module F V] [add_comm_group W] [module F W]
  [finite_dimensional F V] [finite_dimensional F W] :
  finite_dimensional F (V →ₗ[F] W) :=
let b := basis.of_vector_space F V, c := basis.of_vector_space F W in
(matrix.to_lin b c).finite_dimensional

lemma finrank_linear_map (F : Type u) (V : Type v) (W : Type w)
  [field F] [add_comm_group V] [module F V] [add_comm_group W] [module F W]
  [finite_dimensional F V] [finite_dimensional F W] :
  finrank F (V →ₗ[F] W) = finrank F V * finrank F W :=
  let b := basis.of_vector_space F V, c := basis.of_vector_space F W in
by rw [linear_equiv.finrank_eq (linear_map.to_matrix b c), matrix.finrank_matrix,
      finrank_eq_card_basis b, finrank_eq_card_basis c, mul_comm]

-- TODO: generalize by removing [finite_dimensional F K]
-- V = ⊕F,
-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = ⊕K
instance linear_map' (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [algebra F K] [finite_dimensional F K]
  [add_comm_group V] [module F V] [finite_dimensional F V] :
  finite_dimensional K (V →ₗ[F] K) :=
right F _ _

lemma finrank_linear_map' (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [algebra F K] [finite_dimensional F K]
  [add_comm_group V] [module F V] [finite_dimensional F V] :
  finrank K (V →ₗ[F] K) = finrank F V :=
(nat.mul_right_inj $ show 0 < finrank F K, from finrank_pos).1 $
calc  finrank F K * finrank K (V →ₗ[F] K)
    = finrank F (V →ₗ[F] K) : finrank_mul_finrank _ _ _
... = finrank F V * finrank F K : finrank_linear_map F V K
... = finrank F K * finrank F V : mul_comm _ _

end finite_dimensional

end field
