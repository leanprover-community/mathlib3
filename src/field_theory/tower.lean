/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.algebra_tower
import linear_algebra.finite_dimensional

/-!
# Tower of field extensions

In this file we prove the tower law for arbitrary extensions and finite extensions.
Suppose `L` is a field extension of `K` and `K` is a field extension of `F`.
Then `[L:F] = [L:K] [K:F]` where `[E₁:E₂]` means the `E₂`-dimension of `E₁`.

In fact we generalize it to algebras, where `L` is not necessarily a field, but just a `K`-algebra.

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
variables [field F] [field K] [ring A]
variables [algebra F K] [algebra K A] [algebra F A] [is_algebra_tower F K A]

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
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

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim (F : Type u) (K A : Type v) [field F] [field K] [ring A]
  [algebra F K] [algebra K A] [algebra F A] [is_algebra_tower F K A] :
  vector_space.dim F K * vector_space.dim K A = vector_space.dim F A :=
by convert dim_mul_dim' F K A; rw lift_id

namespace finite_dimensional

theorem trans [finite_dimensional F K] [finite_dimensional K A] : finite_dimensional F A :=
let ⟨b, hb⟩ := finite_dimensional.exists_is_basis_finset F K in
let ⟨c, hc⟩ := finite_dimensional.exists_is_basis_finset K A in
finite_dimensional.of_finite_basis $ hb.smul hc

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem findim_mul_findim [finite_dimensional F K] [finite_dimensional K A] :
  findim F K * findim K A = findim F A :=
let ⟨b, hb⟩ := finite_dimensional.exists_is_basis_finset F K in
let ⟨c, hc⟩ := finite_dimensional.exists_is_basis_finset K A in
by rw [findim_eq_card_basis hb, findim_eq_card_basis hc,
    findim_eq_card_basis (hb.smul hc), fintype.card_prod]

end finite_dimensional

end field
