/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import data.nat.prime
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

open finite_dimensional
open cardinal

variables (F : Type u) (K : Type v) (A : Type w)

section ring

variables [comm_ring F] [ring K] [add_comm_group A]
variables [algebra F K] [module K A] [module F A] [is_scalar_tower F K A]
variables [strong_rank_condition F] [strong_rank_condition K] [module.free F K] [module.free K A]

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem rank_mul_rank' :
  (cardinal.lift.{w} (module.rank F K) * cardinal.lift.{v} (module.rank K A)) =
  cardinal.lift.{v} (module.rank F A) :=
begin
  obtain ⟨_, b⟩ := module.free.exists_basis F K,
  obtain ⟨_, c⟩ := module.free.exists_basis K A,
  rw [← (module.rank F K).lift_id, ← b.mk_eq_rank,
      ← (module.rank K A).lift_id, ← c.mk_eq_rank,
      ← lift_umax.{w v}, ← (b.smul c).mk_eq_rank, mk_prod, lift_mul,
      lift_lift, lift_lift, lift_lift, lift_lift, lift_umax]
end

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem rank_mul_rank (F : Type u) (K A : Type v)
  [comm_ring F] [ring K] [add_comm_group A]
  [algebra F K] [module K A] [module F A] [is_scalar_tower F K A]
  [strong_rank_condition F] [strong_rank_condition K] [module.free F K] [module.free K A] :
  module.rank F K * module.rank K A = module.rank F A :=
by convert rank_mul_rank' F K A; rw lift_id

/-- Tower law: if `A` is a `K`-algebra and `K` is an extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem finite_dimensional.finrank_mul_finrank'
  [nontrivial K] [module.finite F K] [module.finite K A] :
  finrank F K * finrank K A = finrank F A :=
begin
  letI := nontrivial_of_invariant_basis_number F,
  let b := module.free.choose_basis F K,
  let c := module.free.choose_basis K A,
  have := module.free.choose_basis_index.fintype K A,
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c,
    finrank_eq_card_basis (b.smul c), fintype.card_prod],
end

end ring

section field
variables [field F] [division_ring K] [add_comm_group A]
variables [algebra F K] [module K A] [module F A] [is_scalar_tower F K A]

namespace finite_dimensional

open is_noetherian

theorem trans [finite_dimensional F K] [finite_dimensional K A] : finite_dimensional F A :=
module.finite.trans K A

/-- In a tower of field extensions `L / K / F`, if `L / F` is finite, so is `K / F`.

(In fact, it suffices that `L` is a nontrivial ring.)

Note this cannot be an instance as Lean cannot infer `L`.
-/
theorem left (K L : Type*) [field K] [algebra F K] [ring L] [nontrivial L]
  [algebra F L] [algebra K L] [is_scalar_tower F K L]
  [finite_dimensional F L] : finite_dimensional F K :=
finite_dimensional.of_injective
  (is_scalar_tower.to_alg_hom F K L).to_linear_map
  (ring_hom.injective _)

lemma right [hf : finite_dimensional F A] : finite_dimensional K A :=
let ⟨⟨b, hb⟩⟩ := hf in ⟨⟨b, submodule.restrict_scalars_injective F _ _ $
by { rw [submodule.restrict_scalars_top, eq_top_iff, ← hb, submodule.span_le],
  exact submodule.subset_span }⟩⟩

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem finrank_mul_finrank [finite_dimensional F K] :
  finrank F K * finrank K A = finrank F A :=
begin
  by_cases hA : finite_dimensional K A,
  { resetI,
    rw finrank_mul_finrank' },
  { rw [finrank_of_infinite_dimensional hA, mul_zero, finrank_of_infinite_dimensional],
    exact mt (@right F K A _ _ _ _ _ _ _) hA }
end

theorem subalgebra.is_simple_order_of_finrank_prime (A) [ring A] [is_domain A] [algebra F A]
  (hp : (finrank F A).prime) : is_simple_order (subalgebra F A) :=
{ to_nontrivial :=
    ⟨⟨⊥, ⊤, λ he, nat.not_prime_one ((subalgebra.bot_eq_top_iff_finrank_eq_one.1 he).subst hp)⟩⟩,
  eq_bot_or_eq_top := λ K, begin
    haveI := finite_dimensional_of_finrank hp.pos,
    letI := division_ring_of_finite_dimensional F K,
    refine (hp.eq_one_or_self_of_dvd _ ⟨_, (finrank_mul_finrank F K A).symm⟩).imp _ (λ h, _),
    { exact subalgebra.eq_bot_of_finrank_one },
    { exact algebra.to_submodule_eq_top.1 (eq_top_of_finrank_eq $ K.finrank_to_submodule.trans h) },
  end }
/- TODO: `intermediate_field` version -/

-- TODO: generalize by removing [finite_dimensional F K]
-- V = ⊕F,
-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = ⊕K
instance _root_.linear_map.finite_dimensional'' (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [algebra F K] [finite_dimensional F K]
  [add_comm_group V] [module F V] [finite_dimensional F V] :
  finite_dimensional K (V →ₗ[F] K) :=
right F _ _

lemma finrank_linear_map' (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [algebra F K] [finite_dimensional F K]
  [add_comm_group V] [module F V] [finite_dimensional F V] :
  finrank K (V →ₗ[F] K) = finrank F V :=
mul_right_injective₀ finrank_pos.ne' $
calc  finrank F K * finrank K (V →ₗ[F] K)
    = finrank F (V →ₗ[F] K) : finrank_mul_finrank _ _ _
... = finrank F V * finrank F K : finrank_linear_map F V K
... = finrank F K * finrank F V : mul_comm _ _

end finite_dimensional

end field
