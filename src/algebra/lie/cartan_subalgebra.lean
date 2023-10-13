/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.nilpotent
import algebra.lie.normalizer

/-!
# Cartan subalgebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `lie_submodule.is_ucs_limit`
  * `lie_subalgebra.is_cartan_subalgebra`
  * `lie_subalgebra.is_cartan_subalgebra_iff_is_ucs_limit`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/

universes u v w w₁ w₂

variables {R : Type u} {L : Type v}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] (H : lie_subalgebra R L)

/-- Given a Lie module `M` of a Lie algebra `L`, `lie_submodule.is_ucs_limit` is the proposition
that a Lie submodule `N ⊆ M` is the limiting value for the upper central series.

This is a characteristic property of Cartan subalgebras with the roles of `L`, `M`, `N` played by
`H`, `L`, `H`, respectively. See `lie_subalgebra.is_cartan_subalgebra_iff_is_ucs_limit`. -/
def lie_submodule.is_ucs_limit
  {M : Type*} [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
  (N : lie_submodule R L M) : Prop :=
∃ k, ∀ l, k ≤ l → (⊥ : lie_submodule R L M).ucs l = N

namespace lie_subalgebra

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra. -/
class is_cartan_subalgebra : Prop :=
(nilpotent        : lie_algebra.is_nilpotent R H)
(self_normalizing : H.normalizer = H)

instance [H.is_cartan_subalgebra] : lie_algebra.is_nilpotent R H := is_cartan_subalgebra.nilpotent

@[simp] lemma normalizer_eq_self_of_is_cartan_subalgebra
  (H : lie_subalgebra R L) [H.is_cartan_subalgebra] :
  H.to_lie_submodule.normalizer = H.to_lie_submodule :=
by rw [← lie_submodule.coe_to_submodule_eq_iff, coe_normalizer_eq_normalizer,
  is_cartan_subalgebra.self_normalizing, coe_to_lie_submodule]

@[simp] lemma ucs_eq_self_of_is_cartan_subalgebra
  (H : lie_subalgebra R L) [H.is_cartan_subalgebra] (k : ℕ) :
  H.to_lie_submodule.ucs k = H.to_lie_submodule :=
begin
  induction k with k ih,
  { simp, },
  { simp [ih], },
end

lemma is_cartan_subalgebra_iff_is_ucs_limit :
  H.is_cartan_subalgebra ↔ H.to_lie_submodule.is_ucs_limit :=
begin
  split,
  { introsI h,
    have h₁ : _root_.lie_algebra.is_nilpotent R H := by apply_instance,
    obtain ⟨k, hk⟩ := H.to_lie_submodule.is_nilpotent_iff_exists_self_le_ucs.mp h₁,
    replace hk : H.to_lie_submodule = lie_submodule.ucs k ⊥ :=
      le_antisymm hk (lie_submodule.ucs_le_of_normalizer_eq_self
      H.normalizer_eq_self_of_is_cartan_subalgebra k),
    refine ⟨k, λ l hl, _⟩,
    rw [← nat.sub_add_cancel hl, lie_submodule.ucs_add, ← hk,
      lie_subalgebra.ucs_eq_self_of_is_cartan_subalgebra], },
  { rintros ⟨k, hk⟩,
    exact
    { nilpotent :=
      begin
        dunfold lie_algebra.is_nilpotent,
        erw H.to_lie_submodule.is_nilpotent_iff_exists_lcs_eq_bot,
        use k,
        rw [_root_.eq_bot_iff, lie_submodule.lcs_le_iff, hk k (le_refl k)],
        exact le_refl _,
      end,
      self_normalizing :=
      begin
        have hk' := hk (k + 1) k.le_succ,
        rw [lie_submodule.ucs_succ, hk k (le_refl k)] at hk',
        rw [← lie_subalgebra.coe_to_submodule_eq_iff,
          ← lie_subalgebra.coe_normalizer_eq_normalizer, hk',
          lie_subalgebra.coe_to_lie_submodule],
      end } },
end

end lie_subalgebra

@[simp] lemma lie_ideal.normalizer_eq_top {R : Type u} {L : Type v}
  [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) :
  (I : lie_subalgebra R L).normalizer = ⊤ :=
begin
  ext x,
  simpa only [lie_subalgebra.mem_normalizer_iff, lie_subalgebra.mem_top, iff_true]
    using λ y hy, I.lie_mem hy
end

open lie_ideal

/-- A nilpotent Lie algebra is its own Cartan subalgebra. -/
instance lie_algebra.top_is_cartan_subalgebra_of_nilpotent [lie_algebra.is_nilpotent R L] :
  lie_subalgebra.is_cartan_subalgebra (⊤ : lie_subalgebra R L) :=
{ nilpotent        := infer_instance,
  self_normalizing :=
    by { rw [← top_coe_lie_subalgebra, normalizer_eq_top, top_coe_lie_subalgebra], }, }
