/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.complement
import group_theory.group_action.basic
import group_theory.index

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `transfer ϕ : G →* A` for `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`.
-/

open_locale big_operators

open subgroup

variables {G : Type*} [group G] {H : subgroup G}
variables {A : Type*} [comm_group A] (ϕ : H →* A) (R S T : left_transversals (H : set G))

namespace subgroup

namespace left_transversals

open mul_action

open_locale pointwise

variables [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α := mem_left_transversals.to_equiv S.2, β := mem_left_transversals.to_equiv T.2 in
∏ q, ϕ ⟨(α q)⁻¹ * β q, quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans
  (congr_arg ϕ (subtype.ext (by simp_rw [coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left])))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ S T S).trans (diff_self ϕ S))

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
finset.prod_bij' (λ q _, g⁻¹ • q) (λ _ _, finset.mem_univ _) (λ _ _, congr_arg ϕ $ subtype.ext $ by
  simp_rw [coe_mk, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left])
  (λ q _, g • q) (λ _ _, finset.mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

lemma mem_normalizer_iff'' {G : Type*} [group G] {H : subgroup G} {g : G} :
  g ∈ H.normalizer ↔ ∀ h : G, h ∈ H ↔ g⁻¹ * h * g ∈ H :=
begin
  refine mem_normalizer_iff'.trans ⟨λ h n, _, λ h n, _⟩,
  { specialize h (g⁻¹ * n),
    rwa [mul_inv_cancel_left, iff.comm] at h },
  { specialize h (g * n),
    rwa [inv_mul_cancel_left, iff.comm] at h },
end

end left_transversals

end subgroup

namespace monoid_hom

variables [fintype (G ⧸ H)]

open subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : H →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : H →+ A`."]
noncomputable def transfer : G →* A :=
let T : left_transversals (H : set G) := left_transversals.inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

@[to_additive] lemma transfer_def (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

section explicit_computation

@[to_additive] lemma _root_.subgroup.pow_index_mem
  {G : Type*} [group G] (H : subgroup G) [H.normal] (hH : H.index ≠ 0) (g : G) :
  g ^ H.index ∈ H :=
begin
  haveI : fintype (G ⧸ H) := sorry,
  rw [←quotient_group.eq_one_iff, quotient_group.coe_pow, index_eq_card, pow_card_eq_one],
end

@[to_additive] lemma _root_.subgroup.pow_index_mem_of_le_center
  {G : Type*} [group G] {H : subgroup G} (hH : H ≤ center G) (g : G) :
  g ^ H.index ∈ H :=
begin
  sorry,
end

lemma transfer_eq_pow (hH : H ≤ center G) (g : G) : transfer ϕ g = ϕ ⟨g ^ H.index, sorry⟩ :=
begin
  sorry,
end

@[to_additive] noncomputable def transfer_pow (hH : H ≤ center G) : G →* H :=
{ to_fun := λ g, ⟨g ^ H.index, subgroup.pow_index_mem_of_le_center hH g⟩,
  map_one' := subtype.ext (one_pow H.index),
  map_mul' := λ a b, begin
    letI : is_commutative H := sorry,
    let ϕ : G →* H := transfer (monoid_hom.id H),
    let ψ : H →* G := H.subtype,
    simp_rw ← show ∀ g : G, ϕ g = ⟨g ^ H.index, _⟩, from transfer_eq_pow (monoid_hom.id H) hH,
    exact ϕ.map_mul a b,
  end }

@[to_additive] noncomputable def transfer_pow' (h : (center G).index ≠ 0) : G →* H :=
transfer_pow h

end explicit_computation

end monoid_hom
