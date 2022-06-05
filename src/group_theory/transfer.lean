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

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
-/

open_locale big_operators

variables {G : Type*} [group G] {H : subgroup G} {A : Type*} [comm_group A] (ϕ : H →* A)

namespace subgroup

namespace left_transversals

open finset mul_action

open_locale pointwise

variables (R S T : left_transversals (H : set G)) [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α := mem_left_transversals.to_equiv S.2, β := mem_left_transversals.to_equiv T.2 in
∏ q, ϕ ⟨(α q)⁻¹ * β q, quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
prod_mul_distrib.symm.trans (prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans (congr_arg ϕ
  (by simp_rw [subtype.ext_iff, coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left]))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one_right $ (diff_mul_diff ϕ S T S).trans $ diff_self ϕ S

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
prod_bij' (λ q _, g⁻¹ • q) (λ _ _, mem_univ _) (λ _ _, congr_arg ϕ (by simp_rw [coe_mk,
  smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]))
  (λ q _, g • q) (λ _ _, mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

end left_transversals

end subgroup

namespace monoid_hom

variables [fintype (G ⧸ H)]

open subgroup subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer : G →* A :=
let T : left_transversals (H : set G) := inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

variables (T : left_transversals (H : set G))

@[to_additive] lemma transfer_def (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

end monoid_hom
