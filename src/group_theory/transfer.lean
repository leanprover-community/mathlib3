/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.complement
import group_theory.group_action.basic

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `transfer ϕ : G →* A` for `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`.
-/

open_locale big_operators

open subgroup

variables {G : Type*} [group G] {H : subgroup G}
variables {A : Type*} [comm_group A] (ϕ : H →* A) (α β γ : left_transversals (H : set G))

namespace subgroup

namespace left_transversals

@[to_additive] instance : mul_action G (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨left_coset g T, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g', by
  { obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g'),
    simp_rw [←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩,
    rintros ⟨_, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_right_inj g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (one_left_coset T),
  mul_smul := λ g g' T, subtype.ext (left_coset_assoc ↑T g g').symm }

@[to_additive] lemma smul_symm_apply_eq_mul_symm_apply_inv_smul
  (g : G) (α : left_transversals (H : set G)) (q : G ⧸ H) :
  ↑((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)).symm q) =
    g * ((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm
      (g⁻¹ • q : G ⧸ H)) :=
begin
  let w := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)),
  let y := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)),
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (subtype.mem _)⟩ : (g • α).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = g • (w (w.symm (g⁻¹ • q : G ⧸ H))),
  rw [equiv.apply_symm_apply, ←mul_smul, mul_inv_self, one_smul],
end

variables [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm,
    β' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp β.2)).symm in
∏ (q : G ⧸ H), ϕ ⟨(α' q)⁻¹ * (β' q),
  (quotient.exact' ((α'.symm_apply_apply q).trans (β'.symm_apply_apply q).symm))⟩

@[to_additive] lemma diff_mul_diff : diff ϕ α β * diff ϕ β γ = diff ϕ α γ :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans
  (congr_arg ϕ (subtype.ext (by simp_rw [coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left])))))

@[to_additive] lemma diff_self : diff ϕ α α = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ α α α)

@[to_additive] lemma diff_inv : (diff ϕ α β)⁻¹ = diff ϕ β α :=
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ α β α).trans (diff_self ϕ α))

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • α) (g • β) = diff ϕ α β :=
finset.prod_bij' (λ q _, g⁻¹ • q) (λ _ _, finset.mem_univ _)
  (λ _ _, congr_arg ϕ (subtype.ext (by simp_rw [coe_mk,
    smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assoc, inv_mul_cancel_left])))
  (λ q _, g • q) (λ _ _, finset.mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

end left_transversals

end subgroup

namespace monoid_hom

variables [fintype (G ⧸ H)]

open subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : H →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : H →+ A`."]
noncomputable def transfer (ϕ : H →* A) : G →* A :=
let α : left_transversals (H : set G) := left_transversals.inhabited.default in
{ to_fun := λ g, diff ϕ α (g • α),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

@[to_additive] lemma transfer_def (g : G) : transfer ϕ g = diff ϕ α (g • α) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

end monoid_hom
