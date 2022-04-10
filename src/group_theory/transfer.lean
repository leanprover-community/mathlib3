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

namespace mul_action

open subgroup

variables (α : Type*) {β : Type*} [monoid α] [mul_action α β] [group β] (H : subgroup β)

@[to_additive] instance right_quotient_action : quotient_action H.normalizer.opposite H :=
⟨λ b c _ _, by rwa [smul_def, smul_def, mul_opposite.smul_eq_mul_unop, mul_inv_rev,
  mul_opposite.smul_eq_mul_unop,
  ←mul_assoc, ←subtype.val_eq_coe, mem_normalizer_iff'.mp b.2, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive] instance [quotient_action α H] : mul_action α (β ⧸ H) :=
{ smul := λ a, quotient.map' ((•) a) (λ b c h, quotient_action.inv_mul_mem a h),
  one_smul := λ q, quotient.induction_on' q (λ b, congr_arg quotient.mk' (one_smul α b)),
  mul_smul := λ a a' q, quotient.induction_on' q (λ b, congr_arg quotient.mk' (mul_smul a a' b)) }

variables {α}

@[simp, to_additive] lemma quotient_action.smul_mk [quotient_action α H] (a : α) (b : β) :
  (a • quotient_group.mk b : β ⧸ H) = quotient_group.mk (a • b) := rfl

@[simp, to_additive] lemma quotient_action.smul_coe [quotient_action α H] (a : α) (b : β) :
  (a • b : β ⧸ H) = ↑(a • b) := rfl

end mul_action

open_locale big_operators

open subgroup

variables {G : Type*} [group G] {H : subgroup G}
variables {A : Type*} [comm_group A] (ϕ : H →* A) (R S T : left_transversals (H : set G))

namespace subgroup

namespace left_transversals

open mul_action

open_locale pointwise

variables {F : Type*} [group F] [mul_action F G] [mul_action.quotient_action F H]

@[to_additive] instance : mul_action F (left_transversals (H : set G)) :=
{ smul := λ f T, ⟨f • T, by
  { refine mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g, _),
    obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (f⁻¹ • g),
    refine ⟨⟨f • t, set.smul_mem_smul_set t.2⟩, _, _⟩,
    { exact (congr_arg (λ g', (f • (t : G))⁻¹ * g' ∈ H) (smul_inv_smul f g)).mp
        (quotient_action.inv_mul_mem f ht1) },
    { rintros ⟨-, t', ht', rfl⟩ h,
      simp_rw [subtype.ext_iff, subtype.coe_mk, smul_left_cancel_iff],
      refine subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ _),
      exact (congr_arg (λ g', g'⁻¹ * f⁻¹ • g ∈ H) (inv_smul_smul f t')).mp
        (quotient_action.inv_mul_mem f⁻¹ h) } }⟩,
  one_smul := λ T, subtype.ext (one_smul F T),
  mul_smul := λ f₁ f₂ T, subtype.ext (mul_smul f₁ f₂ T) }

@[to_additive] lemma smul_to_fun (f : F) (T : left_transversals (H : set G)) (g : G) :
  (f • mem_left_transversals.to_fun T.2 g : G) = mem_left_transversals.to_fun (f • T).2 (f • g) :=
begin
  change ↑(⟨_, set.smul_mem_smul_set (subtype.coe_prop _)⟩ : f • T) = _,
  exact subtype.ext_iff.mp (unique_of_exists_unique
    (mem_left_transversals_iff_exists_unique_inv_mul_mem.mp (f • T).2 (f • g))
      (quotient_action.inv_mul_mem f (mem_left_transversals.inv_to_fun_mul_mem T.2 g))
      (mem_left_transversals.inv_to_fun_mul_mem (f • T).2 (f • g))),
end

@[to_additive] lemma smul_to_equiv (f : F) (T : left_transversals (H : set G)) (q : G ⧸ H) :
  f • (mem_left_transversals.to_equiv T.2 q : G) =
    mem_left_transversals.to_equiv (f • T).2 (f • q) :=
quotient.induction_on' q (λ g, smul_to_fun f T g)

@[to_additive] lemma smul_apply_eq_smul_apply_inv_smul
  (f : F) (T : left_transversals (H : set G)) (q : G ⧸ H) :
  (mem_left_transversals.to_equiv (f • T).2 q : G) =
    f • (mem_left_transversals.to_equiv T.2 (f⁻¹ • q) : G) :=
by rw [smul_to_equiv, smul_inv_smul]

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

lemma smul_diff_smul' [is_commutative H] (g : H.normalizer.opposite) :
  diff (monoid_hom.id H) (g • S) (g • T) =
    ⟨(g : Gᵐᵒᵖ).unop⁻¹ * (diff (monoid_hom.id H) S T : H) * (g : Gᵐᵒᵖ).unop,
      (mem_normalizer_iff''.mp g.2 _).mp (set_like.coe_mem _)⟩ :=
begin
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨(g : Gᵐᵒᵖ).unop⁻¹ * h * (g : Gᵐᵒᵖ).unop,
      (mem_normalizer_iff''.mp g.2 _).mp (set_like.coe_mem _)⟩,
    map_one' := by rw [subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_self],
    map_mul' := λ h₁ h₂, by rw [subtype.ext_iff, coe_mk, coe_mul, coe_mul, coe_mk, coe_mk,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_inv_cancel_left] },
  refine eq.trans (finset.prod_bij' (λ q _, g⁻¹ • q) (λ _ _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, g • q) (λ _ _, finset.mem_univ _)
    (λ q _, smul_inv_smul _ q) (λ q _, inv_smul_smul _ q)) (ϕ.map_prod _ _).symm,
  rw [monoid_hom.id_apply, monoid_hom.id_apply, monoid_hom.coe_mk, coe_mk, coe_mk, coe_mk,
      smul_apply_eq_smul_apply_inv_smul, smul_apply_eq_smul_apply_inv_smul, smul_def, smul_def,
      mul_opposite.smul_eq_mul_unop, mul_opposite.smul_eq_mul_unop, mul_inv_rev,
      mul_assoc, mul_assoc, mul_assoc],
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
