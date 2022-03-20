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

class subgroup.coset_action
  {G : Type*} [group G] (H : subgroup G) (F : Type*) [monoid F] [mul_action F G] : Prop :=
(inv_mul_mem : ∀ (f : F) {g₁ g₂ : G}, g₁⁻¹ * g₂ ∈ H → (f • g₁)⁻¹ * (f • g₂) ∈ H)

class add_subgroup.coset_action
  {G : Type*} [add_group G] (H : add_subgroup G) (F : Type*) [add_monoid F] [add_action F G] : Prop :=
(inv_mul_mem : ∀ (f : F) {g₁ g₂ : G}, -g₁ + g₂ ∈ H → -(f +ᵥ g₁) + (f +ᵥ g₂) ∈ H)

attribute [to_additive add_subgroup.coset_action] subgroup.coset_action

open_locale big_operators

open subgroup

variables {G : Type*} [group G] {H : subgroup G}
variables {A : Type*} [comm_group A] (ϕ : H →* A) (R S T : left_transversals (H : set G))

namespace subgroup

@[to_additive] instance inst1 : H.coset_action G :=
⟨λ _ _ _ _, by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩

@[to_additive] instance inst3 : mul_action Hᵐᵒᵖ G :=
{ smul := λ h, (* h.unop),
  one_smul := mul_one,
  mul_smul := λ h₁ h₂ g, (mul_assoc g h₂.unop h₁.unop).symm }

@[to_additive] lemma smul_eq_mul_unop (h : Hᵐᵒᵖ) (g : G) : h • g = g * h.unop := rfl

@[to_additive] instance inst2 : H.coset_action H.normalizerᵐᵒᵖ :=
⟨λ g g' _ _, by rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ←mul_assoc, mul_assoc _ g'⁻¹,
  mem_normalizer_iff'.mp (show ↑g.unop ∈ H.normalizer, from g.unop.2), mul_inv_cancel_left]⟩

@[to_additive] instance mk_coset_action {F : Type*} [group F] [mul_action F G] [H.coset_action F] :
  mul_action F (G ⧸ H) :=
{ smul := λ f, quotient.map' ((•) f) (λ g g' h, coset_action.inv_mul_mem f h),
  one_smul := λ q, quotient.induction_on' q (λ g, congr_arg quotient.mk' (one_smul F g)),
  mul_smul := λ f f' q, quotient.induction_on' q (λ g, congr_arg quotient.mk' (mul_smul f f' g)) }

@[to_additive] instance action1 : mul_action G (G ⧸ H) := subgroup.mk_coset_action

@[to_additive] instance action2 : mul_action H.normalizerᵐᵒᵖ (G ⧸ H) := subgroup.mk_coset_action

namespace left_transversals

open_locale pointwise

@[to_additive] instance {F : Type*} [group F] [mul_action F G] [H.coset_action F] :
  mul_action F (left_transversals (H : set G)) :=
{ smul := λ f T, ⟨f • T, by
  { refine mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g, _),
    obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (f⁻¹ • g),
    refine ⟨⟨f • t, set.smul_mem_smul_set t.2⟩, _, _⟩,
    { exact (congr_arg (λ g', (f • (t : G))⁻¹ * g' ∈ H) (smul_inv_smul f g)).mp
        (coset_action.inv_mul_mem f ht1) },
    { rintros ⟨-, t', ht', rfl⟩ h,
      simp_rw [subtype.ext_iff, subtype.coe_mk, smul_left_cancel_iff],
      refine subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ _),
      exact (congr_arg (λ g', g'⁻¹ * f⁻¹ • g ∈ H) (inv_smul_smul f t')).mp
        (coset_action.inv_mul_mem f⁻¹ h) } }⟩,
  one_smul := λ T, subtype.ext (one_smul F T),
  mul_smul := λ f₁ f₂ T, subtype.ext (mul_smul f₁ f₂ T) }

@[to_additive] lemma smul_to_fun {F : Type*} [group F] [mul_action F G] [H.coset_action F]
  (f : F) (T : left_transversals (H : set G)) (g : G) :
  (f • mem_left_transversals.to_fun T.2 g : G) = mem_left_transversals.to_fun (f • T).2 (f • g) :=
begin
  change ↑(⟨_, set.smul_mem_smul_set (subtype.coe_prop _)⟩ : f • T) = _,
  exact subtype.ext_iff.mp (unique_of_exists_unique
    (mem_left_transversals_iff_exists_unique_inv_mul_mem.mp (f • T).2 (f • g))
      (coset_action.inv_mul_mem f (mem_left_transversals.inv_to_fun_mul_mem T.2 g))
      (mem_left_transversals.inv_to_fun_mul_mem (f • T).2 (f • g))),
end

@[to_additive] lemma smul_to_equiv {F : Type*} [group F] [mul_action F G] [H.coset_action F]
  (f : F) (T : left_transversals (H : set G)) (q : G ⧸ H) :
  f • (mem_left_transversals.to_equiv T.2 q : G) =
    mem_left_transversals.to_equiv (f • T).2 (f • q) :=
quotient.induction_on' q (λ g, smul_to_fun f T g)

@[to_additive] lemma general_action_apply {F : Type*} [group F] [mul_action F G]
  [H.coset_action F]
  (f : F) (T : left_transversals (H : set G)) (q : G ⧸ H) :
  (mem_left_transversals.to_equiv (f • T).2 q : G) =
    f • (mem_left_transversals.to_equiv T.2 (f⁻¹ • q) : G) :=
begin
  rw smul_to_equiv,
  rw smul_inv_smul,
end

@[to_additive] lemma smul_apply_eq_mul_apply_inv_smul (g : G) (q : G ⧸ H) :
  ↑(mem_left_transversals.to_equiv (g • T).2 q) =
    g * mem_left_transversals.to_equiv T.2 (g⁻¹ • q) :=
general_action_apply g T q

@[to_additive] lemma smul_apply_eq_apply_inv_smul_mul (g : H.normalizerᵐᵒᵖ) (q : G ⧸ H) :
  (mem_left_transversals.to_equiv (g • T).2 q : G) =
    mem_left_transversals.to_equiv T.2 (g⁻¹ • q) * g.unop :=
general_action_apply g T q

variables [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α' := mem_left_transversals.to_equiv S.2, β' := mem_left_transversals.to_equiv T.2 in
∏ q, ϕ ⟨(α' q)⁻¹ * (β' q),
  quotient.exact' ((α'.symm_apply_apply q).trans (β'.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans
  (congr_arg ϕ (subtype.ext (by simp_rw [coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left])))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ S T S).trans (diff_self ϕ S))

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
finset.prod_bij' (λ q _, g⁻¹ • q) (λ _ _, finset.mem_univ _) (λ _ _, congr_arg ϕ $ subtype.ext $ by
  simp_rw [coe_mk, smul_apply_eq_mul_apply_inv_smul, mul_inv_rev, mul_assoc, inv_mul_cancel_left])
  (λ q _, g • q) (λ _ _, finset.mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

lemma smul_diff_smul' [is_commutative H] (g : H.normalizerᵐᵒᵖ) :
  diff (monoid_hom.id H) (g • S) (g • T) = ⟨g.unop⁻¹ * (diff (monoid_hom.id H) S T : H) * g.unop,
    begin
      have := (g.unop⁻¹.2 (diff (monoid_hom.id H) S T : H)).mp (diff (monoid_hom.id H) S T : H).2,
      rwa [subtype.val_eq_coe, coe_inv, inv_inv] at this,
    end⟩ :=
begin
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨g.unop⁻¹ * h * g.unop, by
    { have := (g.unop⁻¹.2 h).mp h.2,
      rwa [subtype.val_eq_coe, coe_inv, inv_inv] at this }⟩,
    map_one' := by rw [subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_self],
    map_mul' := λ h₁ h₂, by rw [subtype.ext_iff, coe_mk, coe_mul, coe_mul, coe_mk, coe_mk,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_inv_cancel_left] },
  refine eq.trans (finset.prod_bij' (λ q _, g⁻¹ • q) (λ _ _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, g • q) (λ _ _, finset.mem_univ _)
    (λ q _, smul_inv_smul _ q) (λ q _, inv_smul_smul _ q)) (ϕ.map_prod _ _).symm,
  change _ * _ = (g.unop : G)⁻¹ * (_ * _) * (g.unop : G),
  simp_rw [smul_apply_eq_apply_inv_smul_mul, mul_inv_rev, mul_assoc],
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
noncomputable def transfer (ϕ : H →* A) : G →* A :=
let T : left_transversals (H : set G) := left_transversals.inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

@[to_additive] lemma transfer_def (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

end monoid_hom
