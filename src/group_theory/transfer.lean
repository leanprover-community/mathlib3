/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.zmod.basic
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

section temp

noncomputable def orbit_zpowers_equiv
  {α β : Type*} [group α] (a : α) [mul_action α β] (b : β) :
  mul_action.orbit (subgroup.zpowers a) b ≃ zmod (function.minimal_period ((•) a) b) :=
equiv.symm (equiv.of_bijective (λ k, (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ k.val •
  ⟨b, mul_action.mem_orbit_self b⟩) begin
  let a' : subgroup.zpowers a := ⟨a, subgroup.mem_zpowers a⟩,
  let b' : mul_action.orbit α b := ⟨b, mul_action.mem_orbit_self b⟩,
  have key : function.minimal_period ((•) a) b = function.minimal_period ((•) a') b',
  { sorry },
  -- ^ this stuff might not be necessary ^ --
  split,
  { intros k k' h,
    replace h : a ^ k.val • b = a ^ k'.val • b := subtype.ext_iff.mp h,
    sorry },
  { rintros ⟨-, ⟨-, k, rfl⟩, rfl⟩,
    refine ⟨k, subtype.ext _⟩,
    change a ^ (k : zmod _).val • b = a ^ k • b,
    sorry },
end)

lemma orbit_zpowers_equiv_symm_apply {α β : Type*} [group α] (a : α) [mul_action α β] (b : β)
  (k : zmod (function.minimal_period ((•) a) b)) :
  (orbit_zpowers_equiv a b).symm k =
  (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ k.val • ⟨b, mul_action.mem_orbit_self b⟩ :=
rfl


end temp

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
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ S T S).trans (diff_self ϕ S))

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

section explicit_computation

variables (H)

open_locale classical

noncomputable def key_equiv (g : G) :
  G ⧸ H ≃ Σ (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))),
  fin (fintype.card (mul_action.orbit (zpowers g) q.out')) :=
(mul_action.self_equiv_sigma_orbits (zpowers g) (G ⧸ H)).trans
  (equiv.sigma_congr_right (λ q, equiv.symm (equiv.of_bijective
  (λ k, ((⟨g, mem_zpowers g⟩ : zpowers g) ^ k.1) • ⟨q.out', mul_action.mem_orbit_self q.out'⟩)
begin
  split,
  { intros k k' h,
    replace h := subtype.ext_iff.mp h,
    simp only at h,
    sorry },
  { sorry }
end)))

lemma key_equiv_symm_apply (g : G) (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H)))
  (k : fin (fintype.card (mul_action.orbit (zpowers g) q.out'))) :
  (key_equiv H g).symm ⟨q, k⟩ = g ^ k.1 • q.out' :=
rfl

def key_transversal (g : G) : left_transversals (H : set G) :=
⟨set.range (λ q, g ^ (key_equiv H g q).2.1 * (key_equiv H g q).1.out'.out'),
  range_mem_left_transversals (λ q, begin
  refine eq.trans _ ((key_equiv H g).symm_apply_apply q),
  exact _root_.congr_arg ((•) (g ^ (key_equiv H g q).2.1))
    (quotient.out_eq' (key_equiv H g q).1.out'),
end)⟩

lemma key_transversal_apply (g : G) (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H)))
  (k : fin (fintype.card (mul_action.orbit (zpowers g) q.out'))) :
  ↑(mem_left_transversals.to_equiv (key_transversal H g).2 ((key_equiv H g).symm ⟨q, k⟩)) =
    g ^ k.1 * q.out'.out' :=
begin
  change _ = ↑(⟨g ^ k.1 * q.out'.out', begin
    refine ⟨(key_equiv H g).symm ⟨q, k⟩, _⟩,
    have key := (key_equiv H g).apply_symm_apply ⟨q, k⟩,
    simp only [(key_equiv H g).apply_symm_apply ⟨q, k⟩],
    congr,
    simp only [(key_equiv H g).apply_symm_apply ⟨q, k⟩],
    sorry,
  end⟩ :
    set.range (λ q, g ^ (key_equiv H g q).2.1 * (key_equiv H g q).1.out'.out')),
  refine subtype.ext_iff.mp _,
  rw equiv.apply_eq_iff_eq_symm_apply,
  sorry
end

lemma key_transversal_apply' (g : G) (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H)))
  (k : fin (fintype.card (mul_action.orbit (zpowers g) q.out'))) :
  ↑(mem_left_transversals.to_equiv (g • key_transversal H g).2 ((key_equiv H g).symm ⟨q, k⟩)) =
    g ^ k.1 * q.out'.out' :=
begin
  sorry
end

lemma transfer_computation (g : G) : transfer ϕ g =
  ∏ (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))), 1 :=
begin
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (key_transversal H g) g
  ... = _ : ((key_equiv H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only [key_transversal_apply, key_transversal_apply'],
end

end explicit_computation

section explicit_computation

lemma transfer_eq_pow (hH : H ≤ center G) (g : G) : transfer ϕ g = ϕ ⟨g ^ H.index, sorry⟩ :=
begin

  sorry,
end




lemma orbit_powers_eq_orbit_zpowers {α : Type*} [group α] (a : α) {β : Type*} [fintype β]
  [mul_action α β] (b : β) : mul_action.orbit (submonoid.powers a) b = mul_action.orbit (zpowers a) b :=
begin
  sorry
end

open_locale classical

noncomputable def key_function (g : G) : G ⧸ H → G :=
λ q : G ⧸ H,
let q' := (quotient.mk' q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))).out',
hq : q ∈ mul_action.orbit (submonoid.powers g) q' := by
{ rw [orbit_powers_eq_orbit_zpowers, ←mul_action.orbit_eq_iff, eq_comm, mul_action.orbit_eq_iff],
  exact @quotient.mk_out' (G ⧸ H) (mul_action.orbit_rel (zpowers g) (G ⧸ H)) q },
hq' : ∃ k : ℕ, g ^ k • q' = q := by
{ have hq' := hq,
  obtain ⟨⟨-, ⟨k, rfl⟩⟩, hk⟩ := hq',
  exact ⟨k, hk⟩ } in g ^ (nat.find hq') * q'.out'

def key_transversal (g : G) : left_transversals (H : set G) :=
⟨set.range (λ q : G ⧸ H,
let q' := (quotient.mk' q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))).out',
hq : q ∈ mul_action.orbit (submonoid.powers g) q' := by
{ rw [orbit_powers_eq_orbit_zpowers, ←mul_action.orbit_eq_iff, eq_comm, mul_action.orbit_eq_iff],
  exact @quotient.mk_out' (G ⧸ H) (mul_action.orbit_rel (zpowers g) (G ⧸ H)) q },
hq' : ∃ k : ℕ, g ^ k • q' = q := by
{ have hq' := hq,
  obtain ⟨⟨-, ⟨k, rfl⟩⟩, hk⟩ := hq',
  exact ⟨k, hk⟩ } in g ^ (nat.find hq') * q'.out'), mem_left_transversals_iff_bijective.mpr
begin
  split,
  { intros a b h,
    sorry },
  { sorry },
end⟩

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
sorry

end explicit_computation

end monoid_hom
