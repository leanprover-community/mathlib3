/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.complement
import group_theory.group_action.basic
import group_theory.index
import group_theory.sylow

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
-/

section equiv_stuff

-- Auxillary PR
lemma orbit_zpowers_equiv_symm_apply' {α β : Type*} [group α] (a : α) [mul_action α β] (b : β)
  (k : ℤ) :
  (mul_action.orbit_zpowers_equiv a b).symm k =
  (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ k • ⟨b, mul_action.mem_orbit_self b⟩ :=
begin
  conv_rhs { rw ← int.mod_add_div k (function.minimal_period ((•) a) b) },
  rw [zpow_add, mul_smul, mul_action.orbit_zpowers_equiv_symm_apply, zmod.coe_int_cast, smul_left_cancel_iff,
      subtype.ext_iff, mul_action.orbit.coe_smul, subtype.coe_mk, eq_comm,
      mul_action.zpow_smul_eq_iff_minimal_period_dvd],
  apply dvd_mul_right,
end

universe u

-- PR2
noncomputable def key_equiv {G : Type u} [group G] (H : subgroup G) (g : G) :
  G ⧸ H ≃ Σ (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H))),
  zmod (function.minimal_period ((•) g) q.out') :=
(mul_action.self_equiv_sigma_orbits (subgroup.zpowers g) (G ⧸ H)).trans
  (equiv.sigma_congr_right (λ q, mul_action.orbit_zpowers_equiv g q.out'))

-- PR2
lemma key_equiv_symm_apply {G : Type u} [group G] (H : subgroup G) (g : G)
  (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  (key_equiv H g).symm ⟨q, k⟩ = g ^ (k : ℤ) • q.out' :=
rfl

-- PR2
lemma key_equiv_apply {G : Type u} [group G] (H : subgroup G) (g : G)
  (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : ℤ) :
  key_equiv H g (g ^ k • q.out') = ⟨q, k⟩ :=
begin
  rw [equiv.apply_eq_iff_eq_symm_apply, key_equiv_symm_apply],
  rw [←inv_smul_eq_iff, ←zpow_neg_one, ←zpow_mul, mul_neg_one, ←mul_smul, ←zpow_add, add_comm,
    ←sub_eq_add_neg, mul_action.zpow_smul_eq_iff_minimal_period_dvd, ←zmod.int_coe_eq_int_coe_iff_dvd_sub],
  rw [zmod.int_cast_cast, zmod.cast_int_cast'],
end

end equiv_stuff

section transversal_stuff

-- PR3
def key_transversal_set {G : Type*} [group G] (H : subgroup G) (g : G) : set G :=
set.range (λ q, g ^ ((key_equiv H g q).2 : ℤ)  * (key_equiv H g q).1.out'.out')

-- PR3
def key_transversal {G : Type*} [group G] (H : subgroup G) (g : G) : subgroup.left_transversals (H : set G) :=
⟨key_transversal_set H g, subgroup.range_mem_left_transversals (λ q, by rw [←smul_eq_mul,
  mul_action.quotient.coe_smul_out', ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply])⟩

-- PR3
lemma key_transversal_apply {G : Type*} [group G] (H : subgroup G) (g : G) (q : G ⧸ H) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 q) =
    g ^ ((key_equiv H g q).2 : ℤ) * (key_equiv H g q).1.out'.out' :=
subgroup.mem_left_transversals.to_equiv_apply (λ q, by rw [←smul_eq_mul, mul_action.quotient.coe_smul_out',
  ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply]) q

-- PR3
lemma key_transversal_apply' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
    g ^ (k : ℤ) * q.out'.out' :=
by rw [key_transversal_apply, ←key_equiv_symm_apply, equiv.apply_symm_apply]

-- PR4
lemma key_transversal_apply'' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (g • key_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
    if k = 0 then g ^ function.minimal_period ((•) g) q.out' * q.out'.out'
      else g ^ (k : ℤ) * q.out'.out' :=
begin
  rw [subgroup.smul_apply_eq_smul_apply_inv_smul, key_transversal_apply, ←mul_smul, ←zpow_neg_one,
      ←zpow_add, key_equiv_apply, smul_eq_mul, ←mul_assoc, ←zpow_one_add,
      int.cast_add, int.cast_neg, int.cast_one, zmod.int_cast_cast, zmod.cast_id', id.def],

  rw [←sub_eq_neg_add, zmod.cast_sub_one, add_sub_cancel'_right],
  by_cases hk : k = 0,
  { rw [if_pos hk, if_pos hk, int.nat_cast_eq_coe_nat, zpow_coe_nat] },
  { rw [if_neg hk, if_neg hk] },
end

end transversal_stuff

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

section explicit_computation

variables (H)

@[to_additive] lemma lem0 {α β : Type*} [group α] [mul_action α β] (a : α) (b : β)
  [fintype (mul_action.orbit (zpowers a) b)] :
  function.minimal_period ((•) a) b = fintype.card (mul_action.orbit (zpowers a) b) :=
by rw [←fintype.of_equiv_card (mul_action.orbit_zpowers_equiv a b), zmod.card]

@[to_additive] instance {α β : Type*} [group α] [mul_action α β] (a : α) (b : β)
  [fintype (mul_action.orbit (zpowers a) b)] :
  fact (0 < function.minimal_period ((•) a) b) :=
⟨begin
  rw lem0,
  exact fintype.card_pos_iff.mpr ⟨⟨b, mul_action.mem_orbit_self b⟩⟩,
end⟩

open_locale classical

lemma transfer_computation (g : G) : transfer ϕ g =
  ∏ (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))),
    ϕ ⟨q.out'.out'⁻¹ * g ^ (function.minimal_period ((•) g) q.out') * q.out'.out',
      by rw [mul_assoc, ←quotient_group.eq', ←smul_eq_mul, mul_action.quotient.mk_smul_out',
        quotient_group.out_eq', eq_comm, mul_action.pow_smul_eq_iff_minimal_period_dvd]⟩ :=
begin
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (key_transversal H g) g
  ... = _ : ((key_equiv H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only,
  simp only [key_equiv_symm_apply, key_transversal_apply', key_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod (function.minimal_period ((•) g) q.out')),
  { simp only [if_pos, zmod.cast_zero, zpow_zero, one_mul, mul_assoc] },
  { intros k hk,
    simp only [if_neg hk, inv_mul_self],
    exact ϕ.map_one },
end

lemma silly_lemma {G α : Type*} [group G] [mul_action G α] (g : G) [fintype α] :
  ∏ (q : quotient (mul_action.orbit_rel (zpowers g) α)),
    (⟨g, mem_zpowers g⟩ : zpowers g) ^ function.minimal_period ((•) g) q.out' =
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ fintype.card α :=
begin
  rw [finset.prod_pow_eq_pow_sum],
  congr,
  simp only [lem0, ←fintype.card_sigma],
  convert fintype.card_congr (mul_action.self_equiv_sigma_orbits (zpowers g) α).symm,
end

lemma transfer_eq_pow'_aux (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  g ^ H.index ∈ H :=
begin
  replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H :=
  λ k g₀ hk, (_root_.congr_arg (∈ H) (key k g₀ hk)).mp hk,
  replace key : ∀ q : G ⧸ H, g ^ function.minimal_period ((•) g) q ∈ H :=
  λ q, key (function.minimal_period ((•) g) q) q.out' (by rw [mul_assoc, ←quotient_group.eq',
    ←smul_eq_mul, mul_action.quotient.mk_smul_out',
    quotient_group.out_eq', eq_comm, mul_action.pow_smul_eq_iff_minimal_period_dvd]),
  replace key : ∀ (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))), q ∈ finset.univ →
    (⟨g, mem_zpowers g⟩ : zpowers g) ^ function.minimal_period ((•) g) q.out' ∈ H.subgroup_of (zpowers g) :=
  λ q hq, key q.out',
  have key := @subgroup.prod_mem (zpowers g) _ (H.subgroup_of (zpowers g))
    (quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))) finset.univ
    (λ q, (⟨g, mem_zpowers g⟩ : zpowers g) ^ function.minimal_period ((•) g) q.out') key,
  rwa [silly_lemma, ←index_eq_card] at key,
end

lemma transfer_eq_pow' (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow'_aux H g key⟩ :=
begin
  have key : ∀ (k : ℕ) (g₀ : G) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H),
    (⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = (⟨g ^ k, (_root_.congr_arg (∈ H) (key k g₀ hk)).mp hk⟩ : H) :=
  λ k g₀ hg, subtype.ext (key k g₀ hg),
  rw transfer_computation,
  simp only [key],
  rw [←finset.prod_to_list, list.prod_map_hom],
  apply congr_arg ϕ,
  apply (show function.injective H.subtype, from subtype.coe_injective),
  rw [←list.prod_map_hom],
  change (list.map (λ q, _) _).prod = _,
  have key : ∀ (k : ℕ) (hk : g ^ k ∈ H), H.subtype ⟨g ^ k, hk⟩ = (zpowers g).subtype (⟨g, mem_zpowers g⟩ ^ k),
  { intros k hk,
    refl },
  simp only [key],
  rw [list.prod_map_hom, finset.prod_to_list, silly_lemma, index_eq_card],
end

end explicit_computation

section center_transfer

lemma transfer_eq_pow [fintype (G ⧸ center G)] (g : G) :
  transfer (monoid_hom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
begin
  refine transfer_eq_pow' (center G) (monoid_hom.id (center G)) g (λ k g₀ hk, _),
  rw [normal.mem_comm_iff, mul_inv_cancel_left] at hk,
  { rw [mul_assoc, ←hk g₀, inv_mul_cancel_left] },
  { apply_instance },
end

noncomputable def transfer_pow [fintype (G ⧸ center G)] : G →* center G :=
{ to_fun := λ g, ⟨g ^ (center G).index, (center G).pow_index_mem g⟩,
  map_one' := subtype.ext (one_pow (center G).index),
  map_mul' := λ a b, by simp_rw [←show ∀ g, (_ : center G) = _, from transfer_eq_pow, map_mul] }

noncomputable def transfer_pow' (h : (center G).index ≠ 0) : G →* center G :=
begin
  haveI : fintype (G ⧸ center G) := fintype_of_index_ne_zero h,
  exact transfer_pow,
end

end center_transfer

section burnside_transfer

lemma key_sylow_lemma {p : ℕ} {G : Type*} [group G] (g : G) [fintype (sylow p G)] (P : sylow p G)
  {x : G} (hx : x ∈ (P.1.subtype.comp P.1.center.subtype).range) (hy : g⁻¹ * x * g ∈
    (P.1.subtype.comp P.1.center.subtype).range) : ∃ n ∈ P.1.normalizer, g⁻¹ * x * g = n⁻¹ * x * n :=
begin
  /-
  We know that `P ≤ C(x)` and `P ≤ C(g⁻¹ * x * g)`.
  Then `g • P ≤ C(g⁻¹ * x * g)` and `P ≤ C(g⁻¹ * x * g)`.
  Then `h • g • P
  -/
  sorry
end

#print sylow.mul_action.is_pretransitive

lemma key_sylow_lemma' {p : ℕ} {G : Type*} [group G] (g : G) [fintype (sylow p G)] (P : sylow p G)
  (hP : P.1.is_commutative)
  {x : G} (hx : x ∈ P.1) (hy : g⁻¹ * x * g ∈ P.1) : ∃ n ∈ P.1.normalizer, g⁻¹ * x * g = n⁻¹ * x * n :=
begin
  suffices : (P.1.subtype.comp P.1.center.subtype).range = P.1,
  { rw ← this at hx hy,
    exact key_sylow_lemma g P hx hy },
  rw [comm_group.center_eq_top, range_eq_map, ←map_map, ←range_eq_map, subtype_range,
      ←range_eq_map, subtype_range],
end

noncomputable def burnside_transfer {p : ℕ} {G : Type*} [group G] (P : sylow p G)
  [fintype (G ⧸ P.1)] (hP : P.1.normalizer ≤ P.1.centralizer) : G →* P.1 :=
begin
  haveI : P.1.is_commutative := ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩,
  exact transfer (monoid_hom.id P.1),
end

lemma burnside_transfer_surjective {p : ℕ} {G : Type*} [group G] (P : sylow p G)
  [fintype (G ⧸ P.1)] [fintype G]
  (hP : P.1.normalizer ≤ P.1.centralizer) : function.surjective (burnside_transfer P hP) :=
begin
  classical,
  haveI P_comm : P.1.is_commutative := ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩,
  suffices : P.1 ⊓ (burnside_transfer P hP).ker = ⊥,
  { -- todo: make this a separate lemma
    sorry },
  refine le_bot_iff.mp (λ g hg, _),
  rw [mem_inf, mem_ker] at hg,
  have key := transfer_eq_pow' P.1 (monoid_hom.id P.1) g (λ k g₀ hk, begin
    obtain ⟨n, hn, key⟩ := key_sylow_lemma' g₀ P P_comm (P.1.pow_mem hg.1 k) hk,
    rw [key, mul_assoc, hP hn (g ^ k) (P.1.pow_mem hg.1 k), inv_mul_cancel_left],
  end),
  have key' : (fintype.card P.1).coprime P.1.index,
  { -- todo: make this a lemma
    sorry },
  let ϕ := pow_coprime key',
  have : ϕ ⟨g, hg.1⟩ = 1 := key.symm.trans hg.2,
  replace this := this.trans (pow_coprime_one key').symm,
  replace this := ϕ.injective this,
  exact subtype.ext_iff.mp this,
end

end burnside_transfer

end monoid_hom
