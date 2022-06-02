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

open mul_action subgroup subgroup.left_transversals

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

lemma transfer_eq_prod_quotient_orbit_rel_zpowers_quot
  (g : G) [fintype (quotient (orbit_rel (zpowers g) (G ⧸ H)))] :
  transfer ϕ g =
    ∏ (q : quotient (orbit_rel (zpowers g) (G ⧸ H))),
      ϕ ⟨q.out'.out'⁻¹ * g ^ (function.minimal_period ((•) g) q.out') * q.out'.out',
        by rw [mul_assoc, ←quotient_group.eq', ←smul_eq_mul, quotient.mk_smul_out',
          quotient_group.out_eq', eq_comm, pow_smul_eq_iff_minimal_period_dvd]⟩ :=
begin
  classical,
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (transfer_transversal H g) g
  ... = _ : ((quotient_equiv_sigma_zmod H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only [quotient_equiv_sigma_zmod_symm_apply,
    transfer_transversal_apply', transfer_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod (function.minimal_period ((•) g) q.out')),
  { simp only [if_pos, zmod.cast_zero, zpow_zero, one_mul, mul_assoc] },
  { intros k hk,
    simp only [if_neg hk, inv_mul_self],
    exact map_one ϕ },
end

lemma transfer_eq_pow'_aux (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  g ^ H.index ∈ H :=
begin
  classical,
  replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H :=
  λ k g₀ hk, (_root_.congr_arg (∈ H) (key k g₀ hk)).mp hk,
  replace key : ∀ q : G ⧸ H, g ^ function.minimal_period ((•) g) q ∈ H :=
  λ q, key (function.minimal_period ((•) g) q) q.out' (by rw [mul_assoc, ←quotient_group.eq',
    ←smul_eq_mul, quotient.mk_smul_out',
    quotient_group.out_eq', eq_comm, pow_smul_eq_iff_minimal_period_dvd]),
  let f : quotient (orbit_rel (zpowers g) (G ⧸ H)) → zpowers g :=
  λ q, (⟨g, mem_zpowers g⟩ : zpowers g) ^ function.minimal_period ((•) g) q.out',
  have hf : ∀ q, f q ∈ H.subgroup_of (zpowers g) := λ q, key q.out',
  replace key := subgroup.prod_mem (H.subgroup_of (zpowers g)) (λ q (hq : q ∈ finset.univ), hf q),
  simpa only [minimal_period_eq_card, finset.prod_pow_eq_pow_sum, ←fintype.card_sigma,
    ←fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)), ←index_eq_card] using key,
end

lemma transfer_eq_pow' (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow'_aux H g key⟩ :=
begin
  classical,
  have key : ∀ (k : ℕ) (g₀ : G) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H),
    (⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = (⟨g ^ k, (_root_.congr_arg (∈ H) (key k g₀ hk)).mp hk⟩ : H) :=
  λ k g₀ hg, subtype.ext (key k g₀ hg),
  rw transfer_eq_prod_quotient_orbit_rel_zpowers_quot,
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
  rw [list.prod_map_hom, finset.prod_to_list],
  simp only [minimal_period_eq_card, finset.prod_pow_eq_pow_sum, ←fintype.card_sigma,
    ←fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)), ←index_eq_card],
end

end explicit_computation

section center_transfer

lemma transfer_eq_pow [fintype (G ⧸ center G)] (g : G) :
  transfer (monoid_hom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
begin
  refine transfer_eq_pow' (center G) (monoid_hom.id (center G)) g (λ k g₀ hk, _),
  rw [←mul_right_inj g₀⁻¹, hk, mul_inv_cancel_right],
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

lemma key_sylow_lemma {p : ℕ} [fact p.prime] {G : Type*} [group G] (g : G) [fintype (sylow p G)] (P : sylow p G)
  {x : G} (hx : x ∈ P.1.centralizer) (hy : g⁻¹ * x * g ∈ (P : subgroup G).centralizer) :
  ∃ n ∈ (P : subgroup G).normalizer, g⁻¹ * x * g = n⁻¹ * x * n :=
begin
  let H := (zpowers x).centralizer,
  have key : ∀ K : subgroup G, K ≤ H ↔ x ∈ K.centralizer,
  { refine λ K, ⟨λ h k hk, (h hk x (mem_zpowers x)).symm, λ h k hk, _⟩,
    rintro _ ⟨m, rfl⟩,
    exact (commute.zpow_right (h k hk) m).symm },
  obtain ⟨h, hh⟩ := mul_action.exists_smul_eq H ((g • P).subtype (show _ ≤ H, from _))
    (P.subtype (show _ ≤ H, from _)),
  { refine ⟨h * g, _, _⟩,
    { rw ← sylow.smul_eq_iff_mem_normalizer,
      rw mul_smul,
      simp only [sylow.ext_iff, sylow.coe_subgroup_smul, sylow.coe_subtype] at hh ⊢,
      sorry },
    { rw [←mul_assoc, mul_assoc, mul_assoc _ x, h.prop x (mem_zpowers x)],
      group } },
  { rw key,
    rintros - ⟨z, hz, rfl⟩,
    simp only [mul_distrib_mul_action.to_monoid_End_apply,
      mul_distrib_mul_action.to_monoid_hom_apply, mul_aut.smul_def,
      mul_aut.conj_apply],
    have key := hy z hz,
    rw [←mul_assoc, eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, mul_assoc, ←mul_assoc g⁻¹, key,
        mul_assoc, mul_assoc, mul_inv_cancel_left] },
  { rwa [key] },
end

lemma key_sylow_lemma' {p : ℕ} [fact p.prime] {G : Type*} [group G] (g : G) [fintype (sylow p G)] (P : sylow p G)
  (hP : P.1.is_commutative)
  {x : G} (hx : x ∈ P.1) (hy : g⁻¹ * x * g ∈ P.1) : ∃ n ∈ P.1.normalizer, g⁻¹ * x * g = n⁻¹ * x * n :=
begin
  suffices : P.1 ≤ P.1.centralizer,
  { replace hx := this hx,
    replace hy := this hy,
    exact key_sylow_lemma g P hx hy },
  refine λ z hz w hw, _,
  have this := hP.1.1,
  exact subtype.ext_iff.mp (this (⟨w, hw⟩ : P.1) (⟨z, hz⟩ : P.1)),
end

noncomputable def burnside_transfer {p : ℕ} {G : Type*} [group G] (P : sylow p G)
  [fintype (G ⧸ P.1)] (hP : P.1.normalizer ≤ P.1.centralizer) : G →* P.1 :=
begin
  haveI : P.1.is_commutative := ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩,
  exact transfer (monoid_hom.id P.1),
end

lemma burnside_transfer_ker_inf {p : ℕ} [fact p.prime] {G : Type*} [group G] (P : sylow p G)
  [fintype (G ⧸ P.1)] [fintype G]
  (hP : P.1.normalizer ≤ P.1.centralizer) : (burnside_transfer P hP).ker ⊓ P.1 = ⊥ :=
begin
  classical,
  haveI P_comm : P.1.is_commutative := ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩,
  refine le_bot_iff.mp (λ g hg, _),
  have key := transfer_eq_pow' P.1 (monoid_hom.id P.1) g (λ k g₀ hk, begin
    obtain ⟨n, hn, key⟩ := key_sylow_lemma' g₀ P P_comm (P.1.pow_mem hg.2 k) hk,
    rw [key, mul_assoc, hP hn (g ^ k) (P.1.pow_mem hg.2 k), inv_mul_cancel_left],
  end),
  have key' : (fintype.card P.1).coprime P.1.index := P.lema19,
  have : pow_coprime key' ⟨g, hg.2⟩ = 1 := key.symm.trans hg.1,
  rwa [←pow_coprime_one, equiv.apply_eq_iff_eq, subtype.ext_iff] at this,
end

lemma burnside_transfer_surjective {p : ℕ} {G : Type*} [group G] (P : sylow p G)
  [fintype (G ⧸ P.1)] [fintype G]
  (hP : P.1.normalizer ≤ P.1.centralizer) : function.surjective (burnside_transfer P hP) :=
begin
  classical,
  haveI P_comm : P.1.is_commutative := ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩,
  sorry,
end

end burnside_transfer

end monoid_hom
