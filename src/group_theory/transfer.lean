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
- `transfer_center_pow`: The transfer homomorphism `G →*  center G`.
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
∏ q, ϕ ⟨(α q)⁻¹ * β q, quotient_group.left_rel_apply.mp $
  quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

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

open mul_action subgroup subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer [fintype (G ⧸ H)] : G →* A :=
let T : left_transversals (H : set G) := inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

variables (T : left_transversals (H : set G))

@[to_additive] lemma transfer_def [fintype (G ⧸ H)] (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

/-- Explicit computation of the transfer homomorphism. -/
lemma transfer_eq_prod_quotient_orbit_rel_zpowers_quot [fintype (G ⧸ H)]
  (g : G) [fintype (quotient (orbit_rel (zpowers g) (G ⧸ H)))] :
  transfer ϕ g = ∏ (q : quotient (orbit_rel (zpowers g) (G ⧸ H))),
    ϕ ⟨q.out'.out'⁻¹ * g ^ function.minimal_period ((•) g) q.out' * q.out'.out',
      quotient_group.out'_conj_pow_minimal_period_mem H g q.out'⟩ :=
begin
  classical,
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (transfer_transversal H g) g
  ... = _ : ((quotient_equiv_sigma_zmod H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only [quotient_equiv_sigma_zmod_symm_apply,
    transfer_transversal_apply', transfer_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod (function.minimal_period ((•) g) q.out')) (λ k hk, _),
  { simp only [if_pos, zmod.cast_zero, zpow_zero, one_mul, mul_assoc] },
  { simp only [if_neg hk, inv_mul_self],
    exact map_one ϕ },
end

/-- Auxillary lemma in order to state `transfer_eq_pow`. -/
lemma transfer_eq_pow_aux (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  g ^ H.index ∈ H :=
begin
  by_cases hH : H.index = 0,
  { rw [hH, pow_zero],
    exact H.one_mem },
  haveI := fintype_of_index_ne_zero hH,
  classical,
  replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H :=
  λ k g₀ hk, (_root_.congr_arg (∈ H) (key k g₀ hk)).mp hk,
  replace key : ∀ q : G ⧸ H, g ^ function.minimal_period ((•) g) q ∈ H :=
  λ q, key (function.minimal_period ((•) g) q) q.out'
    (quotient_group.out'_conj_pow_minimal_period_mem H g q),
  let f : quotient (orbit_rel (zpowers g) (G ⧸ H)) → zpowers g :=
  λ q, (⟨g, mem_zpowers g⟩ : zpowers g) ^ function.minimal_period ((•) g) q.out',
  have hf : ∀ q, f q ∈ H.subgroup_of (zpowers g) := λ q, key q.out',
  replace key := subgroup.prod_mem (H.subgroup_of (zpowers g)) (λ q (hq : q ∈ finset.univ), hf q),
  simpa only [minimal_period_eq_card, finset.prod_pow_eq_pow_sum, fintype.card_sigma,
    fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)), index_eq_card] using key,
end

lemma transfer_eq_pow [fintype (G ⧸ H)] (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ :=
begin
  classical,
  change ∀ k g₀ (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key,
  rw [transfer_eq_prod_quotient_orbit_rel_zpowers_quot, ←finset.prod_to_list, list.prod_map_hom],
  refine congr_arg ϕ (subtype.coe_injective _),
  rw [H.coe_mk, ←(zpowers g).coe_mk g (mem_zpowers g), ←(zpowers g).coe_pow, (zpowers g).coe_mk,
      index_eq_card, fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)),
      fintype.card_sigma, ←finset.prod_pow_eq_pow_sum, ←finset.prod_to_list],
  simp only [coe_list_prod, list.map_map, ←minimal_period_eq_card],
  congr' 2,
  funext,
  apply key,
end

lemma transfer_center_eq_pow [fintype (G ⧸ center G)] (g : G) :
  transfer (monoid_hom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
transfer_eq_pow (id (center G)) g (λ k _ hk, by rw [←mul_right_inj, hk, mul_inv_cancel_right])

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transfer_center_pow [fintype (G ⧸ center G)] : G →* center G :=
{ to_fun := λ g, ⟨g ^ (center G).index, (center G).pow_index_mem g⟩,
  map_one' := subtype.ext (one_pow (center G).index),
  map_mul' := λ a b, by simp_rw [←show ∀ g, (_ : center G) = _,
    from transfer_center_eq_pow, map_mul] }

@[simp] lemma transfer_center_pow_apply [fintype (G ⧸ center G)] (g : G) :
  ↑(transfer_center_pow g) = g ^ (center G).index :=
rfl

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transfer_center_pow' (h : (center G).index ≠ 0) : G →* center G :=
@transfer_center_pow G _ (fintype_of_index_ne_zero h)

@[simp] lemma transfer_center_pow'_apply (h : (center G).index ≠ 0) (g : G) :
  ↑(transfer_center_pow' h g) = g ^ (center G).index :=
rfl

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
    { rw [sylow.smul_subtype, sylow.ext_iff, sylow.coe_subtype, sylow.coe_subtype] at hh,
      rw ← sylow.smul_eq_iff_mem_normalizer,
      rw mul_smul,
      refine sylow.ext (P.3 (h • g • P).2 _),
      have key0 : P.1 ≤ H.subtype.range,
      { rwa [subtype_range, key], },
      rw ← comap_le_comap_of_le_range key0,
      exact hh.ge },
    { rw [←mul_assoc, mul_assoc, mul_assoc _ x, h.prop x (mem_zpowers x)],
      group } },
  { rw key,
    rintros - ⟨z, hz, rfl⟩,
    simp only [mul_distrib_mul_action.to_monoid_End_apply,
      mul_distrib_mul_action.to_monoid_hom_apply, mul_aut.smul_def,
      mul_aut.conj_apply],
    rw [←mul_assoc, eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, mul_assoc, ←mul_assoc g⁻¹, hy z hz,
        mul_assoc, mul_assoc, mul_inv_cancel_left] },
  { rwa [key] },
end

lemma key_sylow_lemma' {p : ℕ} [fact p.prime] {G : Type*} [group G] (g : G) [fintype (sylow p G)] (P : sylow p G)
  (hP : P.1.is_commutative)
  {x : G} (hx : x ∈ P.1) (hy : g⁻¹ * x * g ∈ P.1) : ∃ n ∈ P.1.normalizer, g⁻¹ * x * g = n⁻¹ * x * n :=
begin
  suffices : P.1 ≤ P.1.centralizer,
  { exact key_sylow_lemma g P (this hx) (this hy) },
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

/-- Auxillary lemma in order to state `burnside_transfer_eq_pow`. -/
lemma burnside_transfer_eq_pow_aux {p : ℕ} [fact p.prime] {G : Type*} [group G]
  [fintype (sylow p G)] (P : sylow p G) (hP : P.1.normalizer ≤ P.1.centralizer)
  (g : G) (hg : g ∈ P) (k : ℕ) (g₀ : G) (h : g₀⁻¹ * g ^ k * g₀ ∈ P) : g₀⁻¹ * g ^ k * g₀ = g ^ k :=
begin
  obtain ⟨n, hn, key⟩ := key_sylow_lemma' g₀ P ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩
    (P.1.pow_mem hg k) h,
  rw [key, mul_assoc, hP hn (g ^ k) (P.1.pow_mem hg k), inv_mul_cancel_left],
end

-- TODO: `fintype (G ⧸ P.1)` implies `fintype (sylow p G)`.

lemma burnside_transfer_eq_pow {p : ℕ} [fact p.prime] {G : Type*} [group G] [fintype (sylow p G)]
  (P : sylow p G) [fintype (G ⧸ P.1)] (hP : P.1.normalizer ≤ P.1.centralizer)
  (g : G) (hg : g ∈ P) : burnside_transfer P hP g = ⟨g ^ P.1.index,
    transfer_eq_pow_aux g (burnside_transfer_eq_pow_aux P hP g hg)⟩ :=
by apply transfer_eq_pow

lemma burnside_transfer_ker_disjoint {p : ℕ} [fact p.prime] {G : Type*} [group G] (P : sylow p G)
  [fintype (G ⧸ P.1)] [fintype G]
  (hP : P.1.normalizer ≤ P.1.centralizer) : disjoint (burnside_transfer P hP).ker P.1 :=
begin
  classical,
  intros g hg,
  have key := burnside_transfer_eq_pow P hP g hg.2,
  have key' : (fintype.card P.1).coprime P.1.index := P.card_coprime_index,
  have : pow_coprime P.card_coprime_index ⟨g, hg.2⟩ = 1 := key.symm.trans hg.1,
  rwa [←pow_coprime_one, equiv.apply_eq_iff_eq, subtype.ext_iff] at this,
end

lemma burnside_transfer_ker_disjoint' {p : ℕ} [fact p.prime] {G : Type*} [group G] (P Q : sylow p G)
  [fintype (G ⧸ P.1)] [fintype G]
  (hP : P.1.normalizer ≤ P.1.centralizer) : disjoint (burnside_transfer P hP).ker Q.1 :=
begin
  sorry,
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
