/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.sylow
import group_theory.transfer

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `exists_right_complement'_of_coprime` : The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement'_of_coprime`  The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/

open_locale big_operators

namespace subgroup

section schur_zassenhaus_abelian

open mul_opposite mul_action subgroup.left_transversals mem_left_transversals

variables {G : Type*} [group G] (H : subgroup G) [is_commutative H] [fintype (G ⧸ H)]
  (α β : left_transversals (H : set G))

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation. -/
def quotient_diff :=
quotient (setoid.mk (λ α β, diff (monoid_hom.id H) α β = 1) ⟨λ α, diff_self (monoid_hom.id H) α,
  λ α β h, by rw [←diff_inv, h, inv_one], λ α β γ h h', by rw [←diff_mul_diff, h, h', one_mul]⟩)

instance : inhabited H.quotient_diff := quotient.inhabited _

lemma smul_diff_smul' [hH : normal H] (g : Gᵐᵒᵖ) :
  diff (monoid_hom.id H) (g • α) (g • β) = ⟨g.unop⁻¹ * (diff (monoid_hom.id H) α β : H) * g.unop,
    hH.mem_comm ((congr_arg (∈ H) (mul_inv_cancel_left _ _)).mpr (set_like.coe_mem _))⟩ :=
begin
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨g.unop⁻¹ * h * g.unop,
      hH.mem_comm ((congr_arg (∈ H) (mul_inv_cancel_left _ _)).mpr (set_like.coe_mem _))⟩,
    map_one' := by rw [subtype.ext_iff, coe_mk, coe_one, mul_one, inv_mul_self],
    map_mul' := λ h₁ h₂, by rw [subtype.ext_iff, coe_mk, coe_mul, coe_mul, coe_mk, coe_mk,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_inv_cancel_left] },
  refine eq.trans (finset.prod_bij' (λ q _, g⁻¹ • q) (λ q _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, g • q) (λ q _, finset.mem_univ _) (λ q _, smul_inv_smul g q)
    (λ q _, inv_smul_smul g q)) (map_prod ϕ _ _).symm,
  simp_rw [monoid_hom.id_apply, monoid_hom.coe_mk, coe_mk, smul_apply_eq_smul_apply_inv_smul,
    smul_eq_mul_unop, mul_inv_rev, mul_assoc],
end

variables {H} [normal H]

instance : mul_action G H.quotient_diff :=
{ smul := λ g, quotient.map' (λ α, op g⁻¹ • α) (λ α β h, subtype.ext (by rwa [smul_diff_smul',
    coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_right_eq_self, ←coe_one, ←subtype.ext_iff])),
  mul_smul := λ g₁ g₂ q, quotient.induction_on' q (λ T, congr_arg quotient.mk'
    (by rw mul_inv_rev; exact mul_smul (op g₁⁻¹) (op g₂⁻¹) T)),
  one_smul := λ q, quotient.induction_on' q (λ T, congr_arg quotient.mk'
    (by rw inv_one; apply one_smul Gᵐᵒᵖ T)) }

lemma smul_diff' (h : H) :
  diff (monoid_hom.id H) α ((op (h : G)) • β) = diff (monoid_hom.id H) α β * h ^ H.index :=
begin
  rw [diff, diff, index_eq_card, ←finset.card_univ, ←finset.prod_const, ←finset.prod_mul_distrib],
  refine finset.prod_congr rfl (λ q _, _),
  simp_rw [subtype.ext_iff, monoid_hom.id_apply, coe_mul, coe_mk, mul_assoc, mul_right_inj],
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, unop_op,
      mul_left_inj, ←subtype.ext_iff, equiv.apply_eq_iff_eq, inv_smul_eq_iff],
  exact self_eq_mul_right.mpr ((quotient_group.eq_one_iff _).mpr h.2),
end

variables [fintype H]

lemma eq_one_of_smul_eq_one (hH : nat.coprime (fintype.card H) H.index)
  (α : H.quotient_diff) (h : H) : h • α = α → h = 1 :=
quotient.induction_on' α $ λ α hα, (pow_coprime hH).injective $
  calc h ^ H.index = diff (monoid_hom.id H) ((op ((h⁻¹ : H) : G)) • α) α :
    by rw [←diff_inv, smul_diff', diff_self, one_mul, inv_pow, inv_inv]
  ... = 1 ^ H.index : (quotient.exact' hα).trans (one_pow H.index).symm

lemma exists_smul_eq (hH : nat.coprime (fintype.card H) H.index)
  (α β : H.quotient_diff) : ∃ h : H, h • α = β :=
quotient.induction_on' α (quotient.induction_on' β (λ β α, exists_imp_exists (λ n, quotient.sound')
  ⟨(pow_coprime hH).symm (diff (monoid_hom.id H) β α), (diff_inv _ _ _).symm.trans
  (inv_eq_one.mpr ((smul_diff' β α ((pow_coprime hH).symm (diff (monoid_hom.id H) β α))⁻¹).trans
  (by rw [inv_pow, ←pow_coprime_apply hH, equiv.apply_symm_apply, mul_inv_self])))⟩))

lemma is_complement'_stabilizer_of_coprime {α : H.quotient_diff}
  (hH : nat.coprime (fintype.card H) H.index) : is_complement' H (stabilizer G α) :=
is_complement'_stabilizer α (eq_one_of_smul_eq_one hH α) (λ g, exists_smul_eq hH (g • α) α)

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma exists_right_complement'_of_coprime_aux
  (hH : nat.coprime (fintype.card H) H.index) : ∃ K : subgroup G, is_complement' H K :=
nonempty_of_inhabited.elim (λ α, ⟨stabilizer G α, is_complement'_stabilizer_of_coprime hH⟩)

end schur_zassenhaus_abelian

open_locale classical

universe u

namespace schur_zassenhaus_induction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/

variables {G : Type u} [group G] [fintype G] {N : subgroup G} [normal N]
  (h1 : nat.coprime (fintype.card N) N.index)
  (h2 : ∀ (G' : Type u) [group G'] [fintype G'], by exactI
    ∀ (hG'3 : fintype.card G' < fintype.card G)
    {N' : subgroup G'} [N'.normal] (hN : nat.coprime (fintype.card N') N'.index),
    ∃ H' : subgroup G', is_complement' N' H')
  (h3 : ∀ H : subgroup G, ¬ is_complement' N H)

include h1 h2 h3

/-! We will arrive at a contradiction via the following steps:
 * step 0: `N` (the normal Hall subgroup) is nontrivial.
 * step 1: If `K` is a subgroup of `G` with `K ⊔ N = ⊤`, then `K = ⊤`.
 * step 2: `N` is a minimal normal subgroup, phrased in terms of subgroups of `G`.
 * step 3: `N` is a minimal normal subgroup, phrased in terms of subgroups of `N`.
 * step 4: `p` (`min_fact (fintype.card N)`) is prime (follows from step0).
 * step 5: `P` (a Sylow `p`-subgroup of `N`) is nontrivial.
 * step 6: `N` is a `p`-group (applies step 1 to the normalizer of `P` in `G`).
 * step 7: `N` is abelian (applies step 3 to the center of `N`).
-/

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
@[nolint unused_arguments] private lemma step0 : N ≠ ⊥ :=
begin
  unfreezingI { rintro rfl },
  exact h3 ⊤ is_complement'_bot_top,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step1 (K : subgroup G) (hK : K ⊔ N = ⊤) : K = ⊤ :=
begin
  contrapose! h3,
  have h4 : (N.comap K.subtype).index = N.index,
  { rw [←N.relindex_top_right, ←hK],
    exact relindex_eq_relindex_sup K N },
  have h5 : fintype.card K < fintype.card G,
  { rw ← K.index_mul_card,
    exact lt_mul_of_one_lt_left fintype.card_pos (one_lt_index_of_ne_top h3) },
  have h6 : nat.coprime (fintype.card (N.comap K.subtype)) (N.comap K.subtype).index,
  { rw h4,
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype subtype.coe_injective) },
  obtain ⟨H, hH⟩ := h2 K h5 h6,
  replace hH : fintype.card (H.map K.subtype) = N.index :=
  ((set.card_image_of_injective _ subtype.coe_injective).trans (nat.mul_left_injective
    fintype.card_pos (hH.symm.card_mul.trans (N.comap K.subtype).index_mul_card.symm))).trans h4,
  have h7 : fintype.card N * fintype.card (H.map K.subtype) = fintype.card G,
  { rw [hH, ←N.index_mul_card, mul_comm] },
  have h8 : (fintype.card N).coprime (fintype.card (H.map K.subtype)),
  { rwa hH },
  exact ⟨H.map K.subtype, is_complement'_of_coprime h7 h8⟩,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step2 (K : subgroup G) [K.normal] (hK : K ≤ N) : K = ⊥ ∨ K = N :=
begin
  have : function.surjective (quotient_group.mk' K) := quotient.surjective_quotient_mk',
  have h4 := step1 h1 h2 h3,
  contrapose! h4,
  have h5 : fintype.card (G ⧸ K) < fintype.card G,
  { rw [←index_eq_card, ←K.index_mul_card],
    refine lt_mul_of_one_lt_right (nat.pos_of_ne_zero index_ne_zero_of_fintype)
      (K.one_lt_card_iff_ne_bot.mpr h4.1) },
  have h6 : nat.coprime (fintype.card (N.map (quotient_group.mk' K)))
    (N.map (quotient_group.mk' K)).index,
  { have index_map := N.index_map_eq this (by rwa quotient_group.ker_mk),
    have index_pos : 0 < N.index := nat.pos_of_ne_zero index_ne_zero_of_fintype,
    rw index_map,
    refine h1.coprime_dvd_left _,
    rw [←nat.mul_dvd_mul_iff_left index_pos, index_mul_card, ←index_map, index_mul_card],
    exact K.card_quotient_dvd_card },
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6,
  refine ⟨H.comap (quotient_group.mk' K), _, _⟩,
  { have key : (N.map (quotient_group.mk' K)).comap (quotient_group.mk' K) = N,
    { refine comap_map_eq_self _,
      rwa quotient_group.ker_mk },
    rwa [←key, comap_sup_eq, hH.symm.sup_eq_top, comap_top] },
  { rw ← comap_top (quotient_group.mk' K),
    intro hH',
    rw [comap_injective this hH', is_complement'_top_right,
        map_eq_bot_iff, quotient_group.ker_mk] at hH,
    { exact h4.2 (le_antisymm hK hH) } },
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step3 (K : subgroup N) [(K.map N.subtype).normal] : K = ⊥ ∨ K = ⊤ :=
begin
  have key := step2 h1 h2 h3 (K.map N.subtype) K.map_subtype_le,
  rw ← map_bot N.subtype at key,
  conv at key { congr, skip, to_rhs, rw [←N.subtype_range, N.subtype.range_eq_map] },
  have inj := map_injective (show function.injective N.subtype, from subtype.coe_injective),
  rwa [inj.eq_iff, inj.eq_iff] at key,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step4 : (fintype.card N).min_fac.prime :=
(nat.min_fac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h2 h3)).ne')

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step5 {P : sylow (fintype.card N).min_fac N} : P.1 ≠ ⊥ :=
begin
  haveI : fact ((fintype.card N).min_fac.prime) := ⟨step4 h1 h2 h3⟩,
  exact P.ne_bot_of_dvd_card (fintype.card N).min_fac_dvd,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step6 : is_p_group (fintype.card N).min_fac N :=
begin
  haveI : fact ((fintype.card N).min_fac.prime) := ⟨step4 h1 h2 h3⟩,
  refine sylow.nonempty.elim (λ P, P.2.of_surjective P.1.subtype _),
  rw [←monoid_hom.range_top_iff_surjective, subtype_range],
  haveI : (P.1.map N.subtype).normal := normalizer_eq_top.mp
    (step1 h1 h2 h3 (P.1.map N.subtype).normalizer P.normalizer_sup_eq_top),
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h2 h3),
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
lemma step7 : is_commutative N :=
begin
  haveI := N.bot_or_nontrivial.resolve_left (step0 h1 h2 h3),
  haveI : fact ((fintype.card N).min_fac.prime) := ⟨step4 h1 h2 h3⟩,
  exact ⟨⟨λ g h, eq_top_iff.mp ((step3 h1 h2 h3 N.center).resolve_left
    (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h) g⟩⟩,
end

end schur_zassenhaus_induction

variables {n : ℕ} {G : Type u} [group G]

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma exists_right_complement'_of_coprime_aux' [fintype G] (hG : fintype.card G = n)
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement' N H :=
begin
  unfreezingI { revert G },
  apply nat.strong_induction_on n,
  rintros n ih G _ _ rfl N _ hN,
  refine not_forall_not.mp (λ h3, _),
  haveI := by exactI
    schur_zassenhaus_induction.step7 hN (λ G' _ _ hG', by { apply ih _ hG', refl }) h3,
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN),
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime_of_fintype [fintype G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement' N H :=
exists_right_complement'_of_coprime_aux' rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime
  {N : subgroup G} [N.normal] (hN : nat.coprime (nat.card N) N.index) :
  ∃ H : subgroup G, is_complement' N H :=
begin
  by_cases hN1 : nat.card N = 0,
  { rw [hN1, nat.coprime_zero_left, index_eq_one] at hN,
    rw hN,
    exact ⟨⊥, is_complement'_top_bot⟩ },
  by_cases hN2 : N.index = 0,
  { rw [hN2, nat.coprime_zero_right] at hN,
    haveI := (cardinal.to_nat_eq_one_iff_unique.mp hN).1,
    rw N.eq_bot_of_subsingleton,
    exact ⟨⊤, is_complement'_bot_top⟩ },
  have hN3 : nat.card G ≠ 0,
  { rw ← N.card_mul_index,
    exact mul_ne_zero hN1 hN2 },
  haveI := (cardinal.lt_omega_iff_fintype.mp
    (lt_of_not_ge (mt cardinal.to_nat_apply_of_omega_le hN3))).some,
  rw nat.card_eq_fintype_card at hN,
  exact exists_right_complement'_of_coprime_of_fintype hN,
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime_of_fintype
  [fintype G] {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement' H N :=
Exists.imp (λ _, is_complement'.symm) (exists_right_complement'_of_coprime_of_fintype hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime
  {N : subgroup G} [N.normal] (hN : nat.coprime (nat.card N) N.index) :
  ∃ H : subgroup G, is_complement' H N :=
Exists.imp (λ _, is_complement'.symm) (exists_right_complement'_of_coprime hN)

end subgroup
