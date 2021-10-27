/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/

import group_theory.index
import group_theory.group_action.conj_act
import group_theory.perm.cycle_type
import group_theory.quotient_group

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

open_locale big_operators

open fintype mul_action

variables (p : ℕ) (G : Type*) [group G]

/-- A p-group is a group in which every element has prime power order -/
def is_p_group : Prop := ∀ g : G, ∃ k : ℕ, g ^ (p ^ k) = 1

variables {p} {G}

namespace is_p_group

lemma iff_order_of [hp : fact p.prime] :
  is_p_group p G ↔ ∀ g : G, ∃ k : ℕ, order_of g = p ^ k :=
forall_congr (λ g, ⟨λ ⟨k, hk⟩, exists_imp_exists (by exact λ j, Exists.snd)
  ((nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hk)),
  exists_imp_exists (λ k hk, by rw [←hk, pow_order_of_eq_one])⟩)

lemma of_card [fintype G] {n : ℕ} (hG : card G = p ^ n) : is_p_group p G :=
λ g, ⟨n, by rw [←hG, pow_card_eq_one]⟩

lemma of_bot : is_p_group p (⊥ : subgroup G) :=
of_card (subgroup.card_bot.trans (pow_zero p).symm)

lemma iff_card [fact p.prime] [fintype G] :
  is_p_group p G ↔ ∃ n : ℕ, card G = p ^ n :=
begin
  have hG : 0 < card G := card_pos_iff.mpr has_one.nonempty,
  refine ⟨λ h, _, λ ⟨n, hn⟩, of_card hn⟩,
  suffices : ∀ q ∈ nat.factors (card G), q = p,
  { use (card G).factors.length,
    rw [←list.prod_repeat, ←list.eq_repeat_of_mem this, nat.prod_factors hG] },
  intros q hq,
  obtain ⟨hq1, hq2⟩ := (nat.mem_factors hG).mp hq,
  haveI : fact q.prime := ⟨hq1⟩,
  obtain ⟨g, hg⟩ := equiv.perm.exists_prime_order_of_dvd_card q hq2,
  obtain ⟨k, hk⟩ := (iff_order_of.mp h) g,
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm,
end

section G_is_p_group

variables (hG : is_p_group p G)

include hG

lemma of_injective {H : Type*} [group H] (ϕ : H →* G) (hϕ : function.injective ϕ) :
  is_p_group p H :=
begin
  simp_rw [is_p_group, ←hϕ.eq_iff, ϕ.map_pow, ϕ.map_one],
  exact λ h, hG (ϕ h),
end

lemma to_subgroup (H : subgroup G) : is_p_group p H :=
hG.of_injective H.subtype subtype.coe_injective

lemma of_surjective {H : Type*} [group H] (ϕ : G →* H) (hϕ : function.surjective ϕ) :
  is_p_group p H :=
begin
  refine λ h, exists.elim (hϕ h) (λ g hg, exists_imp_exists (λ k hk, _) (hG g)),
  rw [←hg, ←ϕ.map_pow, hk, ϕ.map_one],
end

lemma to_quotient (H : subgroup G) [H.normal] :
  is_p_group p (quotient_group.quotient H) :=
hG.of_surjective (quotient_group.mk' H) quotient.surjective_quotient_mk'

lemma of_equiv {H : Type*} [group H] (ϕ : G ≃* H) : is_p_group p H :=
hG.of_surjective ϕ.to_monoid_hom ϕ.surjective

variables [hp : fact p.prime]

include hp

lemma index (H : subgroup G) [fintype (quotient_group.quotient H)] :
  ∃ n : ℕ, H.index = p ^ n :=
begin
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normal_core),
  obtain ⟨k, hk1, hk2⟩ := (nat.dvd_prime_pow hp.out).mp ((congr_arg _
    (H.normal_core.index_eq_card.trans hn)).mp (subgroup.index_dvd_of_le H.normal_core_le)),
  exact ⟨k, hk2⟩,
end

variables {α : Type*} [mul_action G α]

lemma card_orbit (a : α) [fintype (orbit G a)] :
  ∃ n : ℕ, card (orbit G a) = p ^ n :=
begin
  let ϕ := orbit_equiv_quotient_stabilizer G a,
  haveI := fintype.of_equiv (orbit G a) ϕ,
  rw [card_congr ϕ, ←subgroup.index_eq_card],
  exact hG.index (stabilizer G a),
end

variables (α) [fintype α] [fintype (fixed_points G α)]

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
lemma card_modeq_card_fixed_points : card α ≡ card (fixed_points G α) [MOD p] :=
begin
  classical,
  calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
    card_congr (equiv.sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
  ... = ∑ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a} : card_sigma _
  ... ≡ ∑ a : fixed_points G α, 1 [MOD p] : _
  ... = _ : by simp; refl,
  rw [←zmod.eq_iff_modeq_nat p, nat.cast_sum, nat.cast_sum],
  have key : ∀ x, card {y // (quotient.mk' y : quotient (orbit_rel G α)) = quotient.mk' x} =
    card (orbit G x) := λ x, by simp only [quotient.eq']; congr,
  refine eq.symm (finset.sum_bij_ne_zero (λ a _ _, quotient.mk' a.1) (λ _ _ _, finset.mem_univ _)
    (λ a₁ a₂ _ _ _ _ h, subtype.eq ((mem_fixed_points' α).mp a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, quotient.induction_on' b (λ b _ hb, _)) (λ a ha _, by
      { rw [key, mem_fixed_points_iff_card_orbit_eq_one.mp a.2] })),
  obtain ⟨k, hk⟩ := hG.card_orbit b,
  have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p)
    (by rwa [pow_one, ←hk, ←nat.modeq_zero_iff_dvd, ←zmod.eq_iff_modeq_nat, ←key])))),
  exact ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, pow_zero]⟩,
    finset.mem_univ _, (ne_of_eq_of_ne nat.cast_one one_ne_zero), rfl⟩,
end

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
lemma nonempty_fixed_point_of_prime_not_dvd_card (hpα : ¬ p ∣ card α) :
  (fixed_points G α).nonempty :=
@set.nonempty_of_nonempty_subtype _ _ begin
rw [←card_pos_iff, pos_iff_ne_zero],
  contrapose! hpα,
  rw [←nat.modeq_zero_iff_dvd, ←hpα],
  exact hG.card_modeq_card_fixed_points α,
end

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
lemma exists_fixed_point_of_prime_dvd_card_of_fixed_point
  (hpα : p ∣ card α) {a : α} (ha : a ∈ fixed_points G α) :
  ∃ b, b ∈ fixed_points G α ∧ a ≠ b :=
have hpf : p ∣ card (fixed_points G α) :=
  nat.modeq_zero_iff_dvd.mp ((hG.card_modeq_card_fixed_points α).symm.trans hpα.modeq_zero_nat),
have hα : 1 < card (fixed_points G α) :=
  (fact.out p.prime).one_lt.trans_le (nat.le_of_dvd (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf),
let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
⟨b, hb, λ hab, hba (by simp_rw [hab])⟩

lemma center_nontrivial [nontrivial G] [fintype G] : nontrivial (subgroup.center G) :=
begin
  classical,
  have := (hG.of_equiv conj_act.to_conj_act).exists_fixed_point_of_prime_dvd_card_of_fixed_point G,
  rw conj_act.fixed_points_eq_center at this,
  obtain ⟨g, hg⟩ := this _ (subgroup.center G).one_mem,
  { exact ⟨⟨1, ⟨g, hg.1⟩, mt subtype.ext_iff.mp hg.2⟩⟩ },
  { obtain ⟨n, hn⟩ := is_p_group.iff_card.mp hG,
    rw hn,
    apply dvd_pow_self,
    rintro rfl,
    exact (fintype.one_lt_card).ne' hn },
end

lemma bot_lt_center [nontrivial G] [fintype G] : ⊥ < subgroup.center G :=
begin
  haveI := center_nontrivial hG,
  classical,
  exact bot_lt_iff_ne_bot.mpr ((subgroup.center G).one_lt_card_iff_ne_bot.mp fintype.one_lt_card),
end

end G_is_p_group

lemma to_le {H K : subgroup G} (hK : is_p_group p K) (hHK : H ≤ K) : is_p_group p H :=
hK.of_injective (subgroup.inclusion hHK) (λ a b h, subtype.ext (show _, from subtype.ext_iff.mp h))

lemma to_inf_left {H K : subgroup G} (hH : is_p_group p H) : is_p_group p (H ⊓ K : subgroup G) :=
hH.to_le inf_le_left

lemma to_inf_right {H K : subgroup G} (hK : is_p_group p K) : is_p_group p (H ⊓ K : subgroup G) :=
hK.to_le inf_le_right

lemma map {H : subgroup G} (hH : is_p_group p H) {K : Type*} [group K]
  (ϕ : G →* K) : is_p_group p (H.map ϕ) :=
begin
  rw [←H.subtype_range, monoid_hom.map_range],
  exact hH.of_surjective (ϕ.restrict H).range_restrict (ϕ.restrict H).range_restrict_surjective,
end

lemma comap_of_ker_is_p_group {H : subgroup G} (hH : is_p_group p H) {K : Type*} [group K]
  (ϕ : K →* G) (hϕ : is_p_group p ϕ.ker) : is_p_group p (H.comap ϕ) :=
begin
  intro g,
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩,
  rw [subtype.ext_iff, H.coe_pow, subtype.coe_mk, ←ϕ.map_pow] at hj,
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩,
  rwa [subtype.ext_iff, ϕ.ker.coe_pow, subtype.coe_mk, ←pow_mul, ←pow_add] at hk,
  exact ⟨j + k, by rwa [subtype.ext_iff, (H.comap ϕ).coe_pow]⟩,
end

lemma comap_of_injective {H : subgroup G} (hH : is_p_group p H) {K : Type*} [group K]
  (ϕ : K →* G) (hϕ : function.injective ϕ) : is_p_group p (H.comap ϕ) :=
begin
  apply hH.comap_of_ker_is_p_group ϕ,
  rw ϕ.ker_eq_bot_iff.mpr hϕ,
  exact is_p_group.of_bot,
end

lemma to_sup_of_normal_right {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  [K.normal] : is_p_group p (H ⊔ K : subgroup G) :=
begin
  rw [←quotient_group.ker_mk K, ←subgroup.comap_map_eq],
  apply (hH.map (quotient_group.mk' K)).comap_of_ker_is_p_group,
  rwa quotient_group.ker_mk,
end

lemma to_sup_of_normal_left {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  [H.normal] : is_p_group p (H ⊔ K : subgroup G) :=
(congr_arg (λ H : subgroup G, is_p_group p H) sup_comm).mp (to_sup_of_normal_right hK hH)

lemma to_sup_of_normal_right' {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  (hHK : H ≤ K.normalizer) : is_p_group p (H ⊔ K : subgroup G) :=
let hHK' := to_sup_of_normal_right (hH.of_equiv (subgroup.comap_subtype_equiv_of_le hHK).symm)
  (hK.of_equiv (subgroup.comap_subtype_equiv_of_le subgroup.le_normalizer).symm) in
((congr_arg (λ H : subgroup K.normalizer, is_p_group p H)
  (subgroup.sup_subgroup_of_eq hHK subgroup.le_normalizer)).mp hHK').of_equiv
  (subgroup.comap_subtype_equiv_of_le (sup_le hHK subgroup.le_normalizer))

lemma to_sup_of_normal_left' {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  (hHK : K ≤ H.normalizer) : is_p_group p (H ⊔ K : subgroup G) :=
(congr_arg (λ H : subgroup G, is_p_group p H) sup_comm).mp (to_sup_of_normal_right' hK hH hHK)

end is_p_group
