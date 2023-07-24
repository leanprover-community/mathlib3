/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/

import data.zmod.basic
import group_theory.index
import group_theory.group_action.conj_act
import group_theory.group_action.quotient
import group_theory.perm.cycle.type
import group_theory.specific_groups.cyclic
import tactic.interval_cases

/-!
# p-groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  have hG : card G ≠ 0 := card_ne_zero,
  refine ⟨λ h, _, λ ⟨n, hn⟩, of_card hn⟩,
  suffices : ∀ q ∈ nat.factors (card G), q = p,
  { use (card G).factors.length,
    rw [←list.prod_replicate, ←list.eq_replicate_of_mem this, nat.prod_factors hG] },
  intros q hq,
  obtain ⟨hq1, hq2⟩ := (nat.mem_factors hG).mp hq,
  haveI : fact q.prime := ⟨hq1⟩,
  obtain ⟨g, hg⟩ := exists_prime_order_of_dvd_card q hq2,
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
  is_p_group p (G ⧸ H) :=
hG.of_surjective (quotient_group.mk' H) quotient.surjective_quotient_mk'

lemma of_equiv {H : Type*} [group H] (ϕ : G ≃* H) : is_p_group p H :=
hG.of_surjective ϕ.to_monoid_hom ϕ.surjective

lemma order_of_coprime {n : ℕ} (hn : p.coprime n) (g : G) : (order_of g).coprime n :=
let ⟨k, hk⟩ := hG g in (hn.pow_left k).coprime_dvd_left (order_of_dvd_of_pow_eq_one hk)

/-- If `gcd(p,n) = 1`, then the `n`th power map is a bijection. -/
noncomputable def pow_equiv {n : ℕ} (hn : p.coprime n) : G ≃ G :=
let h : ∀ g : G, (nat.card (subgroup.zpowers g)).coprime n :=
  λ g, order_eq_card_zpowers' g ▸ hG.order_of_coprime hn g in
{ to_fun := (^ n),
  inv_fun := λ g, (pow_coprime (h g)).symm ⟨g, subgroup.mem_zpowers g⟩,
  left_inv := λ g, subtype.ext_iff.1 $ (pow_coprime (h (g ^ n))).left_inv
    ⟨g, _, subtype.ext_iff.1 $ (pow_coprime (h g)).left_inv ⟨g, subgroup.mem_zpowers g⟩⟩,
  right_inv := λ g, subtype.ext_iff.1 $ (pow_coprime (h g)).right_inv ⟨g, subgroup.mem_zpowers g⟩ }

@[simp] lemma pow_equiv_apply {n : ℕ} (hn : p.coprime n) (g : G) : hG.pow_equiv hn g = g ^ n :=
rfl

@[simp] lemma pow_equiv_symm_apply {n : ℕ} (hn : p.coprime n) (g : G) :
  (hG.pow_equiv hn).symm g = g ^ (order_of g).gcd_b n :=
by rw order_eq_card_zpowers'; refl

variables [hp : fact p.prime]

include hp

/-- If `p ∤ n`, then the `n`th power map is a bijection. -/
@[reducible] noncomputable def pow_equiv' {n : ℕ} (hn : ¬ p ∣ n) : G ≃ G :=
pow_equiv hG (hp.out.coprime_iff_not_dvd.mpr hn)

lemma index (H : subgroup G) [H.finite_index] : ∃ n : ℕ, H.index = p ^ n :=
begin
  haveI := H.normal_core.fintype_quotient_of_finite_index,
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normal_core),
  obtain ⟨k, hk1, hk2⟩ := (nat.dvd_prime_pow hp.out).mp ((congr_arg _
    (H.normal_core.index_eq_card.trans hn)).mp (subgroup.index_dvd_of_le H.normal_core_le)),
  exact ⟨k, hk2⟩,
end

lemma card_eq_or_dvd : nat.card G = 1 ∨ p ∣ nat.card G :=
begin
  casesI fintype_or_infinite G,
  { obtain ⟨n, hn⟩ := iff_card.mp hG,
    rw [nat.card_eq_fintype_card, hn],
    cases n,
    { exact or.inl rfl },
    { exact or.inr ⟨p ^ n, rfl⟩ } },
  { rw nat.card_eq_zero_of_infinite,
    exact or.inr ⟨0, rfl⟩ },
end

lemma nontrivial_iff_card [fintype G] : nontrivial G ↔ ∃ n > 0, card G = p ^ n :=
⟨λ hGnt, let ⟨k, hk⟩ := iff_card.1 hG in ⟨k, nat.pos_of_ne_zero $ λ hk0,
  by rw [hk0, pow_zero] at hk; exactI fintype.one_lt_card.ne' hk, hk⟩,
λ ⟨k, hk0, hk⟩, one_lt_card_iff_nontrivial.1 $ hk.symm ▸
  one_lt_pow (fact.out p.prime).one_lt (ne_of_gt hk0)⟩

variables {α : Type*} [mul_action G α]

lemma card_orbit (a : α) [fintype (orbit G a)] :
  ∃ n : ℕ, card (orbit G a) = p ^ n :=
begin
  let ϕ := orbit_equiv_quotient_stabilizer G a,
  haveI := fintype.of_equiv (orbit G a) ϕ,
  haveI := (stabilizer G a).finite_index_of_finite_quotient,
  rw [card_congr ϕ, ←subgroup.index_eq_card],
  exact hG.index (stabilizer G a),
end

variables (α) [fintype α]

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
lemma card_modeq_card_fixed_points [fintype (fixed_points G α)] :
  card α ≡ card (fixed_points G α) [MOD p] :=
begin
  classical,
  calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
    card_congr (equiv.sigma_fiber_equiv (@quotient.mk' _ (orbit_rel G α))).symm
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
  have : k = 0 := le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p)
    (by rwa [pow_one, ←hk, ←nat.modeq_zero_iff_dvd, ←zmod.eq_iff_modeq_nat, ←key,
      nat.cast_zero])))),
  exact ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, pow_zero]⟩,
    finset.mem_univ _, (ne_of_eq_of_ne nat.cast_one one_ne_zero), rfl⟩,
end

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
lemma nonempty_fixed_point_of_prime_not_dvd_card (hpα : ¬ p ∣ card α)
  [finite (fixed_points G α)] :
  (fixed_points G α).nonempty :=
@set.nonempty_of_nonempty_subtype _ _ begin
  casesI nonempty_fintype (fixed_points G α),
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
begin
  casesI nonempty_fintype (fixed_points G α),
  have hpf : p ∣ card (fixed_points G α) :=
    nat.modeq_zero_iff_dvd.mp ((hG.card_modeq_card_fixed_points α).symm.trans hpα.modeq_zero_nat),
  have hα : 1 < card (fixed_points G α) :=
    (fact.out p.prime).one_lt.trans_le (nat.le_of_dvd (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf),
  exact let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
  ⟨b, hb, λ hab, hba (by simp_rw [hab])⟩
end

lemma center_nontrivial [nontrivial G] [finite G] : nontrivial (subgroup.center G) :=
begin
  classical,
  casesI nonempty_fintype G,
  have := (hG.of_equiv conj_act.to_conj_act).exists_fixed_point_of_prime_dvd_card_of_fixed_point G,
  rw conj_act.fixed_points_eq_center at this,
  obtain ⟨g, hg⟩ := this _ (subgroup.center G).one_mem,
  { exact ⟨⟨1, ⟨g, hg.1⟩, mt subtype.ext_iff.mp hg.2⟩⟩ },
  { obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp infer_instance,
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0) },
end

lemma bot_lt_center [nontrivial G] [finite G] : ⊥ < subgroup.center G :=
begin
  haveI := center_nontrivial hG,
  casesI nonempty_fintype G,
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

lemma ker_is_p_group_of_injective {K : Type*} [group K] {ϕ : K →* G} (hϕ : function.injective ϕ) :
  is_p_group p ϕ.ker :=
(congr_arg (λ Q : subgroup K, is_p_group p Q) (ϕ.ker_eq_bot_iff.mpr hϕ)).mpr is_p_group.of_bot

lemma comap_of_injective {H : subgroup G} (hH : is_p_group p H) {K : Type*} [group K]
  (ϕ : K →* G) (hϕ : function.injective ϕ) : is_p_group p (H.comap ϕ) :=
hH.comap_of_ker_is_p_group ϕ (ker_is_p_group_of_injective hϕ)

lemma comap_subtype {H : subgroup G} (hH : is_p_group p H) {K : subgroup G} :
  is_p_group p (H.comap K.subtype) :=
hH.comap_of_injective K.subtype subtype.coe_injective

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
let hHK' := to_sup_of_normal_right (hH.of_equiv (subgroup.subgroup_of_equiv_of_le hHK).symm)
  (hK.of_equiv (subgroup.subgroup_of_equiv_of_le subgroup.le_normalizer).symm) in
((congr_arg (λ H : subgroup K.normalizer, is_p_group p H)
  (subgroup.sup_subgroup_of_eq hHK subgroup.le_normalizer)).mp hHK').of_equiv
  (subgroup.subgroup_of_equiv_of_le (sup_le hHK subgroup.le_normalizer))

lemma to_sup_of_normal_left' {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  (hHK : K ≤ H.normalizer) : is_p_group p (H ⊔ K : subgroup G) :=
(congr_arg (λ H : subgroup G, is_p_group p H) sup_comm).mp (to_sup_of_normal_right' hK hH hHK)

/-- finite p-groups with different p have coprime orders -/
lemma coprime_card_of_ne {G₂ : Type*} [group G₂]
  (p₁ p₂ : ℕ) [hp₁ : fact p₁.prime] [hp₂ : fact p₂.prime] (hne : p₁ ≠ p₂)
  (H₁ : subgroup G) (H₂ : subgroup G₂) [fintype H₁] [fintype H₂]
  (hH₁ : is_p_group p₁ H₁) (hH₂ : is_p_group p₂ H₂) :
  nat.coprime (fintype.card H₁) (fintype.card H₂) :=
begin
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁, rw heq₁, clear heq₁,
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂, rw heq₂, clear heq₂,
  exact nat.coprime_pow_primes _ _ (hp₁.elim) (hp₂.elim) hne,
end

/-- p-groups with different p are disjoint -/
lemma disjoint_of_ne (p₁ p₂ : ℕ) [hp₁ : fact p₁.prime] [hp₂ : fact p₂.prime] (hne : p₁ ≠ p₂)
  (H₁ H₂ : subgroup G) (hH₁ : is_p_group p₁ H₁) (hH₂ : is_p_group p₂ H₂) :
  disjoint H₁ H₂ :=
begin
  rw subgroup.disjoint_def,
  intros x hx₁ hx₂,
  obtain ⟨n₁, hn₁⟩ := iff_order_of.mp hH₁ ⟨x, hx₁⟩,
  obtain ⟨n₂, hn₂⟩ := iff_order_of.mp hH₂ ⟨x, hx₂⟩,
  rw [← order_of_subgroup, subgroup.coe_mk] at hn₁ hn₂,
  have : p₁ ^ n₁ = p₂ ^ n₂, by rw [← hn₁, ← hn₂],
  rcases n₁.eq_zero_or_pos with rfl|hn₁,
  { simpa using hn₁ },
  { exact absurd (eq_of_prime_pow_eq hp₁.out.prime hp₂.out.prime hn₁ this) hne }
end

section p2comm

variables [fintype G] [fact p.prime] {n : ℕ} (hGpn : card G = p ^ n)
include hGpn
open subgroup

/-- The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive. -/
lemma card_center_eq_prime_pow (hn : 0 < n) [fintype (center G)] :
  ∃ k > 0, card (center G) = p ^ k :=
begin
  have hcG := to_subgroup (of_card hGpn) (center G),
  rcases iff_card.1 hcG with ⟨k, hk⟩,
  haveI : nontrivial G := (nontrivial_iff_card $ of_card hGpn).2 ⟨n, hn, hGpn⟩,
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn)),
end

omit hGpn

/-- The quotient by the center of a group of cardinality `p ^ 2` is cyclic. -/
lemma cyclic_center_quotient_of_card_eq_prime_sq (hG : card G = p ^ 2) :
  is_cyclic (G ⧸ (center G)) :=
begin
  classical,
  rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩,
  rw [card_eq_card_quotient_mul_card_subgroup (center G), mul_comm, hk] at hG,
  have hk2 := (nat.pow_dvd_pow_iff_le_right (fact.out p.prime).one_lt).1 ⟨_, hG.symm⟩,
  interval_cases k,
  { rw [sq, pow_one, mul_right_inj' (fact.out p.prime).ne_zero] at hG,
    exact is_cyclic_of_prime_card hG },
  { exact @is_cyclic_of_subsingleton _ _ ⟨fintype.card_le_one_iff.1 (mul_right_injective₀
      (pow_ne_zero 2 (ne_zero.ne p)) (hG.trans (mul_one (p ^ 2)).symm)).le⟩ },
end

/-- A group of order `p ^ 2` is commutative. See also `is_p_group.commutative_of_card_eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a` -/
def comm_group_of_card_eq_prime_sq (hG : card G = p ^ 2) : comm_group G :=
@comm_group_of_cycle_center_quotient _ _ _ _ (cyclic_center_quotient_of_card_eq_prime_sq hG) _
  (quotient_group.ker_mk (center G)).le

/-- A group of order `p ^ 2` is commutative. See also `is_p_group.comm_group_of_card_eq_prime_sq`
for the `comm_group` instance. -/
lemma commutative_of_card_eq_prime_sq (hG : card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
(comm_group_of_card_eq_prime_sq hG).mul_comm

end p2comm

end is_p_group
