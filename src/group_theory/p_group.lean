/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/

import group_theory.index
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

lemma to_le {H K : subgroup G} (hK : is_p_group p K) (hHK : H ≤ K) : is_p_group p H :=
begin
  simp_rw [is_p_group, subtype.ext_iff, subgroup.coe_pow] at hK ⊢,
  exact λ h, hK ⟨h, hHK h.2⟩,
end

lemma to_inf_left {H : subgroup G} (hH : is_p_group p H) (K : subgroup G) :
  is_p_group p (H ⊓ K : subgroup G) :=
hH.to_le inf_le_left

lemma to_inf_right {K : subgroup G} (hK : is_p_group p K) (H : subgroup G) :
  is_p_group p (H ⊓ K : subgroup G) :=
hK.to_le inf_le_right

variables (hG : is_p_group p G)

include hG

lemma to_subgroup (H : subgroup G) : is_p_group p H :=
begin
  simp_rw [is_p_group, subtype.ext_iff, subgroup.coe_pow],
  exact λ h, hG h,
end

lemma to_quotient (H : subgroup G) [H.normal] :
  is_p_group p (quotient_group.quotient H) :=
begin
  refine quotient.ind' (forall_imp (λ g, _) hG),
  exact exists_imp_exists (λ k h, (quotient_group.coe_pow H g _).symm.trans (congr_arg coe h)),
end

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
  haveI := of_equiv (orbit G a) ϕ,
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

end mul_action

/-- `p`-groups have non-trivial `center` -/
lemma exists_ne_one_mem_center (hn : 0 < n): ∃ g ≠ (1 : G), g ∈ center G :=
have ∃ g : G, g ∈ fixed_points (conj G) G ∧ 1 ≠ g :=
  exists_fixed_point_of_prime_dvd_card_of_fixed_point G
    (conj.card.trans hG)
    (hG.symm ▸ (dvd_pow (dvd_refl p) (pos_iff_ne_zero.1 hn)))
    (show (1 : G) ∈ fixed_points (conj G) G,
      by simp [conj.fixed_points_eq_center, subgroup.one_mem]),
by simpa [conj.fixed_points_eq_center, eq_comm, and.comm]

/-- The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive. -/
lemma card_center_eq_prime_pow (hn : 0 < n) : ∃ k > 0, card (center G) = p ^ k :=
have card (center G) ∣ p ^ n,
  from hG ▸ card_subgroup_dvd_card (center G),
begin
  rcases (nat.dvd_prime_pow (fact.out p.prime)).1 this with ⟨k, hkn, hk⟩,
  refine ⟨k, nat.pos_of_ne_zero (λ hk0, _), hk⟩,
  rw [hk0, pow_zero] at hk,
  rcases exists_ne_one_mem_center hG hn with ⟨g, hg1, hg⟩,
  have hg1' : (⟨g, hg⟩ : center G) ≠ 1, from λ h, hg1 (subtype.ext_iff.1 h),
  exact hg1' (fintype.card_le_one_iff.1 (le_of_eq hk) _ _)
end

omit hG

/-- The quotient by the center of a group of cardinality `p ^ 2` is cyclic. -/
def cyclic_center_quotient_of_card_eq_prime_sqr (hG : card G = p ^ 2) :
  is_cyclic (quotient_group.quotient (center G)) :=
begin
  rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩,
  have hk2 : k ≤ 2, from (nat.pow_dvd_pow_iff_le_right (fact.out p.prime).one_lt).1
    (hG ▸ hk ▸ card_subgroup_dvd_card (center G)),
  rw [card_eq_card_quotient_mul_card_subgroup (center G), hk] at hG,
  rcases k with  _ | _ | _ | k,
  { exact (lt_irrefl _ hk0).elim },
  { rw [pow_two, pow_one, nat.mul_left_inj (fact.out p.prime).pos] at hG,
    exact is_cyclic_of_prime_card hG },
  { conv_rhs at hG { rw ← one_mul (p ^ 2) },
    rw [nat.mul_left_inj (pow_pos (fact.out p.prime).pos _)] at hG,
    exact @is_cyclic_of_subsingleton _ _ ⟨fintype.card_le_one_iff.1 (le_of_eq hG)⟩ },
  { simpa [nat.succ_le_succ_iff] using hk2 }
end

/-- A group of order `p ^ 2` is commutative. See also `comm_group_of_card_eq_prime_sqr` for the
`comm_group` instance. -/
lemma commutative_of_card_eq_prime_sqr (hG : card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
by haveI : is_cyclic (quotient_group.quotient (center G)) :=
  cyclic_center_quotient_of_card_eq_prime_sqr hG;
exact commutative_of_cyclic_center_quotient (quotient_group.mk' (center G)) (by simp)

/-- A group of order `p ^ 2` is commutative. See also `commutative_of_card_eq_prime_sqr`
for just the proof that `∀ a b, a * b = b * a` -/
def comm_group_of_card_eq_prime_sqr (hG : card G = p ^ 2) : comm_group G :=
{ mul_comm := commutative_of_card_eq_prime_sqr hG,
  .. show group G, by apply_instance }

end p_group
