/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.basic
import data.fintype.card
import data.zmod.basic
import group_theory.group_action.conj
import group_theory.specific_groups.cyclic
import group_theory.quotient_group
/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

namespace p_group

open fintype equiv finset subgroup mul_action
open_locale big_operators classical

variables {G : Type*} (α : Type*) [group G] [fintype G] {p n : ℕ}
  [fact p.prime] (hG : card G = p ^ n)

include hG

section mul_action
variables [mul_action G α] [fintype α] [fintype (fixed_points G α)]

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
lemma card_modeq_card_fixed_points : card α ≡ card (fixed_points G α) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
  card_congr (sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
... = ∑ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a} : card_sigma _
... ≡ ∑ a : fixed_points G α, 1 [MOD p] :
begin
  rw [←zmod.eq_iff_modeq_nat p, nat.cast_sum, nat.cast_sum],
  refine eq.symm (sum_bij_ne_zero (λ a _ _, quotient.mk' a.1)
    (λ _ _ _, mem_univ _)
    (λ a₁ a₂ _ _ _ _ h,
      subtype.eq ((mem_fixed_points' α).1 a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, _)
      (λ a ha _, by rw [← mem_fixed_points_iff_card_orbit_eq_one.1 a.2];
        simp only [quotient.eq']; congr)),
  { refine quotient.induction_on' b (λ b _ hb, _),
    have : card (orbit G b) ∣ p ^ n,
    { rw [← hG, fintype.card_congr (orbit_equiv_quotient_stabilizer G b)],
      exact card_quotient_dvd_card _ },
    rcases (nat.dvd_prime_pow (fact.out p.prime)).1 this with ⟨k, _, hk⟩,
    have hb' :¬ p ^ 1 ∣ p ^ k,
    { rw [pow_one, ← hk, ← nat.modeq_zero_iff_dvd, ← zmod.eq_iff_modeq_nat,
        nat.cast_zero, ← ne.def],
      exact eq.mpr (by simp only [quotient.eq']; congr) hb },
    have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p) hb'))),
    refine ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, pow_zero]⟩,
      mem_univ _, _, rfl⟩,
    rw [nat.cast_one], exact one_ne_zero }
end
... = _ : by simp; refl

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
lemma nonempty_fixed_point_of_prime_not_dvd_card
  (hp : ¬ p ∣ fintype.card α) :
  (fixed_points G α).nonempty :=
@set.nonempty_of_nonempty_subtype _ _ begin
  rw [← fintype.card_pos_iff, pos_iff_ne_zero],
  assume h,
  have := card_modeq_card_fixed_points α hG,
  rw [h, nat.modeq_zero_iff_dvd] at this,
  contradiction
end

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
lemma exists_fixed_point_of_prime_dvd_card_of_fixed_point
  (hpα : p ∣ fintype.card α) {a : α} (ha : a ∈ fixed_points G α) :
  ∃ b, b ∈ fixed_points G α ∧ a ≠ b :=
have hpf : p ∣ fintype.card (fixed_points G α),
  from nat.modeq_zero_iff_dvd.1 ((card_modeq_card_fixed_points α hG).symm.trans hpα.modeq_zero_nat),
have hα : 1 < fintype.card (fixed_points G α),
  from (fact.out p.prime).one_lt.trans_le (nat.le_of_dvd (fintype.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf),
let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
⟨b, hb, λ hab, hba $ by simp [hab]⟩

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
