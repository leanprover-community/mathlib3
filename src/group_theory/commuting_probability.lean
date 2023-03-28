/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import algebra.group.conj_finite
import group_theory.abelianization
import group_theory.group_action.conj_act
import group_theory.group_action.quotient
import group_theory.index

/-!
# Commuting Probability

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file introduces the commuting probability of finite groups.

## Main definitions
* `comm_prob`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/

noncomputable theory
open_locale classical
open_locale big_operators

open fintype

variables (M : Type*) [has_mul M]

/-- The commuting probability of a finite type with a multiplication operation -/
def comm_prob : ℚ := nat.card {p : M × M // p.1 * p.2 = p.2 * p.1} / nat.card M ^ 2

lemma comm_prob_def :
  comm_prob M = nat.card {p : M × M // p.1 * p.2 = p.2 * p.1} / nat.card M ^ 2 :=
rfl

variables [finite M]

lemma comm_prob_pos [h : nonempty M] : 0 < comm_prob M :=
h.elim (λ x, div_pos (nat.cast_pos.mpr (finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
  (pow_pos (nat.cast_pos.mpr finite.card_pos) 2))

lemma comm_prob_le_one : comm_prob M ≤ 1 :=
begin
  refine div_le_one_of_le _ (sq_nonneg (nat.card M)),
  rw [←nat.cast_pow, nat.cast_le, sq, ←nat.card_prod],
  apply finite.card_subtype_le,
end

variables {M}

lemma comm_prob_eq_one_iff [h : nonempty M] : comm_prob M = 1 ↔ commutative ((*) : M → M → M) :=
begin
  haveI := fintype.of_finite M,
  rw [comm_prob, ←set.coe_set_of, nat.card_eq_fintype_card, nat.card_eq_fintype_card],
  rw [div_eq_one_iff_eq, ←nat.cast_pow, nat.cast_inj, sq, ←card_prod,
      set_fintype_card_eq_univ_iff, set.eq_univ_iff_forall],
  { exact ⟨λ h x y, h (x, y), λ h x, h x.1 x.2⟩ },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
end

variables (G : Type*) [group G] [finite G]

lemma card_comm_eq_card_conj_classes_mul_card :
  nat.card {p : G × G // p.1 * p.2 = p.2 * p.1} = nat.card (conj_classes G) * nat.card G :=
begin
  haveI := fintype.of_finite G,
  simp only [nat.card_eq_fintype_card],
  convert calc card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (Σ g, {h // g * h = h * g}) :
  card_congr (equiv.subtype_prod_equiv_sigma_subtype (λ g h : G, g * h = h * g))
... = ∑ g, card {h // g * h = h * g} : card_sigma _
... = ∑ g, card (mul_action.fixed_by (conj_act G) G g) : sum_equiv conj_act.to_conj_act.to_equiv
  _ _ (λ g, card_congr' $ congr_arg _ $ funext $ λ h, mul_inv_eq_iff_eq_mul.symm.to_eq)
... = card (quotient (mul_action.orbit_rel (conj_act G) G)) * card G :
  mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group (conj_act G) G
... = card (quotient (is_conj.setoid G)) * card G :
  have this : mul_action.orbit_rel (conj_act G) G = is_conj.setoid G :=
    setoid.ext (λ g h, (setoid.comm' _).trans is_conj_iff.symm),
  by cc
end

lemma comm_prob_def' : comm_prob G = nat.card (conj_classes G) / nat.card G :=
begin
  rw [comm_prob, card_comm_eq_card_conj_classes_mul_card, nat.cast_mul, sq],
  exact mul_div_mul_right _ _ (nat.cast_ne_zero.mpr finite.card_pos.ne'),
end

variables {G} (H : subgroup G)

lemma subgroup.comm_prob_subgroup_le : comm_prob H ≤ comm_prob G * H.index ^ 2 :=
begin
  /- After rewriting with `comm_prob_def`, we reduce to showing that `G` has at least as many
    commuting pairs as `H`. -/
  rw [comm_prob_def, comm_prob_def,  div_le_iff, mul_assoc, ←mul_pow, ←nat.cast_mul,
      mul_comm H.index, H.card_mul_index, div_mul_cancel, nat.cast_le],
  { refine finite.card_le_of_injective (λ p, ⟨⟨p.1.1, p.1.2⟩, subtype.ext_iff.mp p.2⟩) _,
    exact λ p q h, by simpa only [subtype.ext_iff, prod.ext_iff] using h },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr finite.card_pos.ne') },
  { exact pow_pos (nat.cast_pos.mpr finite.card_pos) 2 },
end

lemma subgroup.comm_prob_quotient_le [H.normal] : comm_prob (G ⧸ H) ≤ comm_prob G * nat.card H :=
begin
  /- After rewriting with `comm_prob_def'`, we reduce to showing that `G` has at least as many
    conjugacy classes as `G ⧸ H`. -/
  rw [comm_prob_def', comm_prob_def', div_le_iff, mul_assoc, ←nat.cast_mul, ←subgroup.index,
      H.card_mul_index, div_mul_cancel, nat.cast_le],
  { apply finite.card_le_of_surjective,
    show function.surjective (conj_classes.map (quotient_group.mk' H)),
    exact (conj_classes.map_surjective quotient.surjective_quotient_mk') },
  { exact nat.cast_ne_zero.mpr finite.card_pos.ne' },
  { exact nat.cast_pos.mpr finite.card_pos },
end

variables (G)

lemma inv_card_commutator_le_comm_prob : (↑(nat.card (commutator G)))⁻¹ ≤ comm_prob G :=
(inv_pos_le_iff_one_le_mul (by exact nat.cast_pos.mpr finite.card_pos)).mpr
  (le_trans (ge_of_eq (comm_prob_eq_one_iff.mpr (abelianization.comm_group G).mul_comm))
    (commutator G).comm_prob_quotient_le)
