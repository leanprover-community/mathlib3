/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import algebra.group.conj
import group_theory.abelianization
import group_theory.group_action.conj_act
import group_theory.index

/-!
# Commuting Probability
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

variables (M : Type*) [fintype M] [has_mul M]

/-- The commuting probability of a finite type with a multiplication operation -/
def comm_prob : ℚ := card {p : M × M // p.1 * p.2 = p.2 * p.1} / card M ^ 2

lemma comm_prob_def : comm_prob M = card {p : M × M // p.1 * p.2 = p.2 * p.1} / card M ^ 2 :=
rfl

lemma comm_prob_pos [h : nonempty M] : 0 < comm_prob M :=
h.elim (λ x, div_pos (nat.cast_pos.mpr (card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
  (pow_pos (nat.cast_pos.mpr card_pos) 2))

lemma comm_prob_le_one : comm_prob M ≤ 1 :=
begin
  refine div_le_one_of_le _ (sq_nonneg (card M)),
  rw [←nat.cast_pow, nat.cast_le, sq, ←card_prod],
  apply set_fintype_card_le_univ,
end

variables {M}

lemma comm_prob_eq_one_iff [h : nonempty M] : comm_prob M = 1 ↔ commutative ((*) : M → M → M) :=
begin
  change (card {p : M × M | p.1 * p.2 = p.2 * p.1} : ℚ) / _ = 1 ↔ _,
  rw [div_eq_one_iff_eq, ←nat.cast_pow, nat.cast_inj, sq, ←card_prod,
      set_fintype_card_eq_univ_iff, set.eq_univ_iff_forall],
  { exact ⟨λ h x y, h (x, y), λ h x, h x.1 x.2⟩ },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
end

variables (G : Type*) [group G] [fintype G]

lemma card_comm_eq_card_conj_classes_mul_card :
  card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (conj_classes G) * card G :=
calc card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (Σ g, {h // g * h = h * g}) :
  card_congr (equiv.subtype_prod_equiv_sigma_subtype (λ g h : G, g * h = h * g))
... = ∑ g, card {h // g * h = h * g} : card_sigma _
... = ∑ g, card (mul_action.fixed_by (conj_act G) G g) : sum_equiv conj_act.to_conj_act.to_equiv
  _ _ (λ g, by { congr, exact set.ext (λ h, mul_inv_eq_iff_eq_mul.symm) })
... = card (quotient (mul_action.orbit_rel (conj_act G) G)) * card G :
  mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group (conj_act G) G
... = card (quotient (is_conj.setoid G)) * card G : by congr;
  exact setoid.ext (λ g h, (setoid.comm' _).trans is_conj_iff.symm)

lemma comm_prob_def' : comm_prob G = card (conj_classes G) / card G :=
begin
  rw [comm_prob, card_comm_eq_card_conj_classes_mul_card, nat.cast_mul, sq],
  exact mul_div_mul_right (card (conj_classes G)) (card G) (nat.cast_ne_zero.mpr card_ne_zero),
end

variables {G} (H : subgroup G)

section conj_classes

lemma conj_classes.map_surjective {α β : Type*} [monoid α] [monoid β] (f : α →* β)
  (hf : function.surjective f) : function.surjective (conj_classes.map f) :=
begin
  intros b,
  obtain ⟨b, rfl⟩ := conj_classes.mk_surjective b,
  obtain ⟨a, rfl⟩ := hf b,
  exact ⟨conj_classes.mk a, rfl⟩,
end

lemma conj_classes.map_quotient_surjective {G : Type*} [group G] (H : subgroup G) [H.normal] :
  function.surjective (conj_classes.map (quotient_group.mk' H)) :=
conj_classes.map_surjective (quotient_group.mk' H) quotient.surjective_quotient_mk'

end conj_classes

lemma subgroup.comm_prob_subgroup_le : comm_prob H ≤ comm_prob G * H.index ^ 2 :=
begin
  rw [comm_prob, comm_prob, div_le_iff, mul_assoc, ←mul_pow, ←nat.cast_mul, H.index_mul_card,
      div_mul_cancel, nat.cast_le],
  { let f : {p : H × H // p.1 * p.2 = p.2 * p.1} → {p : G × G // p.1 * p.2 = p.2 * p.1} :=
    λ p, ⟨⟨p.1.1, p.1.2⟩, subtype.ext_iff.mp p.2⟩,
    convert card_le_of_injective f (λ p q h, _),
    simp only [subtype.ext_iff, prod.ext_iff] at h ⊢,
    exact h },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
  { exact pow_pos (nat.cast_pos.mpr card_pos) 2 },
end

lemma subgroup.comm_prob_quotient_le [H.normal] : comm_prob (G ⧸ H) ≤ comm_prob G * card H :=
begin
  rw [comm_prob_def', comm_prob_def', div_le_iff, mul_assoc, ←nat.cast_mul, mul_comm (card H),
      ←subgroup.card_eq_card_quotient_mul_card_subgroup, div_mul_cancel, nat.cast_le],
  { exact card_le_of_surjective _ (conj_classes.map_quotient_surjective H) },
  { exact nat.cast_ne_zero.mpr card_ne_zero },
  { exact nat.cast_pos.mpr card_pos },
end

variables (G)

lemma subgroup.bound5 : (↑(card (commutator G)))⁻¹ ≤ comm_prob G :=
begin
  have key1 := (commutator G).comm_prob_quotient_le,
  have key2 : comm_prob (abelianization G) = 1 := comm_prob_eq_one_iff.mpr begin
    intros x y,
    exact mul_comm x y,
  end,
  sorry
end
