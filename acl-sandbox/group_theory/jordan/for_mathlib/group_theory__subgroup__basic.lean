/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.subgroup.basic
import data.fintype.perm

lemma monoid_hom.range_is_commutative {G H : Type*} [group G] [group H] (f : G →* H) (hG : is_commutative G (*)) :
 f.range.is_commutative :=
begin
  apply subgroup.is_commutative.mk,
  apply is_commutative.mk,
  rintro ⟨_, a, rfl⟩,  rintro ⟨_, b, rfl⟩,
  rw ← subtype.coe_inj,
  change (f a) * (f b) = (f b) * (f a),
  simp only [← map_mul],
  rw hG.comm,
end

lemma equiv.perm_is_nontrivial {α: Type*} [decidable_eq α] [fintype α] :
  1 < fintype.card α ↔  nontrivial (equiv.perm α)  :=
by rw [← fintype.one_lt_card_iff_nontrivial, fintype.card_perm, nat.one_lt_factorial]

lemma monoid.is_commutative_of_order_le_2 {G : Type*} [decidable_eq G] [fintype G] [monoid G]
  (hG : fintype.card G ≤ 2) : is_commutative G (*) :=
begin
  suffices : ∀(a b : G) (ha : a ≠ 1) (hb : b ≠ 1), a = b,
  apply is_commutative.mk,
  intros a b,
  cases dec_em (a = 1) with ha ha,
  { rw ha, simp only [one_mul, mul_one], },
  cases dec_em (b = 1) with hb hb,
  { rw hb, simp only [one_mul, mul_one], },
  rw this a b ha hb,

  by_contradiction, apply not_lt.mpr hG,
  push_neg at h,
  obtain ⟨a, b, hab1⟩ := h,
  rw fintype.two_lt_card_iff,
  use a, use b, use 1,
  simp only [hab1, ne.def, not_false_iff, and_self],
end

/-
lemma group.is_commutative_of_order_le_2' {G: Type*} [decidable_eq G] [fintype G] [group G] (hG : fintype.card G ≤ 2) :
  is_commutative G (*) := monoid.is_commutative_of_order_le_2 hG

lemma group.is_commutative_of_order_le_2 {G: Type*} [fintype G] [group G] (hG : fintype.card G ≤ 2) :
  is_commutative G (*) :=
begin
  apply is_commutative.mk,
  suffices : ∀ (a : G), a = a⁻¹,
  { intros a b,
    rw this (a*b),
    simp only [mul_inv_rev],
    rw ← this a, rw ← this b, },

  intro a,
  by_contradiction,
  apply not_lt.mpr hG,
  rw fintype.two_lt_card_iff,
  use a, use a⁻¹, use 1,
  split, exact h,
  suffices : a ≠ 1,
  split,
  exact this,
  simp only [ne.def, inv_eq_one], exact this,

  intro h1, apply h,
  rw h1, simp only [inv_one],
end
-/

lemma equiv.perm.is_commutative_iff {α: Type*} [decidable_eq α] [fintype α] :
  fintype.card α ≤ 2 ↔ is_commutative (equiv.perm α) (*) :=
begin
  cases nat.lt_or_ge (fintype.card α) 3 with hα hα,
  { rw nat.lt_succ_iff at hα,
    simp only [hα, true_iff],
    apply monoid.is_commutative_of_order_le_2,
    have : nat.factorial 2 = 2, by norm_num,
    rw [← this, fintype.card_perm],
    exact nat.factorial_le hα, },
  { rw nat.succ_le_iff at hα,
    rw ← not_lt,
    simp only [hα, not_true, false_iff],
    intro h,
    rw fintype.two_lt_card_iff at hα,
    obtain ⟨a, b, c, hab, hac, hbc⟩ := hα,
    have : equiv.swap a c * equiv.swap a b = equiv.swap a b * equiv.swap a c,
    apply h.comm,

    rw equiv.ext_iff at this,
    /- specialize this b,
    simp only [equiv.perm.coe_mul, function.comp_app, equiv.swap_apply_left, equiv.swap_apply_right] at this,
    rw equiv.swap_apply_of_ne_of_ne hab.symm hbc at this,
    simp only [equiv.swap_apply_right] at this,
    exact hac this.symm,  -/
    /- specialize this c,
    simp only [equiv.perm.coe_mul, function.comp_app, equiv.swap_apply_left, equiv.swap_apply_right] at this,
    rw equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm at this,
    simp only [equiv.swap_apply_right] at this,
    exact hab this, -/

    specialize this a,
    simp only [equiv.perm.coe_mul, function.comp_app, equiv.swap_apply_left, equiv.swap_apply_right] at this,
    rw equiv.swap_apply_of_ne_of_ne hab.symm hbc at this,
    rw equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm at this,
    exact hbc this, },
end
