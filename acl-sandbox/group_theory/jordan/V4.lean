/- Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL
-/

import tactic
-- import logic.equiv.basic
-- import tactic.basic tactic.group
-- import group_theory.subgroup.basic
-- import group_theory.group_action.sub_mul_action
-- import group_theory.group_action.embedding
-- import group_theory.perm.cycle.type
-- import group_theory.perm.list
-- import group_theory.perm.cycle.concrete
-- import group_theory.group_action.quotient
import group_theory.specific_groups.alternating
-- import group_theory.abelianization
import group_theory.sylow

import .conj_class_count

namespace alternating_group

variables (α : Type*) [decidable_eq α] [fintype α]

def K4_carrier : finset (equiv.perm α) := finset.univ.filter (λ g, g.cycle_type = {} ∨ g.cycle_type = {2,2})

example (hα4: fintype.card α = 4) (g : equiv.perm α) (n : ℕ) (hg : order_of g = 2 ^ n) : g.cycle_type = {} ∨ g.cycle_type = {2} ∨ g.cycle_type = {2, 2} ∨ g.cycle_type = {4} :=
begin
  rw ← equiv.perm.lcm_cycle_type  at hg,

  have hg4 : g.cycle_type.sum ≤ 4,
  { rw ← hα4, rw equiv.perm.sum_cycle_type, apply finset.card_le_univ, },
  simp only [← or_assoc],
  by_cases h4 : 4 ∈ g.cycle_type,
  { apply or.intro_right,
    rw ← multiset.cons_erase h4,
    apply symm,
    rw multiset.singleton_eq_cons_iff,
    apply and.intro (rfl),
    rw ← multiset.cons_erase h4 at hg4,
    simp only [multiset.sum_cons, add_le_iff_nonpos_right, le_zero_iff, multiset.sum_eq_zero_iff] at hg4,
    ext x, simp only [multiset.count_zero, multiset.count_eq_zero],
    intro hx,
    apply not_le.mpr (equiv.perm.one_lt_of_mem_cycle_type (multiset.mem_of_mem_erase hx)),
    rw hg4 x hx, norm_num, },
  { -- 4 ∉ g.cycle_type,
    apply or.intro_left,
    suffices : ∃ n, g.cycle_type = multiset.repeat 2 n,
    { obtain ⟨k, hk⟩ := this,
      -- prove : k ← 2
      have hk2 : k ≤ 2,
      { rw hk at hg4, rw multiset.sum_repeat at hg4,
        apply nat.le_of_mul_le_mul_left, rw mul_comm 2 k, exact hg4,
        norm_num, },
      cases nat.eq_or_lt_of_le hk2 with hk2 hk1,
      apply or.intro_right, rw [hk, hk2], refl,
      apply or.intro_left,
      rw nat.lt_succ_iff at hk1,
      cases nat.eq_or_lt_of_le hk1 with hk1 hk0,
      apply or.intro_right, rw [hk, hk1], refl,
      simp only [nat.lt_one_iff] at hk0,
      apply or.intro_left, rw [hk, hk0], refl, },

    use g.cycle_type.card,
    rw multiset.eq_repeat',
    intros i hi,
    have := multiset.dvd_lcm hi, rw [hg, nat.dvd_prime_pow] at this,
    obtain ⟨k, ⟨hk, rfl⟩⟩ := this,
    suffices : k = 1,
    rw this, norm_num,
    apply le_antisymm,
    rw ← not_lt, intro hk1,
    suffices : k = 2,
    apply h4, rw this at hi, exact hi,
    refine le_antisymm _ hk1,
    { -- k ≤ 2
      rw ← nat.pow_le_iff_le_right (nat.le_refl 2),
      norm_num, rw ← hα4,
      apply le_trans (equiv.perm.le_card_support_of_mem_cycle_type hi),
      apply finset.card_le_univ, },
    rw nat.one_le_iff_ne_zero, intro hk0,
    rw hk0 at hi, norm_num at hi,
    apply nat.lt_irrefl 1, exact equiv.perm.one_lt_of_mem_cycle_type hi,
    norm_num, },
end

lemma mem_K4_of_order_two_pow (hα4: fintype.card α = 4)
  (g : equiv.perm α) (hg0 : g ∈ alternating_group α) (n : ℕ) (hg : order_of g ∣ 2 ^ n) : g ∈ K4_carrier α
:=
begin
  rw ← equiv.perm.lcm_cycle_type  at hg,
  rw [equiv.perm.mem_alternating_group, equiv.perm.sign_of_cycle_type] at hg0,

  have hg4 : g.cycle_type.sum ≤ 4,
  { rw ← hα4, rw equiv.perm.sum_cycle_type, apply finset.card_le_univ, },

  by_cases h4 : 4 ∈ g.cycle_type,
  { exfalso,
    suffices : g.cycle_type = {4},
    rw [this, ← units.eq_iff] at hg0, norm_num at hg0,
    rw ← multiset.cons_erase h4,
    apply symm,
    rw multiset.singleton_eq_cons_iff,
    apply and.intro (rfl),
    rw ← multiset.cons_erase h4 at hg4,
    simp only [multiset.sum_cons, add_le_iff_nonpos_right, le_zero_iff, multiset.sum_eq_zero_iff] at hg4,
    ext x, simp only [multiset.count_zero, multiset.count_eq_zero],
    intro hx,
    apply not_le.mpr (equiv.perm.one_lt_of_mem_cycle_type (multiset.mem_of_mem_erase hx)),
    rw hg4 x hx, norm_num, },
  { -- we know 4 ∉ g.cycle_type,
    suffices : g.cycle_type = multiset.repeat 2 (g.cycle_type.card),
    { rw this at hg0,
      simp only [pow_add, pow_mul, multiset.sum_repeat, algebra.id.smul_eq_mul, multiset.card_repeat, int.units_sq, one_mul] at hg0,
      -- prove : g.cycle_type.card ≤ 2
      have hk2 : g.cycle_type.card ≤ 2,
      { rw this at hg4, rw multiset.sum_repeat at hg4,
        apply nat.le_of_mul_le_mul_left, rw mul_comm 2 _, exact hg4,
        norm_num, },
      cases nat.eq_or_lt_of_le hk2 with hk2 hk1,
      -- g.cycle_type.card = 2
      rw hk2 at this, simp only [K4_carrier, finset.mem_filter, this],
      simp only [finset.mem_univ, multiset.repeat_succ, multiset.repeat_one, multiset.empty_eq_zero, multiset.cons_ne_zero, multiset.insert_eq_cons, eq_self_iff_true, false_or, and_self],
      -- we know : g.cycle_type.card ≤ 1
      rw nat.lt_succ_iff at hk1,
      cases nat.eq_or_lt_of_le hk1 with hk1 hk0,
      -- g.cycle_type.card = 1 : exfalso
      exfalso, rw [hk1, ← units.eq_iff] at hg0, norm_num at hg0,
      -- g.cycle_type.card = 0
      simp only [nat.lt_one_iff] at hk0,
      rw hk0 at this, simp only [K4_carrier, finset.mem_filter, this],
      simp, },

    rw multiset.eq_repeat',
    intros i hi,
    have := dvd_trans (multiset.dvd_lcm hi) hg,
    rw [nat.dvd_prime_pow] at this,
    obtain ⟨k, ⟨hk, rfl⟩⟩ := this,
    suffices : k = 1, rw this, norm_num,
    apply le_antisymm,
    rw ← not_lt, intro hk1,
    suffices : k = 2,
    apply h4, rw this at hi, exact hi,
    refine le_antisymm _ hk1,
    { -- k ≤ 2
      rw ← nat.pow_le_iff_le_right (nat.le_refl 2),
      norm_num, rw ← hα4,
      apply le_trans (equiv.perm.le_card_support_of_mem_cycle_type hi),
      apply finset.card_le_univ, },
    rw nat.one_le_iff_ne_zero, intro hk0,
    rw hk0 at hi, norm_num at hi,
    apply nat.lt_irrefl 1, exact equiv.perm.one_lt_of_mem_cycle_type hi,
    norm_num, },
end

lemma K4_carrier_card (hα4 : fintype.card α = 4) : finset.card (K4_carrier α) = 4 :=
begin
  simp only [K4_carrier],
  simp only [finset.filter_or],
  rw finset.card_union_eq _,
  simp [on_cycle_factors.equiv.perm.card_of_cycle_type, hα4],
  norm_num,
  -- disjoint
  intro x, simp only [multiset.empty_eq_zero, multiset.insert_eq_cons, finset.inf_eq_inter, finset.mem_inter, finset.mem_filter,
  finset.mem_univ, true_and, finset.bot_eq_empty, finset.not_mem_empty, and_imp],
  intro hx, rw hx, exact multiset.zero_ne_cons,
end

lemma K4_is_sylow (hα4 : fintype.card α = 4) (S : sylow 2 (alternating_group α)) :
  (K4_carrier α : set (equiv.perm α))= (subgroup.map (alternating_group α).subtype S) :=
begin
  classical,
  suffices hS4 : fintype.card S = 4,
  apply symm,
  apply set.eq_of_subset_of_card_le,

  { -- inclusion S ⊆ K4
    intros k hk,
    simp only [subgroup.coe_map, subgroup.coe_subtype, set.mem_image, set_like.mem_coe] at hk,
    obtain ⟨⟨g, hg⟩, ⟨hg', rfl⟩⟩ := hk,
    simp only [subgroup.coe_mk, finset.mem_coe],
    apply mem_K4_of_order_two_pow α hα4 g hg 2,
    norm_num,
    rw order_of_dvd_iff_pow_eq_one,
    have : order_of (⟨⟨g, hg⟩, hg'⟩ : S) ∣ fintype.card S := order_of_dvd_card_univ,
    rw [hS4, order_of_dvd_iff_pow_eq_one] at this,
    simp only [← subtype.coe_inj, submonoid_class.mk_pow, subgroup.coe_mk, subgroup.coe_one] at this,
    exact this, },

  -- card K4 ≤ card S
  simp only [finset.coe_sort_coe, fintype.card_coe, K4_carrier_card α hα4],
  apply le_of_eq, rw ← hS4,
  let u : S → subgroup.map (alternating_group α).subtype S := λ g,
    ⟨(alternating_group α).subtype g, ⟨g, ⟨g.prop, rfl⟩⟩⟩,
  have hu : function.bijective u,
  { split,
    { intros x y, simp [u], },
    { rintro ⟨x, hx⟩,
      simp only [subgroup.mem_map, subgroup.coe_subtype, exists_prop] at hx,
      obtain ⟨y, ⟨hy, rfl⟩⟩ := hx,
      use ⟨y, hy⟩,
      simp [u], }, },
  rw fintype.card_of_bijective hu, refl,

  -- card S = 4
  rw sylow.card_eq_multiplicity, rw ← nat.factors_count_eq ,
  -- rw nat.factorization_def,
  suffices : list.count 2 (fintype.card (alternating_group α)).factors = 2,
  rw this, norm_num,

  suffices : fintype.card (alternating_group α) = 12,
  rw this, norm_num,

  haveI : nontrivial α, rw [← fintype.one_lt_card_iff_nontrivial, hα4], norm_num,
  rw [← nat.mul_right_inj, two_mul_card_alternating_group, fintype.card_perm, hα4],
  norm_num, norm_num,
end

lemma K4_carrier_is_subgroup (hα4 : fintype.card α = 4) : ∃ S : subgroup ↥(alternating_group α), (K4_carrier α : set (equiv.perm α)) = (subgroup.map (alternating_group α).subtype S) :=
begin
  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  use S,
  exact K4_is_sylow α hα4 S,
end

lemma K4_carrier_le_alternating (hα4: fintype.card α = 4) :
  (K4_carrier α : set (equiv.perm α)) ⊆ (alternating_group α : set (equiv.perm α)) :=
begin
  obtain ⟨S, hS⟩ := K4_carrier_is_subgroup α hα4,
  rw hS, simp only [subgroup.coe_map, subgroup.coe_subtype, set.image_subset_iff],
  rintros ⟨g,  hg⟩ h,
  simp only [set.mem_preimage, subgroup.coe_mk, set_like.mem_coe, hg],
end

def K4 (hα4 : fintype.card α = 4) : subgroup (alternating_group α) := {
carrier := coe ⁻¹' (K4_carrier α : set (equiv.perm α)),
mul_mem' :=
begin
  obtain ⟨S, hS⟩ := K4_carrier_is_subgroup α hα4,
  rintros ⟨a, ha⟩ ⟨b, hb⟩ ha' hb',
  simp only [hS, subgroup.coe_map, subgroup.coe_subtype, set.mem_preimage, subgroup.coe_mk, set.mem_image, set_like.mem_coe] at ha' hb',
  obtain ⟨a', ⟨ha', rfl⟩⟩ := ha',
  obtain ⟨b', ⟨hb', rfl⟩⟩ := hb',
  simp only [hS, set.mem_preimage, set_like.eta],
  use a' * b',
  simp only [set_like.mem_coe, subgroup.coe_subtype, eq_self_iff_true, and_true],
  exact mul_mem ha' hb',
end,
one_mem' :=
begin
  obtain ⟨S, hS⟩ := K4_carrier_is_subgroup α hα4,
  simp only [hS, set.mem_preimage],
  use 1,
  simp only [set_like.mem_coe, subgroup.coe_subtype, eq_self_iff_true, and_true, S.one_mem],
end,
inv_mem' :=
begin
  obtain ⟨S, hS⟩ := K4_carrier_is_subgroup α hα4,
  rintros ⟨a, ha⟩ ha',
  simp only [hS, subgroup.coe_map, subgroup.coe_subtype, set.mem_preimage, subgroup.coe_mk, set.mem_image, set_like.mem_coe] at ha',
  obtain ⟨a', ⟨ha', rfl⟩⟩ := ha',
  simp only [hS, set.mem_preimage, set_like.eta],
  use a'⁻¹,
  simp only [inv_mem ha', set_like.mem_coe, subgroup.coe_subtype, eq_self_iff_true, and_self],
end }

theorem K4_carrier_coe (hα4 : fintype.card α = 4) :
  (K4 α hα4).carrier = coe ⁻¹' (K4_carrier α : set (equiv.perm α)) := rfl

theorem K4_mem_iff (hα4 : fintype.card α = 4) (g : alternating_group α) :
  g ∈ K4 α hα4  ↔ (g : equiv.perm α).cycle_type = {} ∨ (g : equiv.perm α).cycle_type = {2, 2} := by simp only [K4, K4_carrier, finset.coe_filter, finset.coe_univ, set.sep_univ, set.preimage_set_of_eq, subgroup.mem_mk,
  set.mem_set_of_eq]

instance K4_fintype (hα4 : fintype.card α = 4): fintype (K4 α hα4) :=
begin
  haveI : decidable_pred (λ (_x : ↥(alternating_group α)), _x ∈ K4 α hα4),
  intro x, simp_rw K4_mem_iff,
  apply_instance,
  apply subgroup.fintype,
end

theorem K4_card (hα4 : fintype.card α = 4) :
  fintype.card (K4 α hα4) = 4 :=
begin
  let u : K4 α hα4 → K4_carrier α := λ ⟨g, hg⟩, ⟨coe g,
  begin
    rw [← finset.mem_coe, ← set.mem_preimage, ← K4_carrier_coe α hα4],
    exact hg,
  end⟩,
  rw ← K4_carrier_card α hα4,
  have hu : function.bijective u,
  { split,
    rintros ⟨x, hx⟩ ⟨y, hy⟩, simp only [subtype.mk_eq_mk, set_like.coe_eq_coe, imp_self],
    rintro ⟨x, hx⟩,
    use ⟨x, K4_carrier_le_alternating α hα4 hx⟩,
    simp [← subgroup.mem_carrier, K4_carrier_coe, hx],
    simp [u], },
  rw fintype.card_of_bijective hu,
  simp only [fintype.card_coe],
end


def sK4 (hα4 : fintype.card α = 4) : sylow 2 (alternating_group α) := {
to_subgroup := K4 α hα4,
is_p_group' :=
begin
  rw is_p_group.iff_card,
  use 2, rw K4_card α hα4, norm_num,
end,
is_maximal' :=
begin
  classical,
  intros Q hQ hQ',
  obtain ⟨S, hS⟩ := is_p_group.exists_le_sylow hQ,
  rw is_p_group.iff_card  at hQ,
  apply le_antisymm _ hQ',
  apply le_trans hS,
  have := K4_is_sylow α hα4 S, -- rw K4_carrier_coe at this,
  intros g hg,
  rw [← subgroup.mem_carrier, K4_carrier_coe, set.mem_preimage, K4_is_sylow α hα4 S],
  simp [hg],
end }

theorem sK4_is_unique_two_sylow (hα4 : fintype.card α = 4) (S : sylow 2 (alternating_group α)) : S = sK4 α hα4 :=
begin
  apply symm, rw sylow.ext_iff,
  have hS := S.is_maximal',
  have hsK4 := (sK4 α hα4).is_p_group',
  apply hS hsK4,
  intros g hg,
  simp only [sK4, sylow.to_subgroup_eq_coe] at hg ⊢,
  rw [← subgroup.mem_carrier, K4_carrier_coe, set.mem_preimage, K4_is_sylow α hα4 S],
  simp [hg],
end


end alternating_group
