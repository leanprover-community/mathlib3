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
import group_theory.abelianization
import group_theory.sylow
import .multiple_transitivity
import .multiple_primitivity

import .index_normal
import .conj_class_count

namespace alternating_group

variables (α : Type*) [decidable_eq α] [fintype α]

def V4 : subgroup (alternating_group α) :=
  subgroup.closure { g : alternating_group α | (g : equiv.perm α).cycle_type = {2,2} }

lemma mem_V4_of_order_two_pow (hα4 : fintype.card α = 4)
  (g : equiv.perm α) (hg0 : g ∈ alternating_group α) (n : ℕ) (hg : order_of g ∣ 2 ^ n) : g.cycle_type = {} ∨ g.cycle_type = {2,2} :=
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
      rw hk2 at this, simp only [this],
      simp only [finset.mem_univ, multiset.repeat_succ, multiset.repeat_one, multiset.empty_eq_zero, multiset.cons_ne_zero, multiset.insert_eq_cons, eq_self_iff_true, false_or, and_self],
      -- we know : g.cycle_type.card ≤ 1
      rw nat.lt_succ_iff at hk1,
      cases nat.eq_or_lt_of_le hk1 with hk1 hk0,
      -- g.cycle_type.card = 1 : exfalso
      exfalso, rw [hk1, ← units.eq_iff] at hg0, norm_num at hg0,
      -- g.cycle_type.card = 0
      simp only [nat.lt_one_iff] at hk0,
      rw hk0 at this, simp only [this],
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
    exact nat.prime_two, },
end

open_locale classical

lemma A4_card (hα4 : fintype.card α = 4) :
  fintype.card (alternating_group α) = 12 :=
begin
  haveI : nontrivial α, rw [← fintype.one_lt_card_iff_nontrivial, hα4], norm_num,
  apply mul_right_injective₀ _,
  rw [two_mul_card_alternating_group, fintype.card_perm, hα4],
  norm_num, norm_num,
end

lemma A4_sylow_card (hα4 : fintype.card α = 4) (S : sylow 2 (alternating_group α)) : fintype.card S = 4 :=
begin
  rw [sylow.card_eq_multiplicity, ← nat.factors_count_eq, A4_card α hα4],

  suffices : nat.factors 12 ~ [2, 2, 3],
  rw list.perm.count_eq this, norm_num,
  apply symm,
  apply nat.factors_unique,
  norm_num,
  norm_num,
  exact ⟨nat.prime_two, nat.prime_three⟩,
end

lemma A4_sylow_carrier (hα4 : fintype.card α = 4) (S : sylow 2 (alternating_group α)) : S.carrier = {g : alternating_group α | (g : equiv.perm α).cycle_type = 0 ∨ (g : equiv.perm α).cycle_type = {2, 2} } :=
begin
  apply set.eq_of_subset_of_card_le ,
  { -- inclusion S ⊆ (cycle_type = 0 ∨ cycle_type = { 2, 2 })
    intros k hk,
    simp only [set.mem_set_of_eq],
    obtain ⟨n, hn⟩ := (is_p_group.iff_order_of.mp S.is_p_group') ⟨k, hk⟩,
    apply mem_V4_of_order_two_pow α hα4 ↑k k.prop n,
    rw [← order_of_subgroup ⟨k, hk⟩, subgroup.coe_mk] at hn,
    rw [order_of_subgroup, hn], },
  -- card K4 ≤ card S
  change _ ≤ fintype.card S,
  rw A4_sylow_card α hα4 S,
  apply le_trans (fintype.card_subtype_or _ _),
  rw fintype.card_subtype, rw fintype.card_subtype,
  simp only [on_cycle_factors.alternating_group.card_of_cycle_type, hα4],
  norm_num,
end

lemma V4_is_unique_sylow (hα4 : fintype.card α = 4) (S : sylow 2 (alternating_group α)) :
  V4 α = S :=
begin
  classical,
  apply le_antisymm,
  { simp only [V4], rw subgroup.closure_le,
    intros g hg,
    rw [set_like.mem_coe, ← subgroup.mem_carrier, ← sylow.to_subgroup_eq_coe, A4_sylow_carrier α hα4 S, set.mem_set_of_eq],
    apply or.intro_right, exact hg, },
  { intros k hk,
    rw [← sylow.to_subgroup_eq_coe, ← subgroup.mem_carrier, A4_sylow_carrier α hα4 S, set.mem_set_of_eq] at hk,
    cases hk with hk hk,
    { suffices hk : k = 1, rw hk, exact subgroup.one_mem _,
      rw [← subtype.coe_inj, subgroup.coe_one,← equiv.perm.cycle_type_eq_zero, hk], },
    { simp only [V4],
      apply subgroup.subset_closure ,
      simp only [set.mem_set_of_eq],
      exact hk, } },
end

lemma A4_card_two_sylow_eq_one (hα4 : fintype.card α = 4) :
  fintype.card (sylow 2 (alternating_group α)) = 1 :=
begin
  rw fintype.card_eq_one_iff ,
  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  use S,
  intro T,
  rw sylow.ext_iff ,
  rw ← V4_is_unique_sylow α hα4 S,
  rw V4_is_unique_sylow α hα4 T,
end

lemma V4_is_characteristic (hα4 : fintype.card α = 4) :
  (V4 α).characteristic :=
begin
  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  rw V4_is_unique_sylow α hα4 S,
  refine sylow.characteristic_of_normal S _,
  rw ← subgroup.normalizer_eq_top ,
  rw ← subgroup.index_eq_one,
  rw ← card_sylow_eq_index_normalizer,
  exact A4_card_two_sylow_eq_one α hα4,
  /- rw ← V4_is_unique_sylow α hα4 S,
  exact V4_is_normal α hα4, -/
end

lemma V4_is_normal (hα4 : fintype.card α = 4) :
  (V4 α).normal :=
begin
  haveI := V4_is_characteristic α hα4,
  apply_instance,
  /-  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  rw V4_is_unique_sylow α hα4 S,
  rw ← subgroup.normalizer_eq_top ,
  rw ← subgroup.index_eq_one,
  rw ← card_sylow_eq_index_normalizer,
  exact A4_card_two_sylow_eq_one α hα4, -/
end

lemma V4_card (hα4 : fintype.card α = 4) : fintype.card (V4 α) = 4 :=
begin
  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  rw V4_is_unique_sylow α hα4 S,
  change fintype.card S = 4,
  exact A4_sylow_card α hα4 S,
end

lemma is_commutative_of_exponent_two (G : Type*) [group G]
(hG2 : ∀ g : G, g ^ 2 = 1) : is_commutative G (*) :=
begin
  suffices : ∀ g : G, g⁻¹ = g,
  apply is_commutative.mk,
  intros a b,
  rw [← mul_inv_eq_iff_eq_mul, ← mul_inv_eq_one, this, this, ← hG2 (a * b),  pow_two, mul_assoc (a * b) a b],
  { intro g, rw [← mul_eq_one_iff_inv_eq, ← hG2 g, pow_two] },
end

lemma V4_carrier_eq (hα4 : fintype.card α = 4) :
  (V4 α).carrier = {g : alternating_group α | (g : equiv.perm α).cycle_type = 0 ∨ (g : equiv.perm α).cycle_type = {2, 2} } :=
begin
  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  rw V4_is_unique_sylow α hα4 S,
  simpa only [sylow.to_subgroup_eq_coe] using A4_sylow_carrier α hα4 S,
end

lemma V4_is_of_exponent_two (hα4 : fintype.card α = 4):
  ∀ (g : V4 α), g ^ 2 = 1 :=
begin
  rintro ⟨⟨g, hg⟩, hg'⟩,
  simp only [← subtype.coe_inj, submonoid_class.mk_pow, subgroup.coe_mk, subgroup.coe_one],
  rw [← subgroup.mem_carrier, V4_carrier_eq α hα4] at hg',
  cases hg' with hg' hg',
  { simp only [subgroup.coe_mk, equiv.perm.cycle_type_eq_zero] at hg',
    simp only [hg', one_pow], },
  { convert pow_order_of_eq_one g,
    simp only [subgroup.coe_mk] at hg',
    rw [← equiv.perm.lcm_cycle_type, hg'],
    norm_num, },
end

lemma V4_is_commutative (hα4 : fintype.card α = 4) :
  (V4 α).is_commutative :=
begin
  refine {is_comm := _},
  apply is_commutative_of_exponent_two,
  exact V4_is_of_exponent_two α hα4,
end

theorem subgroup.quotient_is_commutative_iff_commutator_le {G : Type*} [group G] (H : subgroup G) [nH : H.normal] :
  is_commutative (G ⧸ H) (*) ↔ commutator G ≤ H :=
begin
  split,
  { intro h,
    simp only [commutator_eq_closure, subgroup.closure_le],
    rintros g ⟨g1, g2, rfl⟩,
    simp only [set_like.mem_coe, ← quotient_group.eq_one_iff],
    rw [← quotient_group.mk'_apply, map_commutator_element (quotient_group.mk' H) g1 g2],
    simp only [quotient_group.mk'_apply, commutator_element_eq_one_iff_mul_comm, h.comm], },
  { intro h,
    apply is_commutative.mk,
    intros a b,
    obtain ⟨g1, rfl⟩ := quotient_group.mk'_surjective H a,
    obtain ⟨g2, rfl⟩ := quotient_group.mk'_surjective H b,
    rw ← commutator_element_eq_one_iff_mul_comm,
    rw ← map_commutator_element _ g1 g2,
    rw quotient_group.mk'_apply,
    rw quotient_group.eq_one_iff ,
    apply h,
    apply subgroup.commutator_mem_commutator,
    refine subgroup.mem_top g1,
    refine subgroup.mem_top g2, },
end

example (hα4: 4 ≤ fintype.card α) (a b : α) (hab : a ≠ b) :
  ∃ (c : α), c ≠ a ∧ c ≠ b :=
begin
  suffices : ({a,b} : finset α)ᶜ.nonempty,
  obtain ⟨c, hc⟩ := this,
  use c,
  simp only [finset.compl_insert, finset.mem_erase, finset.mem_compl, finset.mem_singleton] at hc, exact hc,
  rw [← finset.card_compl_lt_iff_nonempty, compl_compl],
  refine lt_of_lt_of_le _ hα4,
  rw finset.card_doubleton hab,
  norm_num,
end

lemma alternating_group.center_bot (hα4 : 4 ≤ fintype.card α) :
  (alternating_group α).center = ⊥ :=
begin
  rw eq_bot_iff,
  rintros ⟨g, hg⟩ hg',
  simp only [subgroup.mem_bot],
  simp only [← subtype.coe_inj, subgroup.coe_mk, subgroup.coe_one],
  rw ←  equiv.perm.support_eq_empty_iff,
  rw finset.eq_empty_iff_forall_not_mem,
  intros a ha, let b := g a,
  have hab : b ≠ a,
  { simp only [b], rw ← equiv.perm.mem_support, exact ha, },
  have : ({a,b} : finset α)ᶜ.nonempty,
  { rw [← finset.card_compl_lt_iff_nonempty, compl_compl, finset.card_doubleton hab.symm],
    refine lt_of_lt_of_le (by norm_num) hα4, },
  obtain ⟨c, hc⟩ := this,
  simp only [finset.compl_insert, finset.mem_erase, ne.def, finset.mem_compl, finset.mem_singleton] at hc,

  have h2trans : mul_action.is_multiply_pretransitive (alternating_group α) α 2,
  { refine mul_action.is_multiply_pretransitive_of_higher
    (alternating_group α) α (mul_action.alternating_group_is_fully_minus_two_pretransitive α) _ _,
    rw nat.le_sub_iff_right,
    exact hα4,
    exact le_trans (by norm_num) hα4,
    simp only [part_enat.card_eq_coe_fintype_card, part_enat.coe_le_coe, tsub_le_self], },

  rw mul_action.is_two_pretransitive_iff at h2trans,
  obtain ⟨k, hk, hk'⟩ := h2trans a b a c hab.symm (ne.symm hc.left),
  suffices : k • ((⟨g, hg⟩ : alternating_group α)• a) ≠ c,
  apply this, rw ← hk', refl,

  suffices : k • ((⟨g, hg⟩ : alternating_group α) • a) = (⟨g, hg⟩ : alternating_group α) • (k • a),
  rw [this, hk], exact ne.symm hc.right,

  rw subgroup.mem_center_iff at hg',
  specialize hg' k,
  simp only [smul_smul, hg'],
end

lemma V4_eq_commutator (hα4 : fintype.card α = 4) :
  V4 α = commutator (alternating_group α) :=
begin
  haveI : (V4 α).normal := V4_is_normal α hα4,
  have comm_le : commutator (alternating_group α) ≤ V4 α,
  rw ← subgroup.quotient_is_commutative_iff_commutator_le,
  { apply is_commutative_of_prime_order _,
    apply_instance,
    exact 3,
    exact nat.fact_prime_three,
    apply mul_left_injective₀ _,
    dsimp,
    rw [← subgroup.card_eq_card_quotient_mul_card_subgroup,
    V4_card α hα4, A4_card α hα4], norm_num,
    rw V4_card α hα4, norm_num, },

  have comm_ne_bot : commutator (alternating_group α) ≠ ⊥,
  { intro h,
    simp only [commutator, subgroup.commutator_eq_bot_iff_le_centralizer, subgroup.centralizer_top, ← eq_top_iff] at h,
    rw alternating_group.center_bot _ at h,
    suffices : nat.card (alternating_group α) ≠ 1,
    apply this, rw [← subgroup.index_bot, h, subgroup.index_top],
    apply ne.symm,
    apply ne_of_lt,
    rw finite.one_lt_card_iff_nontrivial,
    apply nontrivial_of_three_le_card,
    rw hα4, norm_num,
    rw hα4, },

  obtain ⟨k, hk, hk'⟩ := or.resolve_left (subgroup.bot_or_exists_ne_one _) comm_ne_bot,
  suffices hk22 : (k : equiv.perm α).cycle_type = {2,2},
  refine le_antisymm _ comm_le,
  intros g hg,
  rw [← subgroup.mem_carrier, V4_carrier_eq α hα4] at hg,
  cases hg with hg hg,
  { rw [equiv.perm.cycle_type_eq_zero, one_mem_class.coe_eq_one] at hg,
    rw hg,
    exact subgroup.one_mem _,},
  { rw [← hg, ← equiv.perm.is_conj_iff_cycle_type_eq, is_conj_iff] at hk22,
    obtain ⟨c, hc⟩ := hk22,
    rw [← mul_aut.conj_normal_apply, subtype.coe_inj] at hc,
    simp only [commutator, ← hc],
    let fc : mul_aut (alternating_group α) := mul_aut.conj_normal c,
    suffices : (⊤ : subgroup (alternating_group α)) = subgroup.map fc.to_monoid_hom (⊤ : subgroup (alternating_group α)),
    rw [this, ← subgroup.map_commutator],
    refine subgroup.mem_map_of_mem _ hk,
    { apply symm,
      rw ← monoid_hom.range_eq_map,
      rw monoid_hom.range_top_iff_surjective,
      exact mul_equiv.surjective _, } },
  { have hk2 := comm_le hk,
    rw [← subgroup.mem_carrier, V4_carrier_eq α hα4] at hk2,
    cases hk2 with hk2 hk2,
    { exfalso,
      apply hk',
      rw equiv.perm.cycle_type_eq_zero  at hk2,
      simp only [← subtype.coe_inj, hk2, subgroup.coe_one], },
    exact hk2,},
end

end alternating_group
