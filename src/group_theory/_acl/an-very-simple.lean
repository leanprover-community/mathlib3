/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic
-- import tactic.basic tactic.group tactic.ring
-- import tactic.interval_cases

import group_theory.solvable
import group_theory.perm.concrete_cycle
import group_theory.subgroup.basic
import group_theory.specific_groups.alternating
import group_theory.group_action.basic
import data.list.defs
import data.finset.basic
import data.equiv.transfer_instance
import group_theory.group_action.conj_act

import group_theory.perm.list
import data.list.cycle
import group_theory.perm.cycle_type

import .ad_sub_mul_actions
import .multiset_pigeonhole

variables {α : Type*} [decidable_eq α] [fintype α]

open subgroup equiv.perm equiv alternating_group
open_locale big_operators

/- Boring lemmas for powers of (-1 : units ℤ) -/

namespace int.units

lemma neg_one_ne_one : (-1 : units ℤ) ≠ 1 :=
begin
  intro h,
  rw ← units.eq_iff at h,
  simpa only using h,
end

lemma even_pow_of_neg_one (n : ℕ) (hn : even n) :
  (-1 : units ℤ)^n = 1 :=
begin
  rw ← units.eq_iff,
  rw [units.coe_pow, units.coe_neg_one, units.coe_one],
  exact nat.neg_one_pow_of_even hn,
end

lemma odd_pow_of_neg_one (n : ℕ) (hn : odd n) :
  (-1 : units ℤ)^n = -1 :=
begin
  rw ← units.eq_iff,
  simp only [units.coe_one, units.coe_neg_one, units.coe_pow],
  exact nat.neg_one_pow_of_odd hn,
end

lemma pow_of_neg_one_is_one_of_even_iff (n : ℕ) :
  even n ↔ (-1 : units ℤ)^n = 1  :=
begin
  split,
  exact even_pow_of_neg_one n,

  intro h,
  rw  nat.even_iff_not_odd,
  intro h',
  apply neg_one_ne_one,
  rw ← odd_pow_of_neg_one n h', exact h,
end

lemma pow_of_neg_one_is_neg_one_of_odd_iff (n : ℕ) :
  odd n ↔ (-1 : units ℤ)^n = -1  :=
begin
  split,
  exact odd_pow_of_neg_one n,

  intro h,
  rw  nat.odd_iff_not_even,
  intro h',
  rw even_pow_of_neg_one n h' at h,
  apply neg_one_ne_one,
  exact h.symm,
 end
end int.units


/-- Get an element distinct from those of a given list -/
lemma out_of_list {s : finset α} {l : list α} (h : l.length < s.card ) :
  ∃ (a : α), a ∈ s ∧ a ∉ l :=
begin
  let t := list.to_finset l,
  have : (s \ t).card > 0,
  { apply nat.lt_of_add_lt_add_right,
    rw [finset.card_sdiff_add_card  , zero_add],
    refine lt_of_lt_of_le
      (lt_of_le_of_lt (list.to_finset_card_le l) h)
      (finset.card_le_of_subset (finset.subset_union_left s t)),
  },
  obtain ⟨a : α, ha : a ∈ s \ t⟩ := finset.card_pos.mp this,
  use a,
  apply and.intro,
  exact (finset.mem_sdiff.mp ha).left,
  intro ha', apply (finset.mem_sdiff.mp ha).right,
  exact list.mem_to_finset.mpr ha'
end



/-! Additions to equiv.perm

* `is_cycle_cycle_of_iff` proves that `x` is in the support of `f : perm α`
iff `cycle_of f x` is a cycle.

* `support_card_eq_finset_sum_support_cycles_of` proves
that the cardinal of the support of a permutation is the sum of the lengths
of its cycles.

TODO ? : Add for list and trunc_list ?

-/




namespace equiv.perm

/-- x is in the support of f iff cycle_of f x is a cycle.-/
lemma is_cycle_cycle_of_iff [fintype α] (f : perm α) {x : α} :
  is_cycle (cycle_of f x) ↔ (f x ≠ x) :=
begin
  split,
  { intro hx, rw ne.def, rw ← cycle_of_eq_one_iff f,
    exact equiv.perm.is_cycle.ne_one hx, },
  { intro hx,
    apply equiv.perm.is_cycle_cycle_of, exact hx }
end

/-- If c is a cycle, a ∈ c.support and c is a cycle of g, then c = g.cycle_of a -/
lemma cycle_is_cycle_of {g c : perm α} {a : α}
  (ha : a ∈ c.support) (hc : c ∈ g.cycle_factors_finset) : c = g.cycle_of a :=
begin
  suffices : g.cycle_of a = c.cycle_of a,
  { rw this,
    apply symm,
    exact equiv.perm.is_cycle.cycle_of_eq
     ((equiv.perm.mem_cycle_factors_finset_iff.mp hc).left)
     (equiv.perm.mem_support.mp ha), },
  let hfc := (equiv.perm.disjoint_mul_inv_of_mem_cycle_factors_finset hc).symm,
  let hfc2 := (perm.disjoint.commute hfc),
  rw ← equiv.perm.cycle_of_mul_of_apply_right_eq_self hfc2,
  simp [hfc2.eq],
  -- a est dans le support de c, donc pas dans celui de g c⁻¹
  exact equiv.perm.not_mem_support.mp
    (finset.disjoint_left.mp (equiv.perm.disjoint.disjoint_support  hfc) ha),
end



/-- The sign of cycle is 1 iff its length is odd  -/
lemma sign_one_of_cycle_iff {f : perm α} (hf : f.is_cycle) :
  f.sign = 1 ↔ odd f.support.card :=
begin
  rw hf.sign,
  generalize : f.support.card = n,
  rw int.units.pow_of_neg_one_is_neg_one_of_odd_iff,
  generalize : (-1 : units ℤ)^n = u,
  split,
    intro h, rw ← h, rw units.neg_neg,
    intro h, rw h, rw units.neg_neg,
end

/-- A cycle belongs to the alternating group iff its length is odd -/
lemma mem_alternating_group_of_cycle_iff {f : perm α} (hf : f.is_cycle) :
  f ∈ alternating_group α ↔ odd f.support.card :=
begin
  rw ← sign_one_of_cycle_iff hf,
  exact equiv.perm.mem_alternating_group ,
end


lemma nodup_powers_of_cycle_of {f : perm α} {x : α}
  (i j : ℕ) (hij : i < j) (hj : j < (f.cycle_of x).support.card) :
  (f ^ i) x ≠ (f ^ j) x :=
begin
  have hx : f x ≠ x := equiv.perm.card_support_cycle_of_pos_iff.mp (lt_of_le_of_lt (zero_le j) hj),
  have hf : (f.cycle_of x).is_cycle := f.is_cycle_cycle_of hx,

  rw ← equiv.perm.order_of_is_cycle hf at hj,
  obtain ⟨k, hk, rfl⟩ := lt_iff_exists_add.mp  hij,
  rw pow_add f i k,
  rw equiv.perm.mul_apply,

  intro hfix,
  let hfix' := equiv.injective (f ^ i) hfix,
  rw ← equiv.perm.cycle_of_pow_apply_self  at  hfix',

  refine perm.mem_support.mp _ hfix'.symm,
  refine (equiv.perm.is_cycle.mem_support_pos_pow_iff_of_lt_order_of hf hk _).mpr _,
    exact lt_of_le_of_lt (nat.le_add_left k i) hj,
    rw perm.mem_support, rw equiv.perm.cycle_of_apply_self, exact hx,
end




open_locale classical

lemma mul_support_le (g h : perm α) : (g * h).support ⊆ h.support ∪ g.support :=
begin
  intro x,
  simp only [perm.coe_mul, function.comp_app, ne.def, finset.mem_union, perm.mem_support],
  apply not.imp_symm,
  simp only [not_or_distrib, not_not],
  intro H,
  simp only [H.left, H.right],
end

lemma commutator_support_le (g h : perm α) :
  (g * h * g⁻¹ * h⁻¹).support  ⊆ h.support ∪ g • h.support :=
begin
    suffices : (g * h * g⁻¹).support = g • h.support,
    { simp only [← equiv.perm.support_inv h],
      apply finset.subset.trans (mul_support_le (g * h * g⁻¹) h⁻¹),
      simp only [equiv.perm.support_inv h],
      rw this,
      apply finset.union_subset_union (le_refl h.support) (finset.subset.refl _) , },
    rw equiv.perm.support_conj,
    change finset.map (equiv.to_embedding g) h.support = finset.image g.to_fun h.support,
    rw finset.map_eq_image _ _,
    apply finset.image_congr,
    intros a ha, refl,
end

lemma commutator_support_le' (g h : perm α) :
  (g * h * g⁻¹ * h⁻¹).support ⊆ g.support ∪ h • g.support :=
begin
  rw ← equiv.perm.support_inv (g * h * g⁻¹ * h⁻¹),
  have : (g * h * g⁻¹ * h⁻¹)⁻¹ = h * g * h⁻¹ * g⁻¹ := by group,
  rw this,
  exact commutator_support_le h g,
end


lemma commutator_nontrivial (g h : perm α) (a : α) (hyp : g • a ≠ h • a) :
  g * h * g⁻¹ * h⁻¹ = 1 → g • h.support ⊆ h.support :=
begin
  intro k,
  have k' : g * h = h * g, { group, exact k, },
  intros a ha,
  change a ∈ finset.image (λ x, g • x) h.support at ha,
  rw finset.mem_image at ha,
  obtain ⟨b, hb, rfl⟩ := ha,
  rw equiv.perm.mem_support at hb ⊢,
  rw ← perm.smul_def, rw ← mul_smul, rw ← k', rw mul_smul,
  simp only [hb, perm.smul_def, ne.def, apply_eq_iff_eq],
  trivial,
end

end equiv.perm


lemma three_cycle_mk {a b c : α} -- (g : perm α)
  (h12 : a ≠ b) (h13 : a ≠ c) (h23 : b ≠ c) :
  ∃ (h : perm α), is_three_cycle h ∧
    (h a = b) ∧ (h b = c) ∧ (h c = a) ∧ h.support = {a,b,c} :=
begin
    let l := [a,b,c],
    have l_notnil : l ≠ list.nil,
    { suffices : l.length ≠ list.nil.length,
        intro z, apply this, rw z, dec_trivial },
    have l_nodup : l.nodup := by simp [h12, h13, h23],

    let cl : cycle α := [a,b,c],

    let h := cl.form_perm l_nodup,
    use h,

    have cl_is_nontrivial : cl.nontrivial,
    { rw cycle.nontrivial_coe_nodup_iff, dec_trivial, exact l_nodup, },
    have h_is_cycle : h.is_cycle :=
      cycle.is_cycle_form_perm cl l_nodup cl_is_nontrivial,
    have h_support_eq_l : h.support = l.to_finset :=
      cycle.support_form_perm cl l_nodup cl_is_nontrivial,
    have h_is_three_cycle : h.is_three_cycle,
    { rw ← card_support_eq_three_iff ,
      rw h_support_eq_l,
      rw list.card_to_finset l, rw list.nodup.erase_dup l_nodup, dec_trivial, },

    apply and.intro h_is_three_cycle,

    apply and.intro _, swap,
    { rw cycle.form_perm_apply_mem_eq_next cl l_nodup a _,
      swap,
      change a ∈ l,
      simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
      change l.next a _ = b,
      rw list.next_cons_cons_eq' , refl, },

    apply and.intro _, swap,
    { rw cycle.form_perm_apply_mem_eq_next cl l_nodup  b _,
      swap,
      change b ∈ l,
      simp only [list.mem_cons_iff, true_or, eq_self_iff_true, or_true],
      change l.next b _ = c,
      rw list.next_ne_head_ne_last,
        simp only [list.next_cons_cons_eq],
        apply h12.symm,
        { simp only [list.last, ne.def], apply h23 }, },

    apply and.intro,
    { rw cycle.form_perm_apply_mem_eq_next cl l_nodup c _,
      swap,
      change c ∈ l,
      simp only [list.mem_cons_iff, eq_self_iff_true, or_true, list.mem_singleton, apply_eq_iff_eq],
      change l.next c _ = a,
      rw  list.next_last_cons ,
        apply h13.symm,
        simp only [list.last],
        apply (list.nodup_cons.mp l_nodup).right,  },

    rw h_support_eq_l,
    simp only [insert_emptyc_eq, list.to_finset_nil, list.to_finset_cons],
end


namespace alternating_group

lemma case_cycle' (g : perm α) (a : α) (ha : a ≠ g a)
  (x : α) (hx : a ≠ x) (hx' : g a ≠ x) (hc'' : g (g a) ≠ x) :
  ∃ (h : perm α),
    (is_three_cycle h) ∧
    (g * h * g⁻¹ * h⁻¹) ≠ 1 ∧
    (support (g * h * g⁻¹ * h⁻¹)) ⊆ {a,g a, (g ^ 2) a, x, g x} :=
begin
    let g' := g.cycle_of a,

    let l := [a, g a, x],
    have l_notnil : l ≠ list.nil, by dec_trivial,
    have l_nodup : l.nodup := by simp [ha, hx, hx'],
    obtain ⟨h, h_is_three_cycle, ha_eq_b, hb_eq_c, hc_eq_a, hsup⟩ :=
      three_cycle_mk ha hx hx',

    have hb_neq_c : g (g a) ≠ x := hc'',

    use h,
    split,
    -- h est un 3-cycle
    exact h_is_three_cycle,
    split,

    { -- le commutateur est non trivial
      -- h = [a, g a, x] :
      -- Utiliser que g • (g a) ≠ h • (g a) = x
      intro hz,
      have hz' : g * h = h * g, { group, exact hz, },
      have : (g * h) a ≠ (h * g) a,
      { simp, -- only [perm.smul_mul, perm.mul_def],
        rw ha_eq_b, rw hb_eq_c, exact hb_neq_c, },
      apply this,
      rw hz' },

    apply finset.subset.trans (equiv.perm.commutator_support_le g h),
    apply finset.union_subset,
    { rw hsup,
      iterate { apply finset.insert_subset_insert, },
      apply finset.singleton_subset_iff.mpr,
      simp only [finset.mem_insert, or.intro_right, or.intro_left] },

    { change finset.image (λ x, g • x) h.support ⊆ {a, g a, (g ^ 2) a, x, g x},
      rw hsup,
      simp only [finset.image_insert, finset.insert_subset, finset.image_singleton,
        finset.singleton_subset_iff,
        finset.mem_insert, finset.mem_singleton,
        and.intro _,
        or.intro_left, or.intro_right,
        perm.smul_def,
        true_and, and_true, true_or, or_true],
     iterate { apply or.intro_left _ rfl <|> apply or.intro_right _,} },
end

lemma commutator_mem' {G : Type*} [group G] {N : subgroup G} (nN : normal N)
  (g : N) (h : G) : (g : G) * h * g⁻¹ * h⁻¹ ∈ N :=
begin
    let k := (g : G) * (h * g⁻¹ * h⁻¹),
    have : (g : G) * h * g⁻¹ * h⁻¹ = k := by group,
    rw this,
    apply (subgroup.mul_mem_cancel_left N (set_like.coe_mem g)).mpr,
    apply nN.conj_mem, apply inv_mem,
    exact set_like.coe_mem g
end


lemma has_three_cycle_normal (h5 : 5 ≤ fintype.card α)
  (N : subgroup (alternating_group α)) (nN : N.normal) :
  ∀ (n : ℕ) (g : N) (hg : (g : perm α) ≠ 1) (hsg : (support (g : perm α)).card = n),
  ∃ (f : N), is_three_cycle (f : perm α) :=
begin
  intro n,
  apply nat.strong_induction_on n,
  clear n, intros n ih,

  cases (nat.lt_or_ge n 2) with hn hn',
  { -- n < 2 : trivial case
    intros g hg hgs,
    exfalso,
    apply hg,
    rw ← hgs at hn,
    exact equiv.perm.card_support_le_one.mp (nat.le_of_lt_succ hn), },

  cases (nat.lt_or_ge n 3) with hn hn',
  { -- n = 2 : non swap
    intros g hg hgs,
    have hn2 : n = 2,
      apply le_antisymm (nat.le_of_lt_succ hn),
      rw ← hgs,
      exact equiv.perm.two_le_card_support_of_ne_one hg,
    rw hn2 at hgs,
    exfalso,
    apply  nat.even_iff_not_odd.mp (_ : even (g : perm α).support.card),
    rw ← equiv.perm.mem_alternating_group_of_cycle_iff (equiv.perm.card_support_eq_two.mp hgs).is_cycle,
    apply set_like.coe_mem,
    rw hgs, exact even_bit0 1 },

  -- have : hn' : 3 ≤ n
  intros g hg hgs,
  let l := (cycle_factors_finset (g : perm α)),

  cases (nat.lt_or_ge n 4) with hn hn',
  -- n = 3, g is a 3-cycle
  { rw (nat.eq_of_le_of_lt_succ hn' hn) at hgs, -- n.succ = 3
    rw card_support_eq_three_iff at hgs,  -- ↑g is a 3-cycle
    use g, exact hgs,  },

  -- Trivialities done, now the actual work starts
  -- hn' : 4 ≤ n


--  have : g.cycle_type.sum = g.support.card := equiv.perm.sum_cycle_type (g : perm α),

  have : (g : perm α).support.nonempty,
  { apply finset.nonempty_of_ne_empty ,
    intro h,
    apply nat.one_le_iff_ne_zero.mp (lt_of_lt_of_le _ hn'),
    rw [← hgs, h, finset.card_empty], dec_trivial },

  let ct := (g : perm α).cycle_type,
  have ct_ne_zero : ct ≠ 0, { intro h, apply hg, exact equiv.perm.cycle_type_eq_zero.mp h,  },

  have ct_sup_mem_ct : ct.sup ∈ ct := multiset.sup_mem_of _,
  swap,
  { intro h, apply hg, exact equiv.perm.cycle_type_eq_zero.mp h,  },
  have one_le_ct_sup : 1 ≤ ct.sup,
  { apply le_trans _ (equiv.perm.two_le_of_mem_cycle_type ct_sup_mem_ct),
    dec_trivial, },
  have ct_sup_ne_zero : ct.sup ≠ 0 := nat.one_le_iff_ne_zero.mp one_le_ct_sup,
  have ct_sum_eq_n : ct.sum = n,  { rw equiv.perm.sum_cycle_type, exact hgs, },

  have : ∃ (a : α), ((g : perm α).cycle_of a).support.card = ct.sup,
  { let ct_sup_mem_ct' : ct.sup ∈ (g : perm α).cycle_type := id ct_sup_mem_ct,
    rw equiv.perm.cycle_type_def (g : perm α) at ct_sup_mem_ct',
    obtain ⟨c, hc1, hc2 : c.support.card = ct.sup⟩ := multiset.mem_map.mp ct_sup_mem_ct,
    have : (perm.support c).nonempty,
    { apply finset.nonempty_of_ne_empty,
      intro hc0,
      apply ct_sup_ne_zero,
      rw [← hc2, hc0, finset.card_empty] },
    obtain ⟨a, h⟩ := this,
    use a,
    rw ← equiv.perm.cycle_is_cycle_of h (finset.mem_def.mpr hc1),
    exact hc2 },

  obtain ⟨a : α, h_of_a⟩ := this,

  have ha : a ∈ (g : perm α).support,
  { rw equiv.perm.mem_support,
    refine equiv.perm.card_support_cycle_of_pos_iff.mp _,
    rw h_of_a, exact one_le_ct_sup },
  have h'a : ((g : perm α).cycle_of a).is_cycle :=
    equiv.perm.is_cycle_cycle_of (g : perm α) (equiv.perm.mem_support.mp ha),

  -- La fonction qu'on va appeler
  let conclude_from := case_cycle' (g : perm α) a (ne.symm (equiv.perm.mem_support.mp ha)),

/- Trois cas  pour {a, g a, g (g a), x, g x}
  * n ≥ 6 : on prend x ≠ a, g a et on majore par 5
  * n ≤ 5 et ct.sup ≥ 4.
    Prouver n = 5 (si n = 4, g serait un 4-cycle, donc impair),
    prendre x = g⁻¹ a et on majore par 4
  * n ≤ 5 et ct.sup < 2.
    Prouver ct = {2,2} (tous les cycles ont longueur 2)
    prendre pour x un point fixe et on majore par 3
  -/

  cases nat.lt_or_ge n 6 with Hn6 Hn6,
  { -- n < 6
    cases nat.lt_or_ge ct.sup 5 with Hct5 Hct5,
    { -- ct.sup < 4
      -- prouver que g est (2,2), donc n = 4, prendre pour x un point fixe
      have Hn4 : n = 4 := sorry,
      have Hc2 : ct.sup = 2 := sorry,
      have Hct: ct = {2,2} := sorry,

      have : (g : perm α).supportᶜ.card > 0,
      { rw finset.card_compl,
        apply nat.sub_pos_of_lt,
        refine lt_of_le_of_lt _ h5,
        rw ← equiv.perm.sum_cycle_type,
        change ct.sum ≤ 4,
        rw Hct, dec_trivial, },

      obtain ⟨x, h'x⟩ := finset.card_pos.mp this,
      rw finset.mem_compl at h'x,

      have hx : a ≠ x,  { intro h, rw ← h at h'x, exact h'x ha, },
      have hx' : g a ≠ x,
      { intro h, rw ← h at h'x, exact h'x (equiv.perm.apply_mem_support.mpr ha), },
      have hx'' : g (g a) ≠ x,
      { intro h, rw ← h at h'x, apply h'x,
        apply equiv.perm.apply_mem_support.mpr,
        apply equiv.perm.apply_mem_support.mpr,
        exact ha, },

      obtain ⟨h, h1, h2, h3⟩ := conclude_from x hx hx' hx'',
      refine ih _ _ ⟨_, commutator_mem' nN g ⟨h,is_three_cycle.mem_alternating_group h1⟩⟩ h2 rfl,
      apply lt_of_le_of_lt (finset.card_le_of_subset h3),
      rw Hn4,

      -- g x = x
      rw equiv.perm.not_mem_support.mp h'x,

      have : ((g : perm α) ^ 2) a = a,
      { rw  equiv.perm.pow_apply_eq_pow_mod_order_of_cycle_of_apply,
        rw ← equiv.perm.order_of_is_cycle h'a at h_of_a,
        rw h_of_a, rw Hc2,
        simp only [nat.bit0_mod_two, id.def, pow_zero, perm.coe_one], },
      rw this,

      simp,
      apply nat.lt_succ_of_le,
      iterate { apply le_trans (finset.card_insert_le _ _), apply nat.add_le_add_right _ 1},
      rw finset.card_singleton },

    -- ct.sup ≥ 4, n ≤ 5
    -- prouver que g est (5), prendre x = g⁻¹ a
    have Hnc : n = ct.sup := sorry,
    have Hn5 : n = 5 := sorry,

    let x := g⁻¹ a,
    have hgx : (g : perm α) x = a := perm.eq_inv_iff_eq.mp rfl, -- g x = a
    have hx : a ≠ x,
    { intro h, rw ← h at hgx, exact (equiv.perm.mem_support.mp ha) hgx, },
    have hx' : (g : perm α) a ≠ x,
    { intro h, rw [← h, ← equiv.perm.mul_apply, ← sq] at hgx,
      refine (equiv.perm.nodup_powers_of_cycle_of 0 2 _ _) hgx.symm,
      dec_trivial,
      rw h_of_a, refine lt_of_lt_of_le _ Hct5, dec_trivial },
    have hx'' : (g : perm α) ((g : perm α) a) ≠ x,
    { intro h,
      simp only [← h, ← equiv.perm.mul_apply, ← mul_assoc] at hgx,
      rw [ ← pow_one (g : perm α)] at hgx,
      simp only [← pow_add] at hgx,
      refine (equiv.perm.nodup_powers_of_cycle_of 0 3 _ _) hgx.symm,
      dec_trivial,
      rw h_of_a, refine lt_of_lt_of_le _ Hct5, dec_trivial, },

    obtain ⟨h, h1, h2, h3⟩ := conclude_from x hx hx' hx'',
    refine ih _ _ ⟨_, commutator_mem' nN g ⟨h,is_three_cycle.mem_alternating_group h1⟩⟩ h2 rfl,
    apply lt_of_le_of_lt (finset.card_le_of_subset h3),
    rw Hn5,

    rw hgx, simp,

    apply nat.lt_succ_of_le,
    iterate { apply le_trans (finset.card_insert_le _ _), apply nat.add_le_add_right _ 1},
    rw finset.card_singleton, },

  -- n ≥ 6
  have : ∃ (x : α), x ≠ a ∧ x ≠ g a ∧ x ≠ g (g a),
  { have : [a, g a, g (g a)].length < finset.univ.card,
    { refine lt_of_lt_of_le _ (finset.card_le_univ (g : perm α).support),
      rw hgs,
      refine lt_of_lt_of_le _ Hn6,
      dec_trivial },
    obtain ⟨x, hx, hx'⟩ := out_of_list this,
    use x,
    repeat { apply and.intro },
    all_goals { intro h, apply hx', rw h, simp, } },

  obtain ⟨x, hx, hx', hx''⟩ := this,
  obtain ⟨h, h1, h2, h3⟩ := conclude_from x (ne.symm hx) (ne.symm hx') (ne.symm hx''),
  refine ih _ _ ⟨_, commutator_mem' nN g ⟨h,is_three_cycle.mem_alternating_group h1⟩⟩ h2 rfl,
  apply lt_of_le_of_lt (finset.card_le_of_subset h3),
  refine lt_of_lt_of_le _ Hn6,

  apply nat.lt_succ_of_le,
    iterate { apply le_trans (finset.card_insert_le _ _), apply nat.add_le_add_right _ 1},
    rw finset.card_singleton,
end



/-
subtype.coe_mk : ∀ (a : ?M_1) (h : ?M_2 a), ↑⟨a, h⟩ = a
set_like.coe_mk : ∀ (x : ?M_2) (hx : x ∈ ?M_4), ↑⟨x, hx⟩ = x

set_like.mem_coe : ?M_5 ∈ ↑?M_4 ↔ ?M_5 ∈ ?M_4
set_like.coe_mem : ∀ (x : ↥?M_4), ↑x ∈ ?M_4

set_like.eta : ∀ (x : ↥?M_4) (hx : ↑x ∈ ?M_4), ⟨↑x, hx⟩ = x
-/


theorem eq_bot_or_eq_top_of_normal (h5 : 5 ≤ fintype.card α)
  (N : subgroup (alternating_group α)) (nN : N.normal) :
  N = ⊥ ∨ N = ⊤ :=
begin
  cases subgroup.bot_or_nontrivial N with hNtriv ntN,
  exact or.intro_left _ hNtriv,
  apply or.intro_right _,
  apply top_unique,

  obtain ⟨g, hgN : g ∈ N, hg : g ≠ 1⟩ := (nontrivial_iff_exists_ne_one N).mp ntN,
  obtain ⟨f, hf⟩ := has_three_cycle_normal h5 N nN
    (support (g : perm α)).card ⟨g, hgN⟩ _ rfl,
  rw ← is_three_cycle.alternating_normal_closure h5 hf,
  apply normal_closure_le_normal,
  simp only [set_like.eta, set_like.coe_mem, set_like.mem_coe, set.singleton_subset_iff, coe_coe],

  -- (⟨g, hgN⟩ : ↥N) ≠ 1
  intro hg',  apply hg,
  simp only [← set_like.coe_eq_coe,  coe_coe],
  rw subgroup.coe_one, rw ← hg',
  simp only [coe_mk, coe_coe],
end

theorem is_simple
  (h5 : 5 ≤ fintype.card α) : is_simple_group (alternating_group α) :=
{exists_pair_ne :=
begin
  apply (alternating_group.nontrivial_of_three_le_card _).exists_pair_ne,
  apply le_trans _ h5,
  simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
end,
  eq_bot_or_eq_top_of_normal := λ N nN, eq_bot_or_eq_top_of_normal h5 N nN
}




#exit


lemma has_three_cycle_normal_rec (h5 : 5 ≤ fintype.card α)
  (N : subgroup (alternating_group α)) (nN : N.normal) :
  ∀ (n : ℕ), n ≥ 1 →
  ∀ (g : N) (hsg : (support (g : perm α)).card = n),
  ∃ (f : N), is_three_cycle (f : perm α) :=
begin
  intro n,
  induction n with n ih,
  { -- n = 0 : trivial
    intros hn,
    exfalso,
    simpa only [ge_iff_le, le_zero_iff] using hn, },

  -- induction case
  intros hn g hsg,

  have hg' : (g : perm α) ≠ 1,
  { intro hg,
    rw [hg, perm.support_one, finset.card_empty] at hsg,
    simpa only using hsg, },

  have hg : g ≠ 1,
  { intro h, rw h at hg',
    simpa only [subgroup.coe_one, coe_coe] using hg', },

  have hn' : n.succ ≥ 2,
  { rw ← hsg,
    exact equiv.perm.two_le_card_support_of_ne_one hg' },

  cases (nat.lt_or_ge n.succ 3) with hn hn',
  { -- hn : n.succ < 3
    -- exfalso : g ≠ 1, g ≠ swap
    have H2 : n.succ = 2,
      apply le_antisymm (nat.le_of_lt_succ hn),
      rw ← hsg,
      exact equiv.perm.two_le_card_support_of_ne_one hg',
    rw H2 at hsg,
    exfalso,
    apply  nat.even_iff_not_odd.mp (_ : even (g : perm α).support.card),
    rw ← equiv.perm.mem_alternating_group_of_cycle_iff (equiv.perm.card_support_eq_two.mp hsg).is_cycle,
    apply set_like.coe_mem,
    rw hsg, exact even_bit0 1 },

  -- have : hn' : 3 ≤ n.succ
  let l := (cycle_factors_finset (g : perm α)),

  cases (nat.lt_or_ge n.succ 4) with hn hn',
  -- H' : n.succ ≥ 3, H : n.succ < 4,
  { rw (nat.eq_of_le_of_lt_succ hn' hn) at hsg, -- n.succ = 3
    rw card_support_eq_three_iff at hsg,  -- ↑g is a 3-cycle
    use g, exact hsg,  },

  -- Trivialities done, now the actual work starts
  -- hn' : 4 ≤ n.succ
  have : n.succ = finset.sum  l  (λ c, (support c).card),
  { rw ← hsg,
    exact equiv.perm.support_card_eq_finset_sum_support_cycles_of (g : perm α), },

  -- Induction on the cardinality of l
  cases (nat.eq_zero_or_pos l.card) with Hl0 Hl0,

  { --  Case 0, l = [] :  exfalso from g ≠ 1
    rw finset.card_eq_zero at Hl0,
    rw equiv.perm.cycle_factors_finset_eq_empty_iff at Hl0,
    exfalso, exact hg' Hl0 },

  cases (nat.lt_or_ge l.card 2) with Hl1 Hl1,
  { -- Case 1, l = [↑g]
    let Hl1 := nat.eq_of_le_of_lt_succ Hl0 Hl1,
    obtain ⟨a, h⟩ := finset.card_eq_one.mp Hl1,
    let h' := (equiv.perm.cycle_factors_finset_eq_singleton_iff.mp h).left,
  -- on pourrait perdre que ↑g = a et aussi rw at h,
  -- car on n'aura plus besoin de l = {a}

  -- n.suc ≥ 5, car ≥ 4 et impair
    cases nat.lt_or_ge n.succ 5 with h4 h4',
    { let h4 := nat.eq_of_le_of_lt_succ hn' h4,
      rw h4 at hsg,
      exfalso,
      apply  nat.even_iff_not_odd.mp (_ : even (g : perm α).support.card),
      rw ← equiv.perm.mem_alternating_group_of_cycle_iff h',
      apply set_like.coe_mem,
      rw hsg, exact even_bit0 2 },


    sorry,

sorry,   },




example (s : finset α) (a b : α) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : 2 ≤ s.card :=
begin
  suffices : ({a,b} : finset α).card = 2,
  { rw ← this, apply finset.card_le_of_subset,
    rw finset.insert_subset,
    exact ⟨ha, finset.singleton_subset_iff.mpr hb⟩ },
  rw finset.card_insert_of_not_mem,
  rw finset.card_singleton,
  rw finset.mem_singleton, exact hab,
end

example (a b c d : ℕ) (h : c ≤ d) : a + d < b + c → a < b :=
begin
  intro k,
  apply nat.lt_of_add_lt_add_right,
  apply nat.lt_of_lt_of_le k,
  exact add_le_add_left h b,
end

example (a b c n : ℕ) (ha : a = 3) (hb : n + 4 < b) (hc : 2 ≤ c) :
  a + a < b + c :=
begin
  apply nat.lt_of_lt_of_le _ le_rfl,
  apply le_trans _ (nat.add_le_add (nat.lt_of_le_of_lt (le_add_self) hb) hc),
  rw ha,
end

example (a b c n : ℕ) (ha : a = 3) (hb : b = n + 5) (hc : 2 ≤ c) :
  a + a < b + c :=
begin
  rw [ha, hb],
  apply nat.le_trans le_rfl,
  apply le_trans _ (nat.add_le_add (le_add_self) hc),
  dec_trivial,

  /-
  suffices : 5 + 2 ≤ b + c,
    apply nat.lt_of_lt_of_le _ this,
    dec_trivial,
  suffices : 5 + 2 ≤ 5 + c,
    apply nat.le_trans this,
    apply add_le_add_right _ c,
    rw hb, exact le_add_self,
  exact add_le_add_left hc 5,
-/
    /-
  have hb' : 5 ≤ b,
  { rw hb, exact le_add_self, },
  have hb'c : 5 + c ≤ b + c,
  { exact add_le_add_right hb' c, },
  apply nat.lt_of_lt_of_le _ hb'c,
  have hc' : 5 + 2 ≤ 5 + c,
  { exact add_le_add_left hc 5, },
  apply nat.lt_of_lt_of_le _ hc',
  simp_rw ha,
  dec_trivial, -/
end
