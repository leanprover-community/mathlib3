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
import data.equiv.transfer_instance
import group_theory.group_action.conj_act

import group_theory.perm.list
import data.list.cycle
import group_theory.perm.cycle_type

import .ad_sub_mul_actions


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

/-- the cardinal of the support of a permutation is the sum of the lengths
of its cycles  -/
lemma support_card_eq_finset_sum_support_cycles_of
  (f : perm α) :
  finset.card (support f) =
  finset.sum  (cycle_factors_finset f)  (λ c, (support c).card) :=
begin
    rw ← finset.card_bUnion  ,
    -- cycles of l have disjoint support
    swap,
    { exact λ x hx y hy hxy, equiv.perm.disjoint.disjoint_support
        (cycle_factors_finset_pairwise_disjoint f x hx y hy hxy) },
    -- support of g is union of supports of l
    apply congr_arg,
    ext a,
    rw ← cycle_of_mem_cycle_factors_finset_iff ,
    rw mem_cycle_factors_finset_iff,
    split,
    { intro hyp,
      rw finset.mem_bUnion,
      use f.cycle_of a,
      split,
      { rw equiv.perm.mem_cycle_factors_finset_iff,
        exact hyp, },
      { rw mem_support,
        rw cycle_of_apply_self ,
        exact (equiv.perm.is_cycle_cycle_of_iff f).mp hyp.left },
    },
    { intro ha,
      rw finset.mem_bUnion at ha,
      obtain ⟨c, hc, ha⟩ := ha,
      rw equiv.perm.mem_cycle_factors_finset_iff at hc,
      split,
      { apply equiv.perm.is_cycle_cycle_of,
        rw ← hc.right a ha,
        apply mem_support.mp ha, },
      { intros b hb,
        rw equiv.perm.mem_support_cycle_of_iff at hb,
        apply equiv.perm.same_cycle.cycle_of_apply,
        exact hb.left }  },
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


end equiv.perm


namespace alternating_group

-- equiv.perm.two_le_card_support_of_ne_one :

example (n : ℕ) (h_lt_3 : n < 3) (h_ge_2 : n ≥ 2) : n = 2 :=
nat.eq_of_le_of_lt_succ h_ge_2 h_lt_3


lemma has_three_cycle_normal_rec_1 (h5 : 5 ≤ fintype.card α)
  (N : subgroup (alternating_group α)) (nN : N.normal) :
  ∀ (g : N) (hsg : (support (g : perm α)).card = 1),
  false :=
begin
  sorry,
end


example (f : perm α) (hf : f.is_cycle) (x : α) (hx : f x ≠ x)
  (i : ℕ) (hi0 : 0 < i) (his : i < f.support.card) :
  (f ^ i) x ≠ x :=
begin
  have hi0' : i ≠ 0 := ne_of_gt hi0,
  rw ← equiv.perm.order_of_is_cycle hf at his,
  intro hfix,
  apply  pow_ne_one_of_lt_order_of' hi0' his,
  apply equiv.perm.ext,
  intro y,
  by_contradiction, rw ← ne.def at h,
  have hx' : x ∈ f.support := perm.mem_support.mpr hx,
  rw ← equiv.perm.is_cycle.mem_support_pos_pow_iff_of_lt_order_of hf hi0 his at hx',
  rw perm.mem_support at hx',
  exact hx' hfix,
end

lemma nodup_of_fullcycle {f : perm α} (hf : f.is_cycle) {x : α} (hx : f x ≠ x)
  (i j : ℕ) (hij : i < j) (hj : j < f.support.card) :
  (f ^ i) x ≠ (f ^ j) x :=
begin
  rw ← equiv.perm.order_of_is_cycle hf at hj,
  obtain ⟨k, hk, rfl⟩ := lt_iff_exists_add.mp  hij,
  rw pow_add f i k,
  rw equiv.perm.mul_apply,
  intro hfix,

  have hk' : k ≠ 0 := ne_of_gt hk,
  have hk'' : k < order_of f :=
    lt_of_le_of_lt (nat.le_add_left k i) hj,

  have hx' : x ∈ f.support := perm.mem_support.mpr hx,
  rw ← equiv.perm.is_cycle.mem_support_pos_pow_iff_of_lt_order_of hf hk hk'' at hx',
  rw perm.mem_support at hx',

  apply hx',
  apply equiv.injective (f ^ i),
  exact hfix.symm,
end


lemma nodup_of_sorted_and_bounded (n : ℕ)
  (f : ℕ → α) (hf : ∀ (i j : ℕ), i < n → j < n → i < j → (f i ≠ f j))
  (l : list ℕ) (hln : l.length ≤ n)
  (hl : list.sorted (<) l)
  (hl' : ∀ (i : ℕ), i ∈ l → i < n) :
  (list.map f l).nodup :=
begin
  rw list.nodup_map_iff_inj_on,
  swap,
  apply list.sorted.nodup _,
  exact (<),
  exact has_lt.lt.is_irrefl,
  exact hl,
  intros x hx y hy hxy,
  cases lt_or_ge x y with h h',
  exfalso, exact hf x y (hl' x hx) (hl' y hy) h hxy,
  cases lt_or_eq_of_le h' with h h',
  exfalso, exact hf y x (hl' y hy) (hl' x hx) h hxy.symm,
  exact h'.symm,
end


lemma extract_cycle_of (g : perm α) (hg : g.is_cycle) (a : α) (ha : g a ≠ a) (l : list ℕ)
  (hl : list.sorted (<) l) (hl' : ∀ (i : ℕ), i ∈ l → i < order_of g) (hl'' : l.length ≤ order_of g) :
  (list.map (λ i, (g ^ i) a) l).nodup :=
begin
  refine nodup_of_sorted_and_bounded (order_of g)
  (λ i, (g ^ i) a) _ l _ hl hl',
  { intros i j hi hj hij,
    rw equiv.perm.order_of_is_cycle hg at hj,
    apply nodup_of_fullcycle hg ha i j hij hj },
  exact hl'',
end

example (l : list α) (hl : l.nodup) (h2 : 2 ≤ l.length) :
  order_of l.form_perm = l.length :=
begin
  let p := l.form_perm,
  have p_is_cycle : p.is_cycle := list.is_cycle_form_perm hl h2,
  rw equiv.perm.order_of_is_cycle p_is_cycle,
  rw ← list.nodup.erase_dup hl,
  rw ← list.card_to_finset l,
  apply congr_arg,

  -- il reste à prouver : p.support = l.to_finset
  change l.form_perm.support = l.to_finset,
  rw ← cycle.form_perm_coe l hl ,
  rw cycle.support_form_perm ,
  refl,
  rw cycle.nontrivial_coe_nodup_iff, apply h2, apply hl,
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

lemma finset.map_eq_image {α β : Type*} (f : α ↪ β) (s : finset α) :
  finset.map f s = finset.image f.to_fun s :=
begin
  ext a,
  simp only [finset.mem_map, function.embedding.to_fun_eq_coe, finset.mem_image],
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
    suffices : (equiv.to_embedding g).to_fun = g.to_fun,
    {  rw this, simp only [to_fun_as_coe], ext, simp only [finset.mem_image] },
    refl,
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


lemma list.mem_to_finset' (l : list α) (a : α) : a ∈ l.to_finset ↔ a ∈ (l : cycle α).to_finset :=
begin
  rw list.mem_to_finset,
--  rw ← cycle.mem_coe_iff , -- inutile
  unfold cycle.to_finset, -- change a ∈ ↑l ↔ a ∈ (l : cycle α).to_multiset.to_finset,
  rw multiset.mem_to_finset,
  apply multiset.mem_coe,
end

lemma list.cycle_coe_to_finset  (l : list α) : l.to_finset = (l : cycle α).to_finset :=
begin
  ext a,
  apply list.mem_to_finset',
end

.

example (s : finset α) (g : perm α) : (g • s).card = s.card :=
begin
  apply finset.card_image_of_injective,
  apply mul_action.injective g,
end

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


lemma case_cycle5 (g : perm α) (hg : g.is_cycle) (hg' : order_of g ≥ 5) :
  ∃ (h : perm α), (is_three_cycle h) ∧
    (g * h * g⁻¹ * h⁻¹) ≠ 1 ∧ (g * h * g⁻¹ * h⁻¹).support.card < g.support.card :=
begin
    obtain ⟨n : ℕ, hg'' : order_of g = 5 + n⟩ :=
      nat.exists_eq_add_of_le hg', rw add_comm at hg'',
    obtain ⟨a, ha ⟩ := id hg,  -- trick to not destruct hg
    let l := [a, g a, (g ^ (n+4)) a], -- a b e

    have hn : n + 4 < g.support.card,
      { rw ← equiv.perm.order_of_is_cycle hg,
        rw hg'',
        simp only [nat.bit0_lt_bit1_iff, add_lt_add_iff_left], },

    have l_notnil : l ≠ list.nil,
    { suffices : l.length ≠ list.nil.length,
        intro z, apply this, rw z, dec_trivial },

    have h12 : a ≠ g a := ha.left.symm,
    have h13 : a ≠ (g ^ (n+4)) a,
    { refine nodup_of_fullcycle  hg ha.left 0 (n+4) _ hn, dec_trivial, },
    have h23 : g a ≠ (g ^ (n+4)) a,
    { refine nodup_of_fullcycle  hg ha.left 1 (n+4) _ hn, dec_trivial, },
    have l_nodup : l.nodup := by simp [h12, h13, h23],

    let c : cycle α := l,
    let h := (l : cycle α).form_perm l_nodup,
    have c_is_nontrivial : c.nontrivial,
    { rw cycle.nontrivial_coe_nodup_iff, dec_trivial, exact l_nodup, },
    have h_is_cycle : h.is_cycle :=
      cycle.is_cycle_form_perm c l_nodup c_is_nontrivial,
    have h_support_eq_l : h.support = l.to_finset :=
      cycle.support_form_perm c l_nodup c_is_nontrivial,
    have h_is_three_cycle : h.is_three_cycle,
    { rw ← card_support_eq_three_iff ,
      rw h_support_eq_l,
      rw list.card_to_finset l, rw list.nodup.erase_dup l_nodup, dec_trivial, },

    have ha_eq_b : h a = g a,
    { rw cycle.form_perm_apply_mem_eq_next c l_nodup a _,
      swap,
      change a ∈ l,
      simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
      change l.next a _ = g a ,
      rw list.next_cons_cons_eq' , refl, },

    have hb_eq_c : h (g a) = (g ^ (n+4)) a,
    { rw cycle.form_perm_apply_mem_eq_next c l_nodup (g a) _,
      swap,
      change g a ∈ l,
      simp only [list.mem_cons_iff, true_or, eq_self_iff_true, or_true],
      change l.next (g a) _ = (g ^ (n+4)) a,
      rw list.next_ne_head_ne_last,
        simp only [list.next_cons_cons_eq],
        apply h12.symm,
        { simp only [list.last, ne.def], apply h23 }, },

    have hc_eq_a : h ((g ^ (n+4)) a) = a,
    { rw cycle.form_perm_apply_mem_eq_next c l_nodup ((g ^ (n+4)) a) _,
      swap,
      change ((g ^ (n+4)) a) ∈ l,
      simp only [list.mem_cons_iff, eq_self_iff_true, or_true, list.mem_singleton, apply_eq_iff_eq],
      change l.next ((g ^ (n+4)) a) _ = a,
      rw  list.next_last_cons ,
        apply h13.symm,
        simp only [list.last],
        apply (list.nodup_cons.mp l_nodup).right,  },

    have hb_neq_e : g (g a) ≠ (g ^ (n+4)) a,
    { refine nodup_of_fullcycle hg ha.left 2 (n+4) _ hn,
      dec_trivial, },

    use h,
    split,
    -- h est un 3-cycle
    exact h_is_three_cycle,
    split,

    { -- le commutateur est non trivial
      -- h = [a, b, e] : b = g a, g e = a,
      -- Utiliser que g • b ≠ h • b
      -- g h g⁻¹ h⁻¹ b = g h g⁻¹ a = g h e = g a = b
      -- g h g⁻¹ h⁻¹ a = g h g⁻¹ e = g h d = g d = e ≠ a
      -- g h g⁻¹ h⁻¹ e = g h g⁻¹ b = g h a = g (g a) ≠ e
      /- intro hz,
      let ww := commutator_nontrivial g h (g a) _ hz,
      sorry, -/
      intro hz,
      have hz' : g * h = h * g, { group, exact hz, },
      have : (g * h) a ≠ (h * g) a,
      { simp, -- only [perm.smul_mul, perm.mul_def],
        rw ha_eq_b, rw hb_eq_c, exact hb_neq_e, },
      apply this,
      rw hz' },

    { -- son support est de cardinal < celui de g
      let www := finset.card_le_of_subset (commutator_support_le g h),
      refine nat.lt_of_le_of_lt www _,
      refine nat.lt_of_add_lt_add_right _,
      swap, -- exact (h.support ∩ g • h.support).card,
      rw finset.card_union_add_card_inter,

      have : (g • h.support).card = h.support.card,
      { apply finset.card_image_of_injective,  exact mul_action.injective g, },
      rw this,

      conv_lhs {
        rw h_support_eq_l,
        },
      rw list.to_finset_card_of_nodup l_nodup,

      suffices : 2 ≤ (h.support ∩ g • h.support).card,
      {
      apply nat.lt_of_lt_of_le _ le_rfl,
      apply le_trans _ (nat.add_le_add (nat.lt_of_le_of_lt (le_add_self) hn) this),
      dec_trivial },

      -- h.suport = [a, g a, (g ^ (n+4)) a]
      -- g • h.support = [g a, (g ^ 2) a, g ^ (n+5) a] = [g a, a]
      have ha : a ∈ h.support ∩ g • h.support,
      { rw finset.mem_inter, split,
        rw equiv.perm.mem_support, rw ha_eq_b, exact h12.symm,
        suffices : g⁻¹ • a ∈ h.support,
        {
          sorry, },
        rw equiv.perm.mem_support,
        have : g⁻¹ = g ^ (n+4),
        { rw inv_eq_iff_mul_eq_one,
          rw ← pow_succ,
          change g ^ (n + 5) = 1,
          rw ← hg'',
          exact pow_order_of_eq_one g, },
        rw this,
        simp,
        rw hc_eq_a,
        exact h13, },

      have hga : g a ∈ h.support ∩ g • h.support,
      { sorry, },
      suffices : ({a,g a} : finset α).card = 2,
        { rw ← this, apply finset.card_le_of_subset,
          rw finset.insert_subset,
          exact ⟨ha, finset.singleton_subset_iff.mpr hga⟩ },
        rw finset.card_insert_of_not_mem,
        rw finset.card_singleton,
        rw finset.mem_singleton,
        exact h12 }
end



/-
    g = (a,b,c,d,…,e)
    h = (a,b,e)
    g • a = b,
    g • b = c ≠ h • b -/

  /-

    obtain ⟨n_minus_5 : ℕ, hn_minus_5 : n = 5 + n_minus_5⟩ :=
        nat.exists_eq_add_of_le hn', rw add_comm at hn_minus_5,

    obtain ⟨a, ha⟩ := id is_cycle_g,
    let hl := list.map (λ (i : ℕ), ((g : perm α) ^ i) a) [0, 1, order_of (g : perm α) - 1],
    have hl_length_3 : hl.length = 3, dec_trivial,
    have h2_le_hl_length : 2 ≤ hl.length := dec_trivial,
    have hl_nodup : hl.nodup,
    { have : ∃ (n_minus_5 : ℕ), n = n_minus_5 + 5,
        obtain ⟨n_minus_5 : ℕ, rfl⟩ := nat.exists_eq_add_of_le hn',
        rw add_comm, use n_minus_5,
      obtain ⟨n_minus_5, rfl⟩ := this,
      apply extract_cycle_of (g : perm α) is_cycle_g a ha.left [0, 1, order_of (g : perm α) - 1] ,
      rw hgs',  dec_trivial,
      rw hgs',  simp,
      rw hgs',  simp,  change 3 ≤ n_minus_5 + 5, rw ← nat.zero_add 3, apply add_le_add,
      apply nat.zero_le, dec_trivial,  },


    let hc := (hl : cycle α).form_perm hl_nodup,
    let hp := hl.form_perm,
    have hp_eq_hc : hc = hp := cycle.form_perm_coe hl hl_nodup,

    have hc_nt : (hl : cycle α).nontrivial,
    { rw cycle.nontrivial_coe_nodup_iff, apply h2_le_hl_length, apply hl_nodup,},

    have hp_is_cycle : hp.is_cycle :=
      list.is_cycle_form_perm hl_nodup h2_le_hl_length,

    have hc_is_cycle : hc.is_cycle :=
      cycle.is_cycle_form_perm (hl : cycle α) hl_nodup hc_nt,

    have hc_support_eq_hl : hc.support = hl.to_finset :=
      cycle.support_form_perm (hl : cycle α) hl_nodup hc_nt,

    have hp_is_three_cycle : hc.is_three_cycle,
    {  rw ← card_support_eq_three_iff ,
        rw hc_support_eq_hl,
          rw list.card_to_finset hl,
          rw list.nodup.erase_dup hl_nodup, dec_trivial, },


    have hp_even : hp ∈ alternating_group α :=
      is_three_cycle.mem_alternating_group hp_is_three_cycle,

    let hp' : alternating_group α := ⟨hp, hp_even⟩,

    let g' : N := ⟨hp' * g * hp'⁻¹, nN.conj_mem g (set_like.coe_mem g) hp'⟩,

    have supp_comp : (g' * g⁻¹ : perm α).support ⊆ g • (hp' : perm α).support ∪ (hp' : perm α).support,

    have hg'_ne_g :  g' ≠ g,
    {  sorry, },




  -/


-- subgroup.map : (G →* N) → (subgroup G) → (subgroup N)
-- H.inclusion (H ≤ K) : ↥H →* ↑K

-- subgroup.subtype N : ↥N →* ↥H


lemma commutator_mem {G : Type*} [group G] {H : subgroup G} {N: subgroup H}
  (nN : normal N) (g : N) (h : G) (h' : h ∈ H) :
  ((g : G) * h * g⁻¹ * h⁻¹) ∈ (N : subgroup G) :=
-- let k : G := g * h * g⁻¹ * h⁻¹
-- let jH : ↥H →* G := subgroup.subtype H
begin
  let hH  : H := ⟨h, h'⟩,
  rw ← set_like.coe_mk h h',
  let k := (g : H) * (hH * g⁻¹ * hH⁻¹),
  suffices : k ∈ N,
  { rw subgroup.mem_map,
    use k,
    apply and.intro this,
    simp only [subgroup.coe_subtype, coe_mk, coe_inv, subgroup.coe_mul, coe_coe],
    group, },
  apply (subgroup.mul_mem_cancel_left N (set_like.coe_mem g)).mpr,
  apply nN.conj_mem, apply inv_mem,
  exact set_like.coe_mem g,
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


lemma has_three_cycle_normal_rec' (h5 : 5 ≤ fintype.card α)
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
  have : n = finset.sum  l  (λ c, (support c).card),
  { rw ← hgs,
    exact equiv.perm.support_card_eq_finset_sum_support_cycles_of (g : perm α), },

  -- Induction on the cardinality of l
  cases (nat.eq_zero_or_pos l.card) with Hl0 Hl0,

  { --  Case 0, l = [] :  exfalso from g ≠ 1
    rw finset.card_eq_zero at Hl0,
    rw equiv.perm.cycle_factors_finset_eq_empty_iff at Hl0,
    exfalso, exact hg Hl0 },

  cases (nat.lt_or_ge l.card 2) with Hl1 Hl1,
  { -- Case 1, l = [↑g]
    let Hl1 := nat.eq_of_le_of_lt_succ Hl0 Hl1,
    obtain ⟨a, h⟩ := finset.card_eq_one.mp Hl1,
    let is_cycle_g := (equiv.perm.cycle_factors_finset_eq_singleton_iff.mp h).left,
    have hgs' : order_of (g : perm α) = n,
    { rw equiv.perm.order_of_is_cycle is_cycle_g, exact hgs, },
    -- have hgs'' : order_of g = n,
    -- { simp only [order_of_subgroup, coe_coe] at hgs', exact hgs', },
  -- on pourrait perdre que ↑g = a et aussi rw at h,
  -- car on n'aura plus besoin de l = {a}

  -- n.suc ≥ 5, car ≥ 4 et impair
    cases nat.lt_or_ge n 5 with hn hn',
    { let hn4 := nat.eq_of_le_of_lt_succ hn' hn,
      rw hn4 at hgs,
      exfalso,
      apply  nat.even_iff_not_odd.mp (_ : even (g : perm α).support.card),
      rw ← equiv.perm.mem_alternating_group_of_cycle_iff is_cycle_g,
      apply set_like.coe_mem,
      rw hgs, exact even_bit0 2 },

    -- the heart of the case where g is a cycle (of length ≥ 5)
    -- one gets a 3-cycle such that the commutator g * h * g⁻¹ * h⁻¹ will allow to conclude
    obtain ⟨h, h1, h2, h3⟩ := case_cycle5 (g : perm α) is_cycle_g _,
    swap, { rw hgs', exact hn', },
    -- introduce a notation for the commutator and rewrite
    let k := (g : perm α) * h * g⁻¹ * h⁻¹,
    change k ≠ 1 at h2,
    change k.support.card < (g : perm α).support.card at h3,
    -- the 3-cycle is an even permutation, subtype, rewrite
    let h' : alternating_group α := ⟨h,is_three_cycle.mem_alternating_group h1⟩,
    let k' := (g : alternating_group α) * h' * g⁻¹ * h'⁻¹,
    have : k = ↑k' := by simp only [coe_mk, coe_inv, subgroup.coe_mul, mul_left_inj, coe_coe],
    rw this at h2 h3,
    rw hgs at h3,
    -- conclude by induction : commutator_mem' says that k' ∈ N
    exact ih (k' : perm α).support.card h3 ⟨k', commutator_mem' nN g h'⟩ h2 rfl, },


      /- Trois groupes : N ≤ H ≤ G
      * G = perm α,
      * H = alternating_group α: subgroup (perm α)
      * N : subgroup H, nN : normal N

      g : ↥N
      h : G
      h1' : h ∈ H
      k := (g : G) * h * g⁻¹ * h⁻¹ : G

      Et trois conséquences concernant k  :
      * h2
      * h3
      * commutator_mem nN g h h1' :

      On veut :
      * Prouver k ∈ N
      *



       -/

/-
subtype.coe_mk : ∀ (a : ?M_1) (h : ?M_2 a), ↑⟨a, h⟩ = a
set_like.coe_mk : ∀ (x : ?M_2) (hx : x ∈ ?M_4), ↑⟨x, hx⟩ = x

set_like.mem_coe : ?M_5 ∈ ↑?M_4 ↔ ?M_5 ∈ ?M_4
set_like.coe_mem : ∀ (x : ↥?M_4), ↑x ∈ ?M_4

set_like.eta : ∀ (x : ↥?M_4) (hx : ↑x ∈ ?M_4), ⟨↑x, hx⟩ = x
-/

  sorry,

  end


/-
  Cas 1 : l = [c], donc c = g, c.support.card ≥ 4, donc ≥ 5 (parité)
    c = (a,b,c,d,e…)
    h = (a,b,e)
    g • a = b,
    g • b = c ≠ h • b

  Cas 2 : ∃ c ∈ l, c.support.card ≥ 3
    l ≠ [c], donc il existe aussi c' ≠ c, c' ∈ l
    cela donne trois éléments [a,b,c] dans c, deux éléments [d,e] dans c'
    h = (a,b,d) (3-cycle)
    g • a = b,
    g • b = c ≠ d = h • b,

  Cas 3 : ∀  c ∈ l, c.support.card ≤ 2
    l = [c, c',…] , c = (a,b), c' = (c, d) et on choisit e
    h = (a,b,e)
    g • a = b,
    g • b = a ≠ e = h • b

  g' = h * g * h⁻¹

  CLAIM : g' ∈ N (N distingué)

  CLAIM : g' ≠ g
    g' • b = h g h⁻¹ • b = h g • a = h • b ≠ g • b ?

  CLAIM : card supp(g' g⁻¹) ≤ 5
    * supp(g' g⁻¹) ⊆ g • supp(h) ∪ supp(h)
    -- car  y = g • x ∈ supp(g' g⁻¹) ↔ y ≠ g' g⁻¹ y ↔ g • x ≠ g' • x

    * g • supp(h) ∪ supp(h) = {ga, gb, gx} ∪ {a,b,x}
      ⊆ {b, (c [Cas 1 et 2] ou a [Cas 3]), gx, a, x}  avec x = d ou e

    * donc ≤ 5

  CLAIM : card supp (g' g⁻¹) < card supp(g)
    * Cas 1 : oui si [c] de longueur ≥ 6 (donc 7)
            quid si c de longueur 5 ?
              c = [a,b,c,d,e]
              h = (a b e)
              g' = h conj (a b c d e) = (b e c d a)
              g' g⁻¹ = (a c e), gagné !
            g {a,b,e} ∪ {a,b,e} = {a,b,e} cardinal 3 !

    * Cas 2 : oui car forcément [3, ≥ 3,…] ou [3,2,2,…]
    * Cas 3 : oui car on gagne a : {b,a,gx,x} ≤ 4
              si type [2,2], alors gx = x, et {b,a,x} < 3
              sinon : type [2,2,2,2,…] et 4 ≤ 8


  -- supp(h)={c,d,e}
  -- g⁻¹ supp(h) = {g⁻¹c, g⁻¹d, g⁻¹e} = {?, c, ?}
  -- donc card(supp(g')) ≤ 5

  -- Cas 1 : {c,d,e} ∪ {?,c,d} = {c,d,e,?} donc ≤ 4
  -- Cas 2 : {c,d,e} ∪ {b,?,d} = {b,c,d,e,?}, donc ≤ 5
  -- Cas 3 : {c,d,e} ∪ {c,d,?} = {c,d,e,?}

  -- Le mauvais cas est 2 :



-/


lemma has_three_cycle_normal (h5 : 5 ≤ fintype.card α)
  (N : subgroup (alternating_group α)) (nN : N.normal) (g : N)
  (hg : g ≠ 1) :
  ∃ (f : N), is_three_cycle (f : perm α) :=
begin
  apply has_three_cycle_normal_rec h5 N nN  (support (g : perm α)).card g rfl,
  apply equiv.perm.two_le_card_support_of_ne_one,
  intro hg',
  apply hg,
  apply set_like.coe_eq_coe.mp,
  rw subgroup.coe_one,
  apply set_like.coe_eq_coe.mp,
  rw ← coe_coe,
  rw subgroup.coe_one,
  exact hg'
end



example (n : ℕ) (h0 : n >0) (h1 : n<2) : n = 1 :=
begin
sorry,
end

    /-
    type_check  equiv.perm.cycle_of_mem_cycle_factors_finset_iff,
    ?m_4.cycle_of ?m_5 ∈ ?m_4.cycle_factors_finset ↔ ?m_5 ∈ ?m_4.support

    -/

    /-
    type_check cycle_factors_finset_pairwise_disjoint,
    ∀ (f p : perm ?m_1),
      p ∈ f.cycle_factors_finset → ∀ (q : perm ?m_1), q ∈ f.cycle_factors_finset → p ≠ q → p.disjoint q
    -/


  /-   theorem finset.card_bUnion {β : Type u} {α : Type v}
  [decidable_eq β] {s : finset α} {t : α → finset β}
  (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → x ≠ y → disjoint (t x) (t y)) :
    (s.bUnion t).card = ∑ (u : α) in s, (t u).card -/

    --




theorem eq_bot_or_eq_top_of_normal (h5 : 5 ≤ fintype.card α)
  (N : subgroup (alternating_group α)) (nN : N.normal) (ntN : nontrivial N) :
  N = ⊤ :=
begin
  obtain ⟨g, hgN : g ∈ N, g1 : g ≠ 1⟩ := (nontrivial_iff_exists_ne_one N).mp ntN,
  have hg : (support (g : perm α)).card ≥ 1,
  { apply nat.succ_le_iff.mpr,
    apply finset.card_pos.mpr ,
    by_contradiction,
    simp only [finset.not_nonempty_iff_eq_empty, perm.support_eq_empty_iff] at h,
    apply g1,
    apply set_like.coe_eq_coe.mp,
    rw h, rw subgroup.coe_one, },
  obtain ⟨f, hf⟩ := has_three_cycle_normal h5 N nN (⟨g, hgN⟩ : ↥N) hg,

  apply top_unique,
  rw ← is_three_cycle.alternating_normal_closure h5 hf,
  apply normal_closure_le_normal,
  simp only [set_like.eta, set_like.coe_mem, set_like.mem_coe, set.singleton_subset_iff, coe_coe]
end

theorem is_simple
  (hα : 5 ≤ fintype.card α) : is_simple_group (alternating_group α) :=
{exists_pair_ne :=
begin
  apply (alternating_group.nontrivial_of_three_le_card _).exists_pair_ne,
  apply le_trans _ hα,
  simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
end,
  eq_bot_or_eq_top_of_normal := λ N nN,
begin
  sorry,
end}



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
