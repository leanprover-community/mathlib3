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


#check equiv.perm.sum_cycle_type
-- essentiellement : equiv.perm.sum_cycle_type
/-
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
-/

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

example (s : finset α) (g : perm α) : (g • s).card = s.card :=
begin
  apply finset.card_image_of_injective,
  apply mul_action.injective g,
end


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


lemma case_cycle5 (g : perm α) (hg : g.is_cycle) (hg' : order_of g ≥ 5) :
  ∃ (h : perm α), (is_three_cycle h) ∧
    (g * h * g⁻¹ * h⁻¹) ≠ 1 ∧ (g * h * g⁻¹ * h⁻¹).support.card < g.support.card :=
begin
    obtain ⟨n : ℕ, hg'' : order_of g = 5 + n⟩ :=
      nat.exists_eq_add_of_le hg', rw add_comm at hg'',
    obtain ⟨a, ha⟩ := id hg,  -- trick to not destruct hg

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

    obtain ⟨h, h_is_three_cycle, ha_eq_b, hb_eq_c, hc_eq_a, hsup⟩ :=
      three_cycle_mk h12 h13 h23,

    have hb_neq_c : g (g a) ≠ (g ^ (n+4)) a,
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
        rw ha_eq_b, rw hb_eq_c, exact hb_neq_c, },
      apply this,
      rw hz' },

    { -- son support est de cardinal < celui de g
      refine nat.lt_of_le_of_lt (finset.card_le_of_subset (commutator_support_le g h)) _,
      refine nat.lt_of_add_lt_add_right _,
      swap, -- exact (h.support ∩ g • h.support).card,
      rw finset.card_union_add_card_inter,

      have : (g • h.support).card = h.support.card,
      { apply finset.card_image_of_injective,  exact mul_action.injective g, },
      rw this,

      rw equiv.perm.is_three_cycle.card_support h_is_three_cycle,

      suffices : 2 ≤ (h.support ∩ g • h.support).card,
      { apply nat.lt_of_lt_of_le _ le_rfl,
        apply le_trans _ (nat.add_le_add (nat.lt_of_le_of_lt (le_add_self) hn) this),
        dec_trivial },

      have gc_eq_a : g ((g ^ (n+4)) a) = a,
      { suffices : (g ^ (n+5)) a = a,
          conv_rhs { rw ← this,  }, refl,
        rw [← hg'', pow_order_of_eq_one g, perm.coe_one, id.def], } ,

      -- h.suport = [a, g a, (g ^ (n+4)) a]
      -- g • h.support = [g a, (g ^ 2) a, g ^ (n+5) a] = [g a, a]
      have ha : a ∈ h.support ∩ g • h.support,
      { rw finset.mem_inter, split,
        rw equiv.perm.mem_support, rw ha_eq_b, exact h12.symm,

        change a ∈ finset.image (λ x, g • x) h.support,
        rw finset.mem_image,
        use ((g ^ (n+4)) a),

        split,
        { rw equiv.perm.mem_support,
          rw hc_eq_a, exact h13, },
        exact gc_eq_a,  },

      have hga : g a ∈ h.support ∩ g • h.support,
      { rw finset.mem_inter, split,

        { rw equiv.perm.mem_support,
          rw hb_eq_c, exact h23.symm },

        change g a ∈ finset.image (λ x, g x) h.support,
        rw finset.mem_image,
        use a,
        split,
          rw equiv.perm.mem_support,
          rw ha_eq_b, exact h12.symm,
          refl, },

      suffices : ({a,g a} : finset α).card = 2,
        { rw ← this, apply finset.card_le_of_subset,
          rw finset.insert_subset,
          exact ⟨ha, finset.singleton_subset_iff.mpr hga⟩ },
        rw finset.card_insert_of_not_mem,
        rw finset.card_singleton,
        rw finset.mem_singleton,
        exact h12 }
end

lemma case_cycle5' (g : perm α) (a : α) (hg' : (g.cycle_of a).support.card ≥ 5) :
  ∃ (h : perm α), (is_three_cycle h) ∧
    (g * h * g⁻¹ * h⁻¹) ≠ 1 ∧ (g * h * g⁻¹ * h⁻¹).support.card < g.support.card :=
begin
    let g' := g.cycle_of a,
    have ha : g a ≠ a,
    { rw ← equiv.perm.card_support_cycle_of_pos_iff ,
      apply lt_of_lt_of_le _ hg', dec_trivial, },

    obtain ⟨n : ℕ, hg'' : g'.support.card = 5 + n⟩ :=
      nat.exists_eq_add_of_le hg', rw add_comm at hg'',
--     obtain ⟨a, ha⟩ := id hg',  -- trick to not destruct hg

    let l := [a, g a, (g ^ (n+4)) a], -- a b e

    have hn' : n + 4 < g'.support.card,
      { -- refine nat.lt_of_lt_of_le _
        --   (finset.card_le_of_subset (equiv.perm.support_cycle_of_le g a)),
        rw hg'',
        simp only [nat.bit0_lt_bit1_iff, add_lt_add_iff_left], },

    have l_notnil : l ≠ list.nil,
    { suffices : l.length ≠ list.nil.length,
        intro z, apply this, rw z, dec_trivial },

    have h12 : a ≠ g a := ha.symm,
    have h13 : a ≠ (g ^ (n+4)) a,
    { refine nodup_powers_of_cycle_of 0 (n+4) _ hn', dec_trivial, },
    have h23 : g a ≠ (g ^ (n+4)) a,
    { refine nodup_powers_of_cycle_of 1 (n+4) _ hn', dec_trivial, },
    have l_nodup : l.nodup := by simp [h12, h13, h23],

    obtain ⟨h, h_is_three_cycle, ha_eq_b, hb_eq_c, hc_eq_a, hsup⟩ :=
      three_cycle_mk h12 h13 h23,

    have hb_neq_c : g (g a) ≠ (g ^ (n+4)) a,
    { refine nodup_powers_of_cycle_of 2 (n+4) _ hn', dec_trivial, },

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
        rw ha_eq_b, rw hb_eq_c, exact hb_neq_c, },
      apply this,
      rw hz' },

    { -- son support est de cardinal < celui de g
      refine nat.lt_of_le_of_lt (finset.card_le_of_subset (commutator_support_le g h)) _,
      refine nat.lt_of_add_lt_add_right _,
      swap, -- exact (h.support ∩ g • h.support).card,
      rw finset.card_union_add_card_inter,

      have : (g • h.support).card = h.support.card,
      { apply finset.card_image_of_injective,  exact mul_action.injective g, },
      rw this,

      rw equiv.perm.is_three_cycle.card_support h_is_three_cycle,

      suffices hs2 : 2 ≤ (h.support ∩ g • h.support).card,
      { apply nat.lt_of_lt_of_le _ le_rfl,
        have hg : 5 ≤ g.support.card :=
          le_trans hg' (finset.card_le_of_subset (equiv.perm.support_cycle_of_le g a)),
        refine le_trans _ (nat.add_le_add hg hs2),
        dec_trivial, },

      have gc_eq_a : g ((g ^ (n+4)) a) = a,
      { suffices : (g ^ (n+5)) a = a,
          conv_rhs { rw ← this,  }, refl,
        rw [← equiv.perm.pow_mod_card_support_cycle_of_self_apply, hg'',
          nat.mod_self, pow_zero, perm.coe_one, id.def] } ,

      -- h.suport = [a, g a, (g ^ (n+4)) a]
      -- g • h.support = [g a, (g ^ 2) a, g ^ (n+5) a] = [g a, a]
      have ha : a ∈ h.support ∩ g • h.support,
      { rw finset.mem_inter, split,
        rw equiv.perm.mem_support, rw ha_eq_b, exact h12.symm,

        change a ∈ finset.image (λ x, g • x) h.support,
        rw finset.mem_image,
        use ((g ^ (n+4)) a),

        split,
        { rw equiv.perm.mem_support,
          rw hc_eq_a, exact h13, },
        exact gc_eq_a,  },

      have hga : g a ∈ h.support ∩ g • h.support,
      { rw finset.mem_inter, split,

        { rw equiv.perm.mem_support,
          rw hb_eq_c, exact h23.symm },

        change g a ∈ finset.image (λ x, g x) h.support,
        rw finset.mem_image,
        use a,
        split,
          rw equiv.perm.mem_support,
          rw ha_eq_b, exact h12.symm,
          refl, },

      suffices : ({a,g a} : finset α).card = 2,
        { rw ← this, apply finset.card_le_of_subset,
          rw finset.insert_subset,
          exact ⟨ha, finset.singleton_subset_iff.mpr hga⟩ },
        rw finset.card_insert_of_not_mem,
        rw finset.card_singleton,
        rw finset.mem_singleton,
        exact h12 }
end

lemma case_cycle' (g : perm α) (a : α) (ha : a ≠ g a)
  (x : α) (hx : a ≠ x) (hx' : g a ≠ x) (hc'' : g (g a) ≠ x) :
  ∃ (h : perm α),
    (is_three_cycle h) ∧
    (g * h * g⁻¹ * h⁻¹) ≠ 1 ∧
    (support (g * h * g⁻¹ * h⁻¹)) ⊆ {a,g a, (g ^ 2) a, x, g x} :=
begin
    let g' := g.cycle_of a,
/-     have ha : g a ≠ a,
    { rw ← equiv.perm.card_support_cycle_of_pos_iff ,
      apply lt_of_lt_of_le _ hg', dec_trivial, }, -/

    let l := [a, g a, x],
    have l_notnil : l ≠ list.nil, by dec_trivial,
    have l_nodup : l.nodup := by simp [ha, hx, hx'],
    obtain ⟨h, h_is_three_cycle, ha_eq_b, hb_eq_c, hc_eq_a, hsup⟩ :=
      three_cycle_mk ha hx hx',

    have hb_neq_c : g (g a) ≠ x := hc'',
  --   { refine nodup_powers_of_cycle_of 2 (n+4) _ hn', dec_trivial, },

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
        rw ha_eq_b, rw hb_eq_c, exact hb_neq_c, },
      apply this,
      rw hz' },

    apply finset.subset.trans (commutator_support_le g h),
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


/-
    g = (a,b,c,d,…,e)
    h = (a,b,e)
    g • a = b,
    g • b = c ≠ h • b -/


/-
Cas 2 : ∃ c ∈ l, c.support.card ≥ 3
    l ≠ [c], donc il existe aussi c' ≠ c, c' ∈ l
    cela donne trois éléments [a,b,c] dans c, deux éléments [d,e] dans c'
    h = (a,b,d) (3-cycle)
    g • a = b,
    g • b = c ≠ d = h • b,
-/

lemma case_cycle3' (g : perm α)  :
  ∃ (h : perm α), (is_three_cycle h) ∧
    (g * h * g⁻¹ * h⁻¹) ≠ 1 ∧ (g * h * g⁻¹ * h⁻¹).support.card < g.support.card :=
begin
  sorry
end

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


lemma has_three_cycle_normal_rec'' (h5 : 5 ≤ fintype.card α)
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

 --  obtain ⟨h, h1, h2, h3⟩ := ww _ _ _ _,
  -- On conclut !
  /- Useless coercions

  let h' : alternating_group α := ⟨h,is_three_cycle.mem_alternating_group h1⟩,
  let h'_coe_h := set_like.coe_mk h (is_three_cycle.mem_alternating_group h1),

  have : (g : perm α) * h * g⁻¹ * h⁻¹ = (g : alternating_group α) * h' * g⁻¹ * h'⁻¹,
    { rw ← h'_coe_h,
      simp only [coe_inv, subgroup.coe_mul, mul_left_inj],
      exact coe_coe g },
  -- rw this at h2 h3,  -/

--   let cm := commutator_mem' nN g h',

/- Plusieurs cas  pour {a, g a, g (g a), x, g x}
  * n ≥ 6 : on prend x ≠ a, g a et on majore par 5
  * n = 5 et ct.sup ≥ 4, on prend x = g⁻¹ a et on majore par 4
  * n = 5 et ct.sup = 2, on prend pour x un point fixe et on majore par 3
  * n = 4 et ct.sup ≥ 4, impossible, car g serait un 4-cycle, donc impair
  * n = 3 : g est un 3-cycle

  * n ≥ 6
  * n ≤ 5, ct.sup ≥ 4
  * n ≤ 5, ct.sup = 2
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
      refine (nodup_powers_of_cycle_of 0 2 _ _) hgx.symm,
      dec_trivial,
      rw h_of_a, refine lt_of_lt_of_le _ Hct5, dec_trivial },
    have hx'' : (g : perm α) ((g : perm α) a) ≠ x,
    { intro h,
      simp only [← h, ← equiv.perm.mul_apply, ← mul_assoc] at hgx,
      rw [ ← pow_one (g : perm α)] at hgx,
      simp only [← pow_add] at hgx,
      refine (nodup_powers_of_cycle_of 0 3 _ _) hgx.symm,
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



example (g : perm α) (a : α): g (g a) = (g ^ 2) a :=
begin

end

example (g : perm α) (a : α): g (g⁻¹ a) = a :=
begin
  exact perm.eq_inv_iff_eq.mp rfl
end

example (s : finset α) (a b : α) (h : a ∈ s) (h' : b ∉ s) : a ≠ b :=
begin
  intro hab,
  rw hab at h, exact h' h,
end

example (s t : finset α) (hst : disjoint s t) (a : α) (ha : a ∈ s) : a ∉ t :=
finset.disjoint_left.mp hst ha

lemma testlemma {a : α} {s : finset α} {n : ℕ} (h : s.card ≤ n) :
  (insert a s).card ≤ n.succ :=
begin
  apply le_trans (finset.card_insert_le a s),
  exact nat.add_le_add_right h 1,
end

example : ({(1 : fin 1000), 3, 9, 12} :finset (fin 1000)).card ≤ 4 :=
begin
  let r :=
     λ (n : ℕ) (a : fin 1000) s (h : finset.card s ≤ n),
    le_trans (finset.card_insert_le a s) (nat.add_le_add_right h 1),

--   iterate { apply r, },

    iterate { apply le_trans (finset.card_insert_le _ _), apply nat.add_le_add_right _ 1},
    rw finset.card_singleton,
end

#exit


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
    rw ← equiv.perm.mem_alternating_group_of_cycle_iff
      (equiv.perm.card_support_eq_two.mp hgs).is_cycle,
    apply set_like.coe_mem,
    rw hgs, exact even_bit0 1 },

  -- have : hn' : 3 ≤ n
  intros g hg hgs,
  let l := (cycle_factors_finset (g : perm α)),

  cases (nat.lt_or_ge n 4) with hn hn,
  -- n = 3, g is a 3-cycle
  { rw (nat.eq_of_le_of_lt_succ hn' hn) at hgs, -- n.succ = 3
    rw card_support_eq_three_iff at hgs,  -- ↑g is a 3-cycle
    use g, exact hgs,  },


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

  -- n ≥ 5, car ≥ 4 et impair
    cases nat.lt_or_ge n 5 with hn' hn',
    { let hn4 := nat.eq_of_le_of_lt_succ hn hn',
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

  h = (a, b, x),  a ∈ g.support, b = g a (donc a ≠ b),  x ≠ a, g a,
  Hypothèses à assurer :
    x ≠ g b

  g' = h g h⁻¹

  *Claim :* g' • x ≠ g : car g' • b = h g h⁻¹ b = h g a = h b = x ≠ g b

  supp (g' g⁻¹) ⊆ g • supp(h) ∪ supp(h) = {g a, g b, g x} ∪ {a, b, x}

  *Claim :* On gagne b, supp(g' g⁻¹) ⊆ {a, b, g b, x, g x} car g a = b

  g.support.card ≥ 5
  Si g a un cycle de longueur ≥ 4, prendre a dedans, x = g⁻¹ a
  On trouve supp(g' g⁻¹) ⊆ {a, b, g b, x}

  Sinon, g.support.card ≥ 6
   * il y a au moins 2 cycles
   * (3,2) est impair ; (2,2) est de support 4.

  tous les cycles de g sont de longueur ≤ 3.
  Nécessairement, g.support.card ≥ 6 et g a au moins 2 cycles

  Prendre a dans un cycle, et x dans un autre.


-/


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
