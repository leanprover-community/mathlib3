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
-- open_locale big_operators

lemma cycle_mk (a b c : α) (g : perm α)
  (h12 : a ≠ b) (h13 : a ≠ c) (h23 : b ≠ c) :
  ∃ (h : perm α), is_three_cycle h ∧
    (h a = b) ∧ (h b = c) ∧ (h c = a) :=
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

    { rw cycle.form_perm_apply_mem_eq_next cl l_nodup c _,
      swap,
      change c ∈ l,
      simp only [list.mem_cons_iff, eq_self_iff_true, or_true, list.mem_singleton, apply_eq_iff_eq],
      change l.next c _ = a,
      rw  list.next_last_cons ,
        apply h13.symm,
        simp only [list.last],
        apply (list.nodup_cons.mp l_nodup).right,  },

end
