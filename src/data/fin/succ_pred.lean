/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import order.succ_pred.basic

/-!
# Successors and predecessors of `fin n`

In this file, we show that `fin n` is both a `succ_order` and a `pred_order`. Note that they are
also archimidean, but this is derived from the general instance for well-orderings as opposed
to a specific `fin` instance.

-/

namespace fin

instance : ∀ {n : ℕ}, succ_order (fin n)
| 0 := by constructor; exact elim0
| (n+1) :=
{ succ := λ i, if i < fin.last n then i + 1 else i,
  le_succ := λ a,
  begin
    cases n,
    { exact (subsingleton.elim _ _).le },
    split_ifs,
    { rw [le_iff_coe_le_coe, coe_add_one_of_lt h],
      exact (a : ℕ).le_succ },
    { exact le_rfl }
   end,
  max_of_succ_le := λ a,
  begin
    split_ifs,
    { rw [le_iff_coe_le_coe, coe_add_one_of_lt h],
      intro h,
      cases (lt_add_one _).ne (antisymm (a : ℕ).le_succ h) },
    { rintro -,
      rw [eq_last_of_not_lt h],
      exact is_max_top }
  end,
  succ_le_of_lt := λ a b h', let h := h'.trans_le (le_last _) in
                             by rwa [if_pos h, le_iff_coe_le_coe, coe_add_one_of_lt h],
  le_of_lt_succ := λ a b h,
  begin
    split_ifs at h with hab,
    swap, { exact h.le },
    rw [lt_iff_coe_lt_coe, coe_add_one_of_lt hab] at h,
    exact nat.le_of_lt_succ h
  end }

@[simp] lemma succ_eq {n : ℕ} : succ_order.succ = λ a, if a < fin.last n then a + 1 else a := rfl
lemma succ_apply {n : ℕ} (a) : succ_order.succ a = if a < fin.last n then a + 1 else a := rfl

instance : ∀ {n : ℕ}, pred_order (fin n)
| 0 := by constructor; exact elim0
| (n+1) :=
{ pred := λ x, if x = 0 then 0 else x - 1,
  pred_le := λ a,
  begin
    split_ifs,
    { exact zero_le _ },
    rw [le_iff_coe_le_coe, coe_sub_one, if_neg h],
    exact tsub_le_self
  end,
  min_of_le_pred := λ a,
  begin
    split_ifs,
    { subst h,
      exact λ _, is_min_bot },
    intro ha,
    contrapose! ha,
    rw [lt_iff_coe_lt_coe, coe_sub_one, if_neg h],
    refine nat.sub_lt_of_pos_le _ _ nat.zero_lt_one (nat.one_le_iff_ne_zero.mpr _),
    rwa subtype.ext_iff at h,
  end,
  le_pred_of_lt := λ a b h',
  begin
    have h := (zero_le a).trans_lt h',
    rwa [if_neg h.ne', le_iff_coe_le_coe, coe_sub_one, if_neg h.ne', le_tsub_iff_left, add_comm],
    exact h,
  end,
  le_of_pred_lt := λ a b h',
  begin
    split_ifs at h' with h,
    { simp [h, zero_le] },
    rw [lt_iff_coe_lt_coe, coe_sub_one, if_neg h, tsub_lt_iff_left, add_comm 1] at h',
    { exact nat.le_of_lt_succ h' },
    apply nat.one_le_iff_ne_zero.mpr,
    rwa subtype.ext_iff at h
  end }

@[simp] lemma pred_eq {n} : pred_order.pred = λ a : fin (n + 1), if a = 0 then 0 else a - 1 := rfl
lemma pred_apply {n : ℕ} (a : fin (n + 1)) : pred_order.pred a = if a = 0 then 0 else a - 1 := rfl

end fin
