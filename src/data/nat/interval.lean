/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.interval

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Add all the `finset.Ico` stuff.
-/

open finset nat

instance : locally_finite_order ℕ :=
{ finset_Icc := λ a b, (list.range' a (b + 1 - a)).to_finset,
  finset_Ico := λ a b, (list.range' a (b - a)).to_finset,
  finset_Ioc := λ a b, (list.range' (a + 1) (b - a)).to_finset,
  finset_Ioo := λ a b, (list.range' (a + 1) (b - a - 1)).to_finset,
  finset_mem_Icc := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range'],
    cases le_or_lt a b,
    { rw [nat.add_sub_cancel' (nat.lt_succ_of_le h).le, nat.lt_succ_iff] },
    { rw [nat.sub_eq_zero_iff_le.2 h, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)) }
  end,
  finset_mem_Ico := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range'],
    cases le_or_lt a b,
    { rw [nat.add_sub_cancel' h] },
    { rw [nat.sub_eq_zero_iff_le.2 h.le, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2.le)) }
  end,
  finset_mem_Ioc := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range'],
    cases le_or_lt a b,
    { rw [←succ_sub_succ, nat.add_sub_cancel' (succ_le_succ h), nat.lt_succ_iff, nat.succ_le_iff] },
    { rw [nat.sub_eq_zero_iff_le.2 h.le, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.le.trans hx.2)) }
  end,
  finset_mem_Ioo := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range', nat.sub_sub],
    cases le_or_lt (a + 1) b,
    { rw [nat.add_sub_cancel' h, nat.succ_le_iff] },
    { rw [nat.sub_eq_zero_iff_le.2 h.le, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)) }
  end }

namespace nat
variables (a b c : ℕ)

lemma Icc_eq_range' : Icc a b = (list.range' a (b + 1 - a)).to_finset := rfl
lemma Ioc_eq_range' : Ioc a b = (list.range' (a + 1) (b - a)).to_finset := rfl
lemma Ioo_eq_range' : Ioo a b = (list.range' (a + 1) (b - a - 1)).to_finset := rfl

@[simp] lemma card_Icc : (Icc a b).card = b + 1 - a :=
by rw [Icc_eq_range', list.card_to_finset, (list.nodup_range' _ _).erase_dup, list.length_range']

@[simp] lemma card_Ioc : (Ioc a b).card = b - a :=
by rw [Ioc_eq_range', list.card_to_finset, (list.nodup_range' _ _).erase_dup, list.length_range']

@[simp] lemma card_Ioo : (Ioo a b).card = b - a - 1 :=
by rw [Ioo_eq_range', list.card_to_finset, (list.nodup_range' _ _).erase_dup, list.length_range']

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = b + 1 - a :=
by rw [←card_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = b - a :=
by rw [←card_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = b - a - 1 :=
by rw [←card_Ioo, fintype.card_of_finset]

-- TODO@Yaël: Generalize all the following lemmas to `succ_order`

lemma Icc_succ_left : Icc a.succ b = Ioc a b :=
by { ext x, rw [mem_Icc, mem_Ioc, succ_le_iff] }

end nat
