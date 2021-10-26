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

Some lemmas can be generalized using `ordered_group`, `canonically_ordered_monoid` or `succ_order`
and subsequently be moved upstream to `data.finset.interval`.
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
    { rw [add_tsub_cancel_of_le (nat.lt_succ_of_le h).le, nat.lt_succ_iff] },
    { rw [tsub_eq_zero_iff_le.2 (succ_le_of_lt h), add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)) }
  end,
  finset_mem_Ico := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range'],
    cases le_or_lt a b,
    { rw [add_tsub_cancel_of_le h] },
    { rw [tsub_eq_zero_iff_le.2 h.le, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2.le)) }
  end,
  finset_mem_Ioc := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range'],
    cases le_or_lt a b,
    { rw [←succ_sub_succ, add_tsub_cancel_of_le (succ_le_succ h), nat.lt_succ_iff,
        nat.succ_le_iff] },
    { rw [tsub_eq_zero_iff_le.2 h.le, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.le.trans hx.2)) }
  end,
  finset_mem_Ioo := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range', ← tsub_add_eq_tsub_tsub],
    cases le_or_lt (a + 1) b,
    { rw [add_tsub_cancel_of_le h, nat.succ_le_iff] },
    { rw [tsub_eq_zero_iff_le.2 h.le, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)) }
  end }

namespace nat
variables (a b c : ℕ)

lemma Icc_eq_range' : Icc a b = (list.range' a (b + 1 - a)).to_finset := rfl
lemma Ico_eq_range' : Ico a b = (list.range' a (b - a)).to_finset := rfl
lemma Ioc_eq_range' : Ioc a b = (list.range' (a + 1) (b - a)).to_finset := rfl
lemma Ioo_eq_range' : Ioo a b = (list.range' (a + 1) (b - a - 1)).to_finset := rfl

lemma Iio_eq_range : Iio = range :=
by { ext b x, rw [mem_Iio, mem_range] }

lemma Ico_zero_eq_range : Ico 0 a = range a :=
by rw [←bot_eq_zero, ←Iio_eq_Ico, Iio_eq_range]

lemma _root_.finset.range_eq_Ico : range = Ico 0 := by { funext, exact (Ico_zero_eq_range n).symm }

@[simp] lemma card_Icc : (Icc a b).card = b + 1 - a :=
by rw [Icc_eq_range', list.card_to_finset, (list.nodup_range' _ _).erase_dup, list.length_range']

@[simp] lemma card_Ico : (Ico a b).card = b - a :=
by rw [Ico_eq_range', list.card_to_finset, (list.nodup_range' _ _).erase_dup, list.length_range']

@[simp] lemma card_Ioc : (Ioc a b).card = b - a :=
by rw [Ioc_eq_range', list.card_to_finset, (list.nodup_range' _ _).erase_dup, list.length_range']

@[simp] lemma card_Ioo : (Ioo a b).card = b - a - 1 :=
by rw [Ioo_eq_range', list.card_to_finset, (list.nodup_range' _ _).erase_dup, list.length_range']

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = b + 1 - a :=
by rw [←card_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = b - a :=
by rw [←card_Ico, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = b - a :=
by rw [←card_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = b - a - 1 :=
by rw [←card_Ioo, fintype.card_of_finset]

-- TODO@Yaël: Generalize all the following lemmas to `succ_order`

lemma Icc_succ_left : Icc a.succ b = Ioc a b :=
by { ext x, rw [mem_Icc, mem_Ioc, succ_le_iff] }

lemma Ico_succ_right : Ico a b.succ = Icc a b :=
by { ext x, rw [mem_Ico, mem_Icc, lt_succ_iff] }

lemma Ico_succ_left : Ico a.succ b = Ioo a b :=
by { ext x, rw [mem_Ico, mem_Ioo, succ_le_iff] }

lemma Icc_pred_right {b : ℕ} (h : 0 < b) : Icc a (b - 1) = Ico a b :=
by { ext x, rw [mem_Icc, mem_Ico, lt_iff_le_pred h] }

lemma Ico_succ_succ : Ico a.succ b.succ = Ioc a b :=
by { ext x, rw [mem_Ico, mem_Ioc, succ_le_iff, lt_succ_iff] }

@[simp] lemma Ico_succ_singleton : Ico a (a + 1) = {a} :=
by rw [Ico_succ_right, Icc_self]

@[simp] lemma Ico_pred_singleton {a : ℕ} (h : 0 < a) : Ico (a - 1) a = {a - 1} :=
by rw [←Icc_pred_right _ h, Icc_self]

variables {a b c}

lemma Ico_succ_right_eq_insert_Ico (h : a ≤ b) : Ico a (b + 1) = insert b (Ico a b) :=
by rw [Ico_succ_right, ←Ico_insert_right h]

lemma Ico_insert_succ_left (h : a < b) : insert a (Ico a.succ b) = Ico a b :=
by rw [Ico_succ_left, ←Ioo_insert_left h]

lemma image_sub_const_Ico (h : c ≤ a) :
  (Ico a b).image (λ x, x - c) = Ico (a - c) (b - c) :=
begin
  ext x,
  rw mem_image,
  split,
  { rintro ⟨x, hx, rfl⟩,
    rw [mem_Ico] at ⊢ hx,
    exact ⟨tsub_le_tsub_right hx.1 _, tsub_lt_tsub_right_of_le (h.trans hx.1) hx.2⟩ },
  { rintro h,
    refine ⟨x + c, _, add_tsub_cancel_right _ _⟩,
    rw mem_Ico at ⊢ h,
    exact ⟨tsub_le_iff_right.1 h.1, lt_tsub_iff_right.1 h.2⟩ }
end

lemma Ico_image_const_sub_eq_Ico (hac : a ≤ c) :
  (Ico a b).image (λ x, c - x) = Ico (c + 1 - b) (c + 1 - a) :=
begin
  ext x,
  rw [mem_image, mem_Ico],
  split,
  { rintro ⟨x, hx, rfl⟩,
    rw mem_Ico at hx,
    refine ⟨_, ((tsub_le_tsub_iff_left hac).2 hx.1).trans_lt ((tsub_lt_tsub_iff_right hac).2
      (nat.lt_succ_self _))⟩,
    cases lt_or_le c b,
    { rw tsub_eq_zero_iff_le.mpr (succ_le_of_lt h),
      exact zero_le _ },
    { rw ←succ_sub_succ c,
      exact (tsub_le_tsub_iff_left (succ_le_succ $ hx.2.le.trans h)).2 hx.2 } },
  { rintro ⟨hb, ha⟩,
    rw [lt_tsub_iff_left, lt_succ_iff] at ha,
    have hx : x ≤ c := (nat.le_add_left _ _).trans ha,
    refine ⟨c - x, _, tsub_tsub_cancel_of_le hx⟩,
    { rw mem_Ico,
      exact ⟨le_tsub_of_add_le_right ha, (tsub_lt_iff_left hx).2 $ succ_le_iff.1 $
        tsub_le_iff_right.1 hb⟩ } }
end

lemma range_image_pred_top_sub (n : ℕ) :
  (finset.range n).image (λ j, n - 1 - j) = finset.range n :=
begin
  cases n,
  { rw [range_zero, image_empty] },
  { rw [finset.range_eq_Ico, Ico_image_const_sub_eq_Ico (zero_le _)],
    simp_rw [succ_sub_succ, tsub_zero, tsub_self] }
end

end nat
