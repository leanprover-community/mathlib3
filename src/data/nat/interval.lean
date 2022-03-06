/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `ordered_group`, `canonically_ordered_monoid` or `succ_order`
and subsequently be moved upstream to `data.finset.locally_finite`.
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

variables (a b c : ℕ)

namespace nat

lemma Icc_eq_range' : Icc a b = (list.range' a (b + 1 - a)).to_finset := rfl
lemma Ico_eq_range' : Ico a b = (list.range' a (b - a)).to_finset := rfl
lemma Ioc_eq_range' : Ioc a b = (list.range' (a + 1) (b - a)).to_finset := rfl
lemma Ioo_eq_range' : Ioo a b = (list.range' (a + 1) (b - a - 1)).to_finset := rfl

lemma Iio_eq_range : Iio = range := by { ext b x, rw [mem_Iio, mem_range] }

@[simp] lemma Ico_zero_eq_range : Ico 0 = range := by rw [←bot_eq_zero, ←Iio_eq_Ico, Iio_eq_range]

lemma _root_.finset.range_eq_Ico : range = Ico 0 := Ico_zero_eq_range.symm

@[simp] lemma card_Icc : (Icc a b).card = b + 1 - a :=
by rw [Icc_eq_range', list.card_to_finset, (list.nodup_range' _ _).dedup, list.length_range']

@[simp] lemma card_Ico : (Ico a b).card = b - a :=
by rw [Ico_eq_range', list.card_to_finset, (list.nodup_range' _ _).dedup, list.length_range']

@[simp] lemma card_Ioc : (Ioc a b).card = b - a :=
by rw [Ioc_eq_range', list.card_to_finset, (list.nodup_range' _ _).dedup, list.length_range']

@[simp] lemma card_Ioo : (Ioo a b).card = b - a - 1 :=
by rw [Ioo_eq_range', list.card_to_finset, (list.nodup_range' _ _).dedup, list.length_range']

@[simp] lemma card_Iic : (Iic b).card = b + 1 := by rw [Iic, card_Icc, bot_eq_zero, tsub_zero]
@[simp] lemma card_Iio : (Iio b).card = b := by rw [Iio, card_Ico, bot_eq_zero, tsub_zero]

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = b + 1 - a :=
by rw [fintype.card_of_finset, card_Icc]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = b - a :=
by rw [fintype.card_of_finset, card_Ico]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = b - a :=
by rw [fintype.card_of_finset, card_Ioc]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = b - a - 1 :=
by rw [fintype.card_of_finset, card_Ioo]

@[simp] lemma card_fintype_Iic : fintype.card (set.Iic b) = b + 1 :=
by rw [fintype.card_of_finset, card_Iic]

@[simp] lemma card_fintype_Iio : fintype.card (set.Iio b) = b :=
by rw [fintype.card_of_finset, card_Iio]

-- TODO@Yaël: Generalize all the following lemmas to `succ_order`

lemma Icc_succ_left : Icc a.succ b = Ioc a b := by { ext x, rw [mem_Icc, mem_Ioc, succ_le_iff] }

lemma Ico_succ_right : Ico a b.succ = Icc a b := by { ext x, rw [mem_Ico, mem_Icc, lt_succ_iff] }

lemma Ico_succ_left : Ico a.succ b = Ioo a b := by { ext x, rw [mem_Ico, mem_Ioo, succ_le_iff] }

lemma Icc_pred_right {b : ℕ} (h : 0 < b) : Icc a (b - 1) = Ico a b :=
by { ext x, rw [mem_Icc, mem_Ico, lt_iff_le_pred h] }

lemma Ico_succ_succ : Ico a.succ b.succ = Ioc a b :=
by { ext x, rw [mem_Ico, mem_Ioc, succ_le_iff, lt_succ_iff] }

@[simp] lemma Ico_succ_singleton : Ico a (a + 1) = {a} := by rw [Ico_succ_right, Icc_self]

@[simp] lemma Ico_pred_singleton {a : ℕ} (h : 0 < a) : Ico (a - 1) a = {a - 1} :=
by rw [←Icc_pred_right _ h, Icc_self]

variables {a b c}

lemma Ico_succ_right_eq_insert_Ico (h : a ≤ b) : Ico a (b + 1) = insert b (Ico a b) :=
by rw [Ico_succ_right, ←Ico_insert_right h]

lemma Ico_insert_succ_left (h : a < b) : insert a (Ico a.succ b) = Ico a b :=
by rw [Ico_succ_left, ←Ioo_insert_left h]

lemma image_sub_const_Ico (h : c ≤ a) : (Ico a b).image (λ x, x - c) = Ico (a - c) (b - c) :=
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

lemma Ico_succ_left_eq_erase_Ico : Ico a.succ b = erase (Ico a b) a :=
begin
  ext x,
  rw [Ico_succ_left, mem_erase, mem_Ico, mem_Ioo, ←and_assoc, ne_comm, and_comm (a ≠ x),
    lt_iff_le_and_ne],
end

lemma mod_inj_on_Ico (n a : ℕ) : set.inj_on (% a) (finset.Ico n (n+a)) :=
begin
  induction n with n ih,
  { simp only [zero_add, nat_zero_eq_zero, Ico_zero_eq_range],
    rintro k hk l hl (hkl : k % a = l % a),
    simp only [finset.mem_range, finset.mem_coe] at hk hl,
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl, },
  rw [Ico_succ_left_eq_erase_Ico, succ_add, Ico_succ_right_eq_insert_Ico le_self_add],
  rintro k hk l hl (hkl : k % a = l % a),
  have ha : 0 < a,
  { by_contra ha, simp only [not_lt, nonpos_iff_eq_zero] at ha, simpa [ha] using hk },
  simp only [finset.mem_coe, finset.mem_insert, finset.mem_erase] at hk hl,
  rcases hk with ⟨hkn, (rfl|hk)⟩; rcases hl with ⟨hln, (rfl|hl)⟩,
  { refl },
  { rw add_mod_right at hkl,
    refine (hln $ ih hl _ hkl.symm).elim,
    simp only [lt_add_iff_pos_right, set.left_mem_Ico, finset.coe_Ico, ha], },
  { rw add_mod_right at hkl,
    suffices : k = n, { contradiction },
    refine ih hk _ hkl,
    simp only [lt_add_iff_pos_right, set.left_mem_Ico, finset.coe_Ico, ha], },
  { refine ih _ _ hkl; simp only [finset.mem_coe, hk, hl], },
end

/-- Note that while this lemma cannot be easily generalized to a type class, it holds for ℤ as
well. See `int.image_Ico_mod` for the ℤ version. -/
lemma image_Ico_mod (n a : ℕ) :
  (Ico n (n+a)).image (% a) = range a :=
begin
  obtain rfl | ha := eq_or_ne a 0,
  { rw [range_zero, add_zero, Ico_self, image_empty], },
  ext i,
  simp only [mem_image, exists_prop, mem_range, mem_Ico],
  split,
  { rintro ⟨i, h, rfl⟩, exact mod_lt i ha.bot_lt },
  intro hia,
  have hn := nat.mod_add_div n a,
  obtain hi | hi := lt_or_le i (n % a),
  { refine ⟨i + a * (n/a + 1), ⟨_, _⟩, _⟩,
    { rw [add_comm (n/a), mul_add, mul_one, ← add_assoc],
      refine hn.symm.le.trans (add_le_add_right _ _),
      simpa only [zero_add] using add_le_add (zero_le i) (nat.mod_lt n ha.bot_lt).le, },
    { refine lt_of_lt_of_le (add_lt_add_right hi (a * (n/a + 1))) _,
      rw [mul_add, mul_one, ← add_assoc, hn], },
    { rw [nat.add_mul_mod_self_left, nat.mod_eq_of_lt hia], } },
  { refine ⟨i + a * (n/a), ⟨_, _⟩, _⟩,
    { exact hn.symm.le.trans (add_le_add_right hi _), },
    { rw [add_comm n a],
      refine add_lt_add_of_lt_of_le hia (le_trans _ hn.le),
      simp only [zero_le, le_add_iff_nonneg_left], },
    { rw [nat.add_mul_mod_self_left, nat.mod_eq_of_lt hia], } },
end

section multiset
open multiset

lemma multiset_Ico_map_mod (n a : ℕ) : (multiset.Ico n (n+a)).map (% a) = range a :=
begin
  convert congr_arg finset.val (image_Ico_mod n a),
  refine ((nodup_map_iff_inj_on (finset.Ico _ _).nodup).2 $ _).dedup.symm,
  exact mod_inj_on_Ico _ _,
end

end multiset

end nat

namespace finset

lemma range_image_pred_top_sub (n : ℕ) : (finset.range n).image (λ j, n - 1 - j) = finset.range n :=
begin
  cases n,
  { rw [range_zero, image_empty] },
  { rw [finset.range_eq_Ico, nat.Ico_image_const_sub_eq_Ico (zero_le _)],
    simp_rw [succ_sub_succ, tsub_zero, tsub_self] }
end

lemma range_add_eq_union : range (a + b) = range a ∪ (range b).map (add_left_embedding a) :=
begin
  rw [finset.range_eq_Ico, map_eq_image],
  convert (Ico_union_Ico_eq_Ico a.zero_le le_self_add).symm,
  exact image_add_left_Ico _ _ _,
end

end finset
