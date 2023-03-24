/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.parity
import data.list.chain

/-!
# List of booleans

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove lemmas about the number of `ff`s and `tt`s in a list of booleans. First we
prove that the number of `ff`s plus the number of `tt` equals the length of the list. Then we prove
that in a list with alternating `tt`s and `ff`s, the number of `tt`s differs from the number of
`ff`s by at most one. We provide several versions of these statements.
-/

namespace list

@[simp]
theorem count_bnot_add_count (l : list bool) (b : bool) : count (!b) l + count b l = length l :=
by simp only [length_eq_countp_add_countp (eq (!b)), bool.bnot_not_eq, count]

@[simp]
theorem count_add_count_bnot (l : list bool) (b : bool) : count b l + count (!b) l = length l :=
by rw [add_comm, count_bnot_add_count]

@[simp] theorem count_ff_add_count_tt (l : list bool) : count ff l + count tt l = length l :=
count_bnot_add_count l tt

@[simp] theorem count_tt_add_count_ff (l : list bool) : count tt l + count ff l = length l :=
count_bnot_add_count l ff

lemma chain.count_bnot :
  ∀ {b : bool} {l : list bool}, chain (≠) b l → count (!b) l = count b l + length l % 2
| b [] h := rfl
| b (x :: l) h :=
  begin
    obtain rfl : b = !x := bool.eq_bnot_iff.2 (rel_of_chain_cons h),
    rw [bnot_bnot, count_cons_self, count_cons_of_ne x.bnot_ne_self,
      chain.count_bnot (chain_of_chain_cons h), length, add_assoc, nat.mod_two_add_succ_mod_two]
  end

namespace chain'

variables {l : list bool}

theorem count_bnot_eq_count (hl : chain' (≠) l) (h2 : even (length l)) (b : bool) :
  count (!b) l = count b l :=
begin
  cases l with x l, { refl },
  rw [length_cons, nat.even_add_one, nat.not_even_iff] at h2,
  suffices : count (!x) (x :: l) = count x (x :: l),
  { cases b; cases x; try { exact this }; exact this.symm },
  rw [count_cons_of_ne x.bnot_ne_self, hl.count_bnot, h2, count_cons_self]
end

theorem count_ff_eq_count_tt (hl : chain' (≠) l) (h2 : even (length l)) : count ff l = count tt l :=
hl.count_bnot_eq_count h2 tt

lemma count_bnot_le_count_add_one (hl : chain' (≠) l) (b : bool) :
  count (!b) l ≤ count b l + 1 :=
begin
  cases l with x l, { exact zero_le _ },
  obtain rfl | rfl : b = x ∨ b = !x, by simp only [bool.eq_bnot_iff, em],
  { rw [count_cons_of_ne b.bnot_ne_self, count_cons_self, hl.count_bnot, add_assoc],
    exact add_le_add_left (nat.mod_lt _ two_pos).le _ },
  { rw [bnot_bnot, count_cons_self, count_cons_of_ne x.bnot_ne_self, hl.count_bnot],
    exact add_le_add_right (le_add_right le_rfl) _ }
end

lemma count_ff_le_count_tt_add_one (hl : chain' (≠) l) : count ff l ≤ count tt l + 1 :=
hl.count_bnot_le_count_add_one tt

lemma count_tt_le_count_ff_add_one (hl : chain' (≠) l) : count tt l ≤ count ff l + 1 :=
hl.count_bnot_le_count_add_one ff

theorem two_mul_count_bool_of_even (hl : chain' (≠) l) (h2 : even (length l)) (b : bool) :
  2 * count b l = length l :=
by rw [← count_bnot_add_count l b, hl.count_bnot_eq_count h2, two_mul]

theorem two_mul_count_bool_eq_ite (hl : chain' (≠) l) (b : bool) :
  2 * count b l = if even (length l) then length l else
    if b ∈ l.head' then length l + 1 else length l - 1 :=
begin
  by_cases h2 : even (length l),
  { rw [if_pos h2, hl.two_mul_count_bool_of_even h2] },
  { cases l with x l, { exact (h2 even_zero).elim },
    simp only [if_neg h2, count_cons', mul_add, head', option.mem_some_iff, @eq_comm _ x],
    rw [length_cons, nat.even_add_one, not_not] at h2,
    replace hl : l.chain' (≠) := hl.tail,
    rw [hl.two_mul_count_bool_of_even h2],
    split_ifs; simp }
end

theorem length_sub_one_le_two_mul_count_bool (hl : chain' (≠) l) (b : bool) :
  length l - 1 ≤ 2 * count b l :=
by { rw [hl.two_mul_count_bool_eq_ite], split_ifs; simp [le_tsub_add, nat.le_succ_of_le] }

theorem length_div_two_le_count_bool (hl : chain' (≠) l) (b : bool) : length l / 2 ≤ count b l :=
begin
  rw [nat.div_le_iff_le_mul_add_pred two_pos, ← tsub_le_iff_right],
  exact length_sub_one_le_two_mul_count_bool hl b
end

lemma two_mul_count_bool_le_length_add_one (hl : chain' (≠) l) (b : bool) :
  2 * count b l ≤ length l + 1 :=
by { rw [hl.two_mul_count_bool_eq_ite], split_ifs; simp [nat.le_succ_of_le] }

end chain'

end list
