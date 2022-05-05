/-
Copyright (c) 2020 Pim Spelier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daan van Gent, Praneeth Kolichala, Pim Spelier
-/
import data.num.lemmas
import data.nat.log


/-!
# Conversion of `num` to and from `list bool`

This file provides functions to encode `num` as a `list bool` and decode `list bool`'s into `num`'s.
For convenience, the decoding function always returns a value, essentially ignoring trailing `ff`'s.
-/

namespace pos_num

/-- Convert a `pos_num` to a `list bool` in little-endian form (with LSB at the head).
This is an equivalence, so the msb (which is always present for positive numbers) is omitted. -/
def to_trailing_bits : pos_num → list bool
| 1 := []
| (bit0 xs) := ff :: xs.to_trailing_bits
| (bit1 xs) := tt :: xs.to_trailing_bits

/-- Equivalence between `pos_num` and `list bool` with lsb at the head and msb omitted -/
def equiv_list_bool : pos_num ≃ list bool :=
{ to_fun := to_trailing_bits,
  inv_fun := λ l, l.foldr (λ b n, (cond b bit1 bit0) n) 1,
  left_inv := λ n, by induction n; simpa [to_trailing_bits],
  right_inv := λ l, by { induction l with hd, { refl, }, cases hd; simpa [to_trailing_bits], } }

@[simp] lemma equiv_list_bool_one : equiv_list_bool 1 = [] := rfl
@[simp] lemma equiv_list_bool_bit0 (n : pos_num) :
  equiv_list_bool (bit0 n) = ff :: equiv_list_bool n := rfl
@[simp] lemma equiv_list_bool_bit1 (n : pos_num) :
  equiv_list_bool (bit1 n) = tt :: equiv_list_bool n := rfl
@[simp] lemma equiv_list_bool_symm_cons_tt (l : list bool) :
  equiv_list_bool.symm (tt :: l) = bit1 (equiv_list_bool.symm l) := rfl
@[simp] lemma equiv_list_bool_symm_cons_ff (l : list bool) :
  equiv_list_bool.symm (ff :: l) = bit0 (equiv_list_bool.symm l) := rfl

lemma to_trailing_bits_len (n : pos_num) : (equiv_list_bool n).length = nat.log 2 n :=
begin
  induction n with b ih b ih, { erw equiv_list_bool_one, simp, },
  { simp [cast_bit1, nat.bit1_val b, ih], },
  { simp [cast_bit0, nat.bit0_val b, ih, nat.one_add], }
end

end pos_num

namespace num

/-- An encoding function of the binary numbers in bool. -/
def to_bits : num → list bool
| num.zero := []
| (num.pos n) := (pos_num.equiv_list_bool n) ++ [tt]

@[simp] lemma to_bits_zero : to_bits 0 = [] := rfl

@[simp] lemma to_bits_bit0 (n : num) (hn : n ≠ 0) : (num.bit0 n).to_bits = ff :: n.to_bits :=
by { cases n, { contradiction, }, simp [to_bits, num.bit0], }

@[simp] lemma to_bits_bit1 (n : num) : (num.bit1 n).to_bits = tt :: n.to_bits :=
by { cases n, { refl, }, simp [to_bits, num.bit1], }

/-- A decoding function from `list bool` to `num` -/
def of_bits : list bool → num
| [] := 0
| (tt :: xs) := num.bit1 (of_bits xs)
| (ff :: xs) := num.bit0 (of_bits xs)

@[simp] lemma of_bits_nil : of_bits [] = 0 := rfl
@[simp] lemma of_bits_cons_ff (l : list bool) : of_bits (ff :: l) = num.bit0 (of_bits l) := rfl
@[simp] lemma of_bits_cons_tt (l : list bool) : of_bits (tt :: l) = num.bit1 (of_bits l) := rfl
lemma of_bits_append_tt (l : list bool) : of_bits (l ++ [tt]) = pos_num.equiv_list_bool.symm l :=
by { induction l with hd tl ih, { refl, }, cases hd; simp [ih]; refl, }

@[simp] lemma of_bits_to_bits (n : num) : of_bits (to_bits n) = n :=
by { cases n, { refl, }, simp [of_bits_append_tt, to_bits], }

lemma of_bits_to_bits_left_inv : function.left_inverse of_bits to_bits := of_bits_to_bits

lemma mem_to_bits_range_iff (l : list bool) :
  l ∈ set.range to_bits ↔ l = [] ∨ tt ∈ l.last' :=
begin
  split, { rintro ⟨n, h⟩, subst h, cases n; simp [to_bits], },
  apply list.reverse_cases_on l, { intro, use 0, refl, },
  intros st lt h,
  use (pos_num.equiv_list_bool.symm st),
  symmetry, simpa [to_bits] using h,
end

@[simp] lemma to_bits_of_bits_valid {l : list bool} (h : l ∈ set.range to_bits) :
  to_bits (of_bits l) = l := of_bits_to_bits_left_inv.right_inv_on_range h

@[simp] lemma of_bits_invalid (l : list bool) : of_bits (l ++ [ff]) = of_bits l :=
by { induction l with hd tl ih, { refl, }, cases hd; simp [ih], }

lemma to_bits_len (n : num) : (to_bits n).length = if n = 0 then 0 else nat.log 2 n + 1 :=
begin
  cases n, { refl, },
  simp [(show pos n ≠ 0, by trivial), to_bits, pos_num.to_trailing_bits_len],
end

lemma to_bits_len_le (n : num) : (to_bits n).length ≤ nat.log 2 n + 1 :=
by { rw to_bits_len, split_ifs with h; simp [h],  }

lemma of_bits_lt {l : list bool} (hl : l ∈ set.range to_bits) : (of_bits l : ℕ) < 2^l.length :=
begin
  rcases hl with ⟨n, rfl⟩,
  by_cases h : n = 0, { subst h, simp, },
  convert nat.lt_pow_succ_log_self (show 1 < 2, by simp) n;
  simp [h, to_bits_len],
end

lemma le_of_bits (l : list bool) : 2^l.length ≤ (of_bits (l ++ [tt]) : ℕ) :=
begin
  rw of_bits_append_tt, simp only [num.cast_pos, pos_num.cast_to_num],
  induction l with hd tl ih, { simp, },
  cases hd,
  { simpa [nat.bit0_val (pos_num.equiv_list_bool.symm tl), pow_add, mul_comm], },
  refine calc _ = 2 * 2^tl.length : by { simp [pow_add, mul_comm], }
            ... ≤ 2 * 2^tl.length + 1 : nat.le_succ _
            ... ≤ _ : _,
  simpa [nat.bit1_val (pos_num.equiv_list_bool.symm tl)],
end

lemma of_bits_strict_mono {l₁ l₂ : list bool} (h : l₁.length < l₂.length) :
  (of_bits (l₁ ++ [tt]) : ℕ) < of_bits (l₂ ++ [tt]) :=
calc (of_bits (l₁ ++ [tt]) : ℕ)
      < 2^(l₁.length + 1) : by { convert of_bits_lt _; simp [mem_to_bits_range_iff], }
 ...  ≤ 2^l₂.length: pow_mono (show 1 ≤ 2, by simp) (nat.succ_le_iff.mpr h)
 ...  ≤ of_bits (l₂ ++ [tt]) : le_of_bits l₂

@[simp] lemma to_bits_nil_iff (n : num) : to_bits n = [] ↔ n = 0 :=
⟨λ h, by simpa using congr_arg of_bits h, λ h, by { rw h, refl, }⟩

end num
