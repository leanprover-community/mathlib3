/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import data.num.lemmas
import data.nat.log


/-!
# Conversion of `num` to and from `list bool`

This file provides functions to encode `num` as a `list bool` and decode `list bool`'s into `num`'s.
For convenience, the decoding function always returns a value. If the most significant bit isn't
`1`, it implicitly changes it to `1` when decoding. We then prove several lemmas about this
encoding.
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
  { simp [cast_bit0, nat.bit0_val b, ih], }
end

lemma equiv_list_bool_symm_lt (ls : list bool) : (equiv_list_bool.symm ls : ℕ) < 2^(ls.length+1) :=
begin
  induction ls with hd tl ih, { simp [equiv_list_bool], },
  cases hd,
  { simp only [equiv_list_bool_symm_cons_ff, pos_num.cast_bit0],
    rw [nat.bit0_val, mul_comm, pow_add], simpa, },
  { simp only [equiv_list_bool_symm_cons_tt, pos_num.cast_bit1],
    rw [nat.bit1_val, add_comm, pow_add],
    apply @nat.lt_of_div_lt_div _ _ 2,
    simpa [nat.add_mul_div_left, nat.div_eq_of_lt], },
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
def of_bits (L : list bool) : num := if L = [] then 0 else pos_num.equiv_list_bool.symm L.init

@[simp] lemma of_bits_nil : of_bits [] = 0 := rfl
@[simp] lemma of_bits_cons_ff (l : list bool) (hl : l ≠ []) :
  of_bits (ff :: l) = num.bit0 (of_bits l) := by simp [of_bits, hl, num.bit0]
@[simp] lemma of_bits_cons_tt (l : list bool) : of_bits (tt :: l) = num.bit1 (of_bits l) :=
by { cases l, { refl, }, simp [of_bits, num.bit1], }

@[simp] lemma of_bits_to_bits (n : num) : of_bits (to_bits n) = n :=
by { cases n, { refl, }, simp [of_bits, to_bits], }

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

@[simp] lemma of_bits_invalid (l : list bool) :
  of_bits (l ++ [ff]) = of_bits (l ++ [tt]) := by simp [of_bits]

lemma to_bits_len (n : num) : (to_bits n).length = if n = 0 then 0 else nat.log 2 n + 1 :=
begin
  cases n, { refl, },
  simp [(show pos n ≠ 0, by trivial), to_bits, pos_num.to_trailing_bits_len],
end

lemma to_bits_len_le (n : num) : (to_bits n).length ≤ nat.log 2 n + 1 :=
by { rw to_bits_len, split_ifs with h; simp [h],  }

lemma of_bits_lt (l : list bool) : (of_bits l : ℕ) < 2^l.length :=
begin
  apply list.reverse_cases_on l, { simp [of_bits], },
  intros st tl, cases tl; simpa [of_bits] using pos_num.equiv_list_bool_symm_lt _,
end

lemma le_of_bits (l : list bool) (hl : l ≠ []) : 2^(l.length - 1) ≤ (of_bits l : ℕ) :=
begin
  induction l with hd tl ih, { contradiction, },
  cases tl with h t, { cases hd; simp [of_bits], },
  specialize ih (by trivial),
  cases hd,
  { simpa [pow_add, nat.bit0_val (of_bits (h :: t)), mul_comm] using ih, },
  simp only [of_bits_cons_tt, nat.bit1_val (of_bits (h :: t)), num.cast_bit1],
  refine trans _ (nat.le_succ _),
  simpa [pow_add, mul_comm] using ih,
end

lemma of_bits_strict_mono (l₁ l₂ : list bool) (h : l₁.length < l₂.length) :
  (of_bits l₁ : ℕ) < of_bits l₂ :=
calc (of_bits l₁ : ℕ) < 2^l₁.length : of_bits_lt l₁
                    ...  ≤ 2^(l₂.length - 1) : pow_mono (show 1 ≤ 2, by simp) (nat.le_pred_of_lt h)
                    ...  ≤ of_bits l₂ : le_of_bits l₂ (λ H, by { subst H, simpa using h, })

@[simp] lemma to_bits_nil_iff (n : num) : to_bits n = [] ↔ n = 0 :=
⟨λ h, by simpa using congr_arg of_bits h, λ h, by { rw h, refl, }⟩

@[simp] lemma of_bits_zero_iff (l : list bool) : of_bits l = 0 ↔ l = [] :=
⟨λ h, by { by_contra H, simp [of_bits, H] at h, contradiction, }, λ h, by { rw h, refl, }⟩

end num
