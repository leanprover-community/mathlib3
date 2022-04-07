/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import data.num.lemmas
import data.nat.log
import tactic.linarith


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

lemma encode_pos_num_len (n : pos_num) : (equiv_list_bool n).length = nat.log 2 n :=
begin
  induction n with b ih b ih, { erw equiv_list_bool_one, simp, },
  { simp [cast_bit1, nat.bit1_val b, ih], },
  { simp [cast_bit0, nat.bit0_val b, ih], }
end

lemma decode_pos_num_lt (ls : list bool) : (equiv_list_bool.symm ls : ℕ) < 2^(ls.length+1) :=
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
def encode_num : num → list bool
| num.zero := []
| (num.pos n) := (pos_num.equiv_list_bool n) ++ [tt]

@[simp] lemma encode_zero : encode_num 0 = [] := rfl

@[simp] lemma encode_bit0 (n : num) (hn : n ≠ 0) : (num.bit0 n).encode_num = ff :: n.encode_num :=
by { cases n, { contradiction, }, simp [encode_num, num.bit0], }

@[simp] lemma encode_bit1 (n : num) : (num.bit1 n).encode_num = tt :: n.encode_num :=
by { cases n, { refl, }, simp [encode_num, num.bit1], }

/-- A decoding function from `list bool` to `num` -/
def decode_num (L : list bool) : num := if L = [] then 0 else pos_num.equiv_list_bool.inv_fun L.init

@[simp] lemma decode_num_nil : decode_num [] = 0 := rfl
@[simp] lemma decode_num_cons_ff (l : list bool) (hl : l ≠ []) :
  decode_num (ff :: l) = num.bit0 (decode_num l) := by simp [decode_num, hl, num.bit0]
@[simp] lemma decode_num_cons_tt (l : list bool) : decode_num (tt :: l) = num.bit1 (decode_num l) :=
by { cases l, { refl, }, simp [decode_num, num.bit1], }

@[simp] lemma decode_encode_num (n : num) : decode_num (encode_num n) = n :=
by { cases n, { refl, }, simp [decode_num, encode_num], }

lemma decode_encode_left_inv : function.left_inverse decode_num encode_num := decode_encode_num

lemma mem_encode_range_iff (l : list bool) :
  l ∈ set.range encode_num ↔ l = [] ∨ tt ∈ l.last' :=
begin
  split, { rintro ⟨n, h⟩, subst h, cases n; simp [encode_num], },
  apply list.reverse_cases_on l, { intro, use 0, refl, },
  intros st lt h,
  use (pos_num.equiv_list_bool.inv_fun st),
  symmetry, simpa [encode_num] using h,
end

@[simp] lemma encode_decode_list_bool_valid {l : list bool} (h : l ∈ set.range encode_num) :
  encode_num (decode_num l) = l := decode_encode_left_inv.right_inv_on_range h

@[simp] lemma decode_list_bool_invalid (l : list bool) :
  decode_num (l ++ [ff]) = decode_num (l ++ [tt]) := by simp [decode_num]

lemma encode_num_len (n : num) : (encode_num n).length = if n = 0 then 0 else nat.log 2 n + 1 :=
begin
  cases n, { refl, },
  simp [(show pos n ≠ 0, by trivial), encode_num, pos_num.encode_pos_num_len],
end

lemma encode_num_len_le (n : num) : (encode_num n).length ≤ nat.log 2 n + 1 :=
by { rw encode_num_len, split_ifs; linarith, }

lemma decode_num_lt (l : list bool) : (decode_num l : ℕ) < 2^l.length :=
begin
  apply list.reverse_cases_on l, { simp [decode_num], },
  intros st tl, cases tl; simpa [decode_num] using pos_num.decode_pos_num_lt _,
end

lemma le_decode_num (l : list bool) (hl : l ≠ []) : 2^(l.length - 1) ≤ (decode_num l : ℕ) :=
begin
  induction l with hd tl ih, { contradiction, },
  cases tl with h t, { cases hd; simp [decode_num], },
  specialize ih (by trivial),
  cases hd,
  { simpa [pow_add, nat.bit0_val (decode_num (h :: t)), mul_comm] using ih, },
  simp only [decode_num_cons_tt, nat.bit1_val (decode_num (h :: t)), num.cast_bit1],
  refine trans _ (nat.le_succ _),
  simpa [pow_add, mul_comm] using ih,
end

lemma decode_num_strict_mono (l₁ l₂ : list bool) (h : l₁.length < l₂.length) :
  (decode_num l₁ : ℕ) < decode_num l₂ :=
calc (decode_num l₁ : ℕ) < 2^l₁.length : decode_num_lt l₁
                    ...  ≤ 2^(l₂.length - 1) : pow_mono (show 1 ≤ 2, by simp) (nat.le_pred_of_lt h)
                    ...  ≤ decode_num l₂ : le_decode_num l₂ (λ H, by { subst H, simpa using h, })

@[simp] lemma encode_num_nil_iff (n : num) : encode_num n = [] ↔ n = 0 :=
⟨λ h, by simpa using congr_arg decode_num h, λ h, by { rw h, refl, }⟩

@[simp] lemma decode_list_zero_iff (l : list bool) : decode_num l = 0 ↔ l = [] :=
⟨λ h, by { by_contra H, simp [decode_num, H] at h, contradiction, }, λ h, by { rw h, refl, }⟩

end num
