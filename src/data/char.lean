/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Keeley Hoek

Supplementary theorems about the `char` type.
-/
import data.nat.basic data.num.bitwise

instance : decidable_linear_order char :=
{ le_refl := λ a, @le_refl ℕ _ _,
  le_trans := λ a b c, @le_trans ℕ _ _ _ _,
  le_antisymm := λ a b h₁ h₂,
    char.eq_of_veq $ le_antisymm h₁ h₂,
  le_total := λ a b, @le_total ℕ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ _ _,
  decidable_le := char.decidable_le,
  decidable_eq := char.decidable_eq,
  decidable_lt := char.decidable_lt,
  ..char.has_le, ..char.has_lt }

def byte.nat_max : ℕ := 0xFF

def nat.trunc_to_byte (n : ℕ) : char :=
if h : n > byte.nat_max then ⟨ byte.nat_max, dec_trivial ⟩
else ⟨ n, or.inl $ lt_trans (nat.lt_succ_of_le $ not_lt.mp h) dec_trivial ⟩

namespace utf8

def TAG_CONT    := 0b10000000
def TAG_TWO_B   := 0b11000000
def TAG_THREE_B := 0b11100000
def TAG_FOUR_B  := 0b11110000
def MAX_ONE_B   := 0x80
def MAX_TWO_B   := 0x800
def MAX_THREE_B := 0x10000

open num

def decode_char (c : char) : list char :=
let code : nat := c.to_nat in
let bytes : list ℕ :=
if code < MAX_ONE_B then [
  code
]
else if code < MAX_TWO_B then [
  lor (land (shiftr code  6) 0x1F) TAG_TWO_B,
  lor (land (shiftr code  0) 0x3F) TAG_CONT
]
else if code < MAX_THREE_B then [
  lor (land (shiftr code 12) 0x0F) TAG_THREE_B,
  lor (land (shiftr code  6) 0x3F) TAG_CONT,
  lor (land (shiftr code  0) 0x3F) TAG_CONT
]
else [
  lor (land (shiftr code 18) 0x07) TAG_FOUR_B,
  lor (land (shiftr code 12) 0x3F) TAG_CONT,
  lor (land (shiftr code  6) 0x3F) TAG_CONT,
  lor (land (shiftr code  0) 0x3F) TAG_CONT
]
in bytes.map nat.trunc_to_byte

def decode (cb : list char) : list char := list.join $ cb.map decode_char

end utf8
