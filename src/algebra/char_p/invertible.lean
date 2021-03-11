/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import algebra.invertible
import algebra.field
import algebra.char_p.basic

/-!
# Invertibility of elements given a characteristic

This file  includes some instances of `invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertible_of_nonzero` is a useful definition.
-/
section ring_char

/-- A natural number `t` is invertible in a field `K` if the charactistic of `K` does not divide
`t`. -/
def invertible_of_ring_char_not_dvd {K : Type*} [field K]
  {t : ℕ} (not_dvd : ¬(ring_char K ∣ t)) : invertible (t : K) :=
invertible_of_nonzero (λ h, not_dvd ((ring_char.spec K t).mp h))

end ring_char

section char_p

/-- A natural number `t` is invertible in a field `K` of charactistic `p` if `p` does not divide
`t`. -/
def invertible_of_char_p_not_dvd {K : Type*} [field K] {p : ℕ} [char_p K p]
  {t : ℕ} (not_dvd : ¬(p ∣ t)) : invertible (t : K) :=
invertible_of_nonzero (λ h, not_dvd ((char_p.cast_eq_zero_iff K p t).mp h))

instance invertible_of_pos {K : Type*} [field K] [char_zero K] (n : ℕ) [h : fact (0 < n)] :
  invertible (n : K) :=
invertible_of_nonzero $ by simpa [pos_iff_ne_zero] using h

end char_p

section division_ring

variable [division_ring α]

instance invertible_succ [char_zero α] (n : ℕ) : invertible (n.succ : α) :=
invertible_of_nonzero (nat.cast_ne_zero.mpr (nat.succ_ne_zero _))

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/

instance invertible_two [char_zero α] : invertible (2 : α) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 2 ≠ 0))

instance invertible_three [char_zero α] : invertible (3 : α) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 3 ≠ 0))

end division_ring
