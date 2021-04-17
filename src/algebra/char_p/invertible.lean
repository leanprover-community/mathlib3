/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.invertible
import algebra.field
import algebra.char_p.basic

/-!
# Invertibility of elements given a characteristic

This file includes some instances of `invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertible_of_nonzero` is a useful definition.
-/

variables {K : Type*}

section field
variables [field K]

/-- A natural number `t` is invertible in a field `K` if the charactistic of `K` does not divide
`t`. -/
def invertible_of_ring_char_not_dvd
  {t : ℕ} (not_dvd : ¬(ring_char K ∣ t)) : invertible (t : K) :=
invertible_of_nonzero (λ h, not_dvd ((ring_char.spec K t).mp h))

lemma not_ring_char_dvd_of_invertible {t : ℕ} [invertible (t : K)] :
  ¬(ring_char K ∣ t) :=
begin
  rw [← ring_char.spec, ← ne.def],
  exact nonzero_of_invertible (t : K)
end

/-- A natural number `t` is invertible in a field `K` of charactistic `p` if `p` does not divide
`t`. -/
def invertible_of_char_p_not_dvd {p : ℕ} [char_p K p]
  {t : ℕ} (not_dvd : ¬(p ∣ t)) : invertible (t : K) :=
invertible_of_nonzero (λ h, not_dvd ((char_p.cast_eq_zero_iff K p t).mp h))

instance invertible_of_pos [char_zero K] (n : ℕ) [h : fact (0 < n)] :
  invertible (n : K) :=
invertible_of_nonzero $ by simpa [pos_iff_ne_zero] using h.out

end field

section division_ring
variables [division_ring K] [char_zero K]

instance invertible_succ (n : ℕ) : invertible (n.succ : K) :=
invertible_of_nonzero (nat.cast_ne_zero.mpr (nat.succ_ne_zero _))

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/

instance invertible_two : invertible (2 : K) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 2 ≠ 0))

instance invertible_three : invertible (3 : K) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 3 ≠ 0))

end division_ring
