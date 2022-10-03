/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import data.zmod.basic
import ring_theory.int.basic

/-!
# Coprimality and vanishing

We show that for prime `p`, the image of an integer `a` in `zmod p` vanishes if and only if
`a` and `p` are not coprime.
-/

namespace zmod

/-- If `p` is a prime and `a` is an integer, then `a : zmod p` is zero if and only if
`gcd a p ≠ 1`. -/
lemma eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : fact p.prime] : (a : zmod p) = 0 ↔ a.gcd p ≠ 1 :=
by rw [ne, int.gcd_comm, int.gcd_eq_one_iff_coprime,
       (nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, not_not, int_coe_zmod_eq_zero_iff_dvd]

/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : zmod p` is nonzero. -/
lemma ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p = 1) :
  (a : zmod p) ≠ 0 :=
mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (not_not.mpr h)

/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : zmod p` is zero. -/
lemma eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p ≠ 1) :
  (a : zmod p) = 0 :=
(@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h

end zmod
