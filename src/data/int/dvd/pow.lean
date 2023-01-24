/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.int.dvd.basic
import data.nat.pow

/-!
# Basic lemmas about the divisibility relation in `ℤ` involving powers.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open nat

namespace int

@[simp]
theorem sign_pow_bit1 (k : ℕ) : ∀ n : ℤ, n.sign ^ (bit1 k) = n.sign
| (n+1:ℕ) := one_pow (bit1 k)
| 0       := zero_pow (nat.zero_lt_bit1 k)
| -[1+ n] := (neg_pow_bit1 1 k).trans (congr_arg (λ x, -x) (one_pow (bit1 k)))

lemma pow_dvd_of_le_of_pow_dvd {p m n : ℕ} {k : ℤ} (hmn : m ≤ n) (hdiv : ↑(p ^ n) ∣ k) :
  ↑(p ^ m) ∣ k :=
begin
  induction k,
  { apply int.coe_nat_dvd.2,
    apply pow_dvd_of_le_of_pow_dvd hmn,
    apply int.coe_nat_dvd.1 hdiv },
  change -[1+k] with -(↑(k+1) : ℤ),
  apply dvd_neg_of_dvd,
  apply int.coe_nat_dvd.2,
  apply pow_dvd_of_le_of_pow_dvd hmn,
  apply int.coe_nat_dvd.1,
  apply dvd_of_dvd_neg,
  exact hdiv,
end

lemma dvd_of_pow_dvd {p k : ℕ} {m : ℤ} (hk : 1 ≤ k) (hpk : ↑(p^k) ∣ m) : ↑p ∣ m :=
by rw ←pow_one p; exact pow_dvd_of_le_of_pow_dvd hk hpk

end int
