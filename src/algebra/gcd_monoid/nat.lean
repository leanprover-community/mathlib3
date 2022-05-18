/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.gcd_monoid.finset
import number_theory.padics.padic_val

/-!
# Basic results about setwise gcds on ℕ

This file proves some basic results about `finset.gcd` on `ℕ`.

## Main results
* `finset.coprime_of_div_gcd`: The elements of a set divided through by their gcd are coprime.

-/

instance : is_idempotent ℕ gcd_monoid.gcd := ⟨nat.gcd_self⟩

namespace finset

theorem coprime_of_div_gcd (s : finset ℕ) {x : ℕ} (hx : x ∈ s) (hnz : x ≠ 0) :
  s.gcd (/ (s.gcd id)) = 1 :=
begin
  rw nat.eq_one_iff_not_exists_prime_dvd,
  intros p hp hdvd,
  haveI : fact p.prime := ⟨hp⟩,
  rw dvd_gcd_iff at hdvd,
  replace hdvd : ∀ b ∈ s, s.gcd id * p ∣ b,
  { intros b hb,
    specialize hdvd b hb,
    rwa nat.dvd_div_iff at hdvd,
    apply gcd_dvd hb },
  have : s.gcd id ≠ 0 := (not_iff_not.mpr gcd_eq_zero_iff).mpr (λ h, hnz $ h x hx),
  apply @pow_succ_padic_val_nat_not_dvd p _ _ this.bot_lt,
  apply dvd_gcd,
  intros b hb,
  obtain ⟨k, rfl⟩ := hdvd b hb,
  rw [id, mul_right_comm, pow_succ', mul_dvd_mul_iff_right hp.ne_zero],
  apply dvd_mul_of_dvd_left,
  exact pow_padic_val_nat_dvd
end

end finset
