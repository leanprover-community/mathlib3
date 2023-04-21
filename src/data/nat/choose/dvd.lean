/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import data.nat.choose.basic
import data.nat.prime

/-!
# Divisibility properties of binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace nat

open_locale nat

namespace prime

lemma dvd_choose_add {p a b : ℕ} (hp : prime p) (hap : a < p) (hbp : b < p) (h : p ≤ a + b) :
  p ∣ choose (a + b) a :=
begin
  have h₁ : p ∣ (a + b)!, from hp.dvd_factorial.2 h,
  rw [← add_choose_mul_factorial_mul_factorial, ← choose_symm_add, hp.dvd_mul, hp.dvd_mul,
    hp.dvd_factorial, hp.dvd_factorial] at h₁,
  exact (h₁.resolve_right hbp.not_le).resolve_right hap.not_le
end

lemma dvd_choose {p a b : ℕ} (hp : prime p) (ha : a < p) (hab : b - a < p) (h : p ≤ b) :
  p ∣ choose b a :=
have a + (b - a) = b := nat.add_sub_of_le (ha.le.trans h),
this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)

lemma dvd_choose_self {p k : ℕ} (hp : prime p) (hk : k ≠ 0) (hkp : k < p) : p ∣ choose p k :=
hp.dvd_choose hkp (nat.sub_lt ((zero_le _).trans_lt hkp) hk.bot_lt) le_rfl

end prime

end nat
