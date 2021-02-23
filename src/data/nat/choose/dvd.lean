/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import data.nat.choose.basic
import data.nat.prime
import data.rat.floor
/-!
# Divisibility properties of binomial coefficients
-/

namespace nat
namespace prime

open_locale nat

lemma dvd_choose_add {p a b : ℕ} (hap : a < p) (hbp : b < p) (h : p ≤ a + b)
  (hp : prime p) : p ∣ choose (a + b) a :=
have h₁ : p ∣ (a + b)!, from hp.dvd_factorial.2 h,
have h₂ : ¬p ∣ a!, from mt hp.dvd_factorial.1 (not_le_of_gt hap),
have h₃ : ¬p ∣ b!, from mt hp.dvd_factorial.1 (not_le_of_gt hbp),
by
  rw [← choose_mul_factorial_mul_factorial (le.intro rfl), mul_assoc, hp.dvd_mul, hp.dvd_mul,
      nat.add_sub_cancel_left a b] at h₁;
  exact h₁.resolve_right (not_or_distrib.2 ⟨h₂, h₃⟩)

lemma dvd_choose_self {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) :
  p ∣ choose p k :=
begin
  have r : k + (p - k) = p,
    by rw [← nat.add_sub_assoc (nat.le_of_lt hkp) k, nat.add_sub_cancel_left],
  have e : p ∣ choose (k + (p - k)) k,
    by exact dvd_choose_add hkp (sub_lt (hk.trans hkp) hk) (by rw r) hp,
  rwa r at e,
end

lemma choose_eq_factorial_div_factorial' {a b : ℕ}
  (hab : a ≤ b) : (b.choose a : ℚ) = b! / (a! * (b - a)!) :=
begin
  field_simp [mul_ne_zero, factorial_ne_zero], norm_cast,
  rw ← choose_mul_factorial_mul_factorial hab, ring,
end

lemma choose_mul {n k s : ℕ} (hn : k ≤ n) (hs : s ≤ k) :
  (n.choose k : ℚ) * k.choose s = n.choose s * (n - s).choose (k - s) :=
begin
  rw [choose_eq_factorial_div_factorial' hn, choose_eq_factorial_div_factorial' hs,
      choose_eq_factorial_div_factorial' (le_trans hs hn), choose_eq_factorial_div_factorial' ],
  swap,
  { exact nat.sub_le_sub_right hn s, },
  { field_simp [mul_ne_zero, factorial_ne_zero],
    rw sub_sub_sub_cancel_right hs, ring, },
end

end prime
end nat
