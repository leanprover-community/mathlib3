/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import data.nat.choose.basic
import data.nat.prime

/-!
# Divisibility properties of binomial coefficients
-/

namespace nat

open_locale nat

namespace prime

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
    by exact dvd_choose_add hkp (nat.sub_lt (hk.trans hkp) hk) (by rw r) hp,
  rwa r at e,
end

end prime

lemma cast_choose (K : Type*) [division_ring K] [char_zero K] {a b : ℕ} (h : a ≤ b) :
  (b.choose a : K) = b! / (a! * (b - a)!) :=
begin
  have : ∀ {n : ℕ}, (n! : K) ≠ 0 := λ n, nat.cast_ne_zero.2 (factorial_ne_zero _),
  rw [eq_div_iff_mul_eq (mul_ne_zero this this)],
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h],
end

lemma cast_add_choose (K : Type*) [division_ring K] [char_zero K] {a b : ℕ} :
  ((a + b).choose a : K) = (a + b)! / (a! * b!) :=
by rw [cast_choose K (le_add_right le_rfl), nat.add_sub_cancel_left]

end nat
