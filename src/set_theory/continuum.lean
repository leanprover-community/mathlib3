/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import set_theory.cardinal_ordinal

/-!
# Cardinality of continuum

In this file we define `cardinal.continuum` (notation: `𝔠`, localized in `cardinal`) to be `2 ^ ω`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `cardinal.continuum` in locale `cardinal`.
-/

namespace cardinal

universes u v

open_locale cardinal

/-- Cardinality of continuum. -/
def continuum : cardinal.{u} := 2 ^ omega.{u}

localized "notation `𝔠` := cardinal.continuum" in cardinal

@[simp] lemma two_power_omega : (2 ^ omega.{u} : cardinal.{u}) = 𝔠 := rfl

@[simp] lemma lift_continuum : lift.{v} continuum.{u} = 𝔠 :=
by rw [← two_power_omega, lift_two_power, lift_omega, two_power_omega]

/-!
### Inequalities
-/

lemma omega_lt_continuum : ω < 𝔠 := cantor ω

lemma omega_le_continuum : ω ≤ 𝔠 := omega_lt_continuum.le

lemma nat_lt_continuum (n : ℕ) : ↑n < 𝔠 := (nat_lt_omega n).trans omega_lt_continuum

lemma mk_set_nat : #(set ℕ) = 𝔠 := by simp

lemma continuum_pos : 0 < 𝔠 := nat_lt_continuum 0

lemma continuum_ne_zero : 𝔠 ≠ 0 := continuum_pos.ne'

/-!
### Addition
-/

@[simp] lemma omega_add_continuum : ω + 𝔠 = 𝔠 :=
add_eq_right omega_le_continuum omega_le_continuum

@[simp] lemma continuum_add_omega : 𝔠 + ω = 𝔠 :=
(add_comm _ _).trans omega_add_continuum

@[simp] lemma continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
add_eq_right omega_le_continuum le_rfl

@[simp] lemma nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
add_eq_right omega_le_continuum (nat_lt_continuum n).le

@[simp] lemma continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
(add_comm _ _).trans (nat_add_continuum n)

/-!
### Multiplication
-/

@[simp] lemma continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
mul_eq_left omega_le_continuum le_rfl continuum_ne_zero

@[simp] lemma continuum_mul_omega : 𝔠 * ω = 𝔠 :=
mul_eq_left omega_le_continuum omega_le_continuum omega_ne_zero

@[simp] lemma omega_mul_continuum : ω * 𝔠 = 𝔠 :=
(mul_comm _ _).trans continuum_mul_omega

@[simp] lemma nat_mul_continuum {n : ℕ} (hn : n ≠ 0) :
  ↑n * 𝔠 = 𝔠 :=
mul_eq_right omega_le_continuum (nat_lt_continuum n).le (nat.cast_ne_zero.2 hn)

@[simp] lemma continuum_mul_nat {n : ℕ} (hn : n ≠ 0) :
  𝔠 * n = 𝔠 :=
(mul_comm _ _).trans (nat_mul_continuum hn)

/-!
### Power
-/

@[simp] lemma omega_power_omega : omega.{u} ^ omega.{u} = 𝔠 :=
power_self_eq le_rfl

@[simp] lemma nat_power_omega {n : ℕ} (hn : 2 ≤ n) : (n ^ omega.{u} : cardinal.{u}) = 𝔠 :=
nat_power_eq le_rfl hn

@[simp] lemma continuum_power_omega : continuum.{u} ^ omega.{u} = 𝔠 :=
by rw [← two_power_omega, ← power_mul, mul_eq_left le_rfl le_rfl omega_ne_zero]

end cardinal
