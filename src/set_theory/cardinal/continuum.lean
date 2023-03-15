/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import set_theory.cardinal.ordinal

/-!
# Cardinality of continuum

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `cardinal.continuum` (notation: `𝔠`, localized in `cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `cardinal.continuum` in locale `cardinal`.
-/

namespace cardinal

universes u v

open_locale cardinal

/-- Cardinality of continuum. -/
def continuum : cardinal.{u} := 2 ^ aleph_0.{u}

localized "notation (name := cardinal.continuum) `𝔠` := cardinal.continuum" in cardinal

@[simp] lemma two_power_aleph_0 : 2 ^ aleph_0.{u} = continuum.{u} := rfl

@[simp] lemma lift_continuum : lift.{v} 𝔠 = 𝔠 :=
by rw [←two_power_aleph_0, lift_two_power, lift_aleph_0, two_power_aleph_0]

/-!
### Inequalities
-/

lemma aleph_0_lt_continuum : ℵ₀ < 𝔠 := cantor ℵ₀

lemma aleph_0_le_continuum : ℵ₀ ≤ 𝔠 := aleph_0_lt_continuum.le

@[simp] lemma beth_one : beth 1 = 𝔠 := by simpa using beth_succ 0

lemma nat_lt_continuum (n : ℕ) : ↑n < 𝔠 := (nat_lt_aleph_0 n).trans aleph_0_lt_continuum

lemma mk_set_nat : #(set ℕ) = 𝔠 := by simp

lemma continuum_pos : 0 < 𝔠 := nat_lt_continuum 0

lemma continuum_ne_zero : 𝔠 ≠ 0 := continuum_pos.ne'

lemma aleph_one_le_continuum : aleph 1 ≤ 𝔠 :=
by { rw ←succ_aleph_0, exact order.succ_le_of_lt aleph_0_lt_continuum }

@[simp] theorem continuum_to_nat : continuum.to_nat = 0 :=
to_nat_apply_of_aleph_0_le aleph_0_le_continuum

@[simp] theorem continuum_to_part_enat : continuum.to_part_enat = ⊤ :=
to_part_enat_apply_of_aleph_0_le aleph_0_le_continuum

/-!
### Addition
-/

@[simp] lemma aleph_0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
add_eq_right aleph_0_le_continuum aleph_0_le_continuum

@[simp] lemma continuum_add_aleph_0 : 𝔠 + ℵ₀ = 𝔠 :=
(add_comm _ _).trans aleph_0_add_continuum

@[simp] lemma continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
add_eq_right aleph_0_le_continuum le_rfl

@[simp] lemma nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
add_eq_right aleph_0_le_continuum (nat_lt_continuum n).le

@[simp] lemma continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
(add_comm _ _).trans (nat_add_continuum n)

/-!
### Multiplication
-/

@[simp] lemma continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
mul_eq_left aleph_0_le_continuum le_rfl continuum_ne_zero

@[simp] lemma continuum_mul_aleph_0 : 𝔠 * ℵ₀ = 𝔠 :=
mul_eq_left aleph_0_le_continuum aleph_0_le_continuum aleph_0_ne_zero

@[simp] lemma aleph_0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
(mul_comm _ _).trans continuum_mul_aleph_0

@[simp] lemma nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
mul_eq_right aleph_0_le_continuum (nat_lt_continuum n).le (nat.cast_ne_zero.2 hn)

@[simp] lemma continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
(mul_comm _ _).trans (nat_mul_continuum hn)

/-!
### Power
-/

@[simp] lemma aleph_0_power_aleph_0 : aleph_0.{u} ^ aleph_0.{u} = 𝔠 :=
power_self_eq le_rfl

@[simp] lemma nat_power_aleph_0 {n : ℕ} (hn : 2 ≤ n) : (n ^ aleph_0.{u} : cardinal.{u}) = 𝔠 :=
nat_power_eq le_rfl hn

@[simp] lemma continuum_power_aleph_0 : continuum.{u} ^ aleph_0.{u} = 𝔠 :=
by rw [←two_power_aleph_0, ←power_mul, mul_eq_left le_rfl le_rfl aleph_0_ne_zero]

end cardinal
