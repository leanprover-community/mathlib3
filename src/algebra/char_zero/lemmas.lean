/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import data.nat.cast.field
import algebra.group_power.lemmas

/-!
# Characteristic zero (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main statements

* Characteristic zero implies that the additive monoid is infinite.
-/

namespace nat
variables {R : Type*} [add_monoid_with_one R] [char_zero R]

/-- `nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def cast_embedding : ℕ ↪ R := ⟨coe, cast_injective⟩

@[simp] lemma cast_pow_eq_one {R : Type*} [semiring R] [char_zero R] (q : ℕ) (n : ℕ) (hn : n ≠ 0) :
  (q : R) ^ n = 1 ↔ q = 1 :=
by { rw [←cast_pow, cast_eq_one], exact pow_eq_one_iff hn }

@[simp, norm_cast]
theorem cast_div_char_zero {k : Type*} [field k] [char_zero k] {m n : ℕ}
  (n_dvd : n ∣ m) : ((m / n : ℕ) : k) = m / n :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  { exact cast_div n_dvd (cast_ne_zero.2 hn), },
end

end nat

section

variables (M : Type*) [add_monoid_with_one M] [char_zero M]

instance char_zero.ne_zero.two : ne_zero (2 : M) :=
⟨have ((2:ℕ):M) ≠ 0, from nat.cast_ne_zero.2 dec_trivial, by rwa [nat.cast_two] at this⟩

end

section
variables {R : Type*} [non_assoc_semiring R] [no_zero_divisors R] [char_zero R] {a : R}

@[simp]
lemma add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 :=
by simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or]

@[simp]
lemma bit0_eq_zero {a : R} : bit0 a = 0 ↔ a = 0 := add_self_eq_zero
@[simp]
lemma zero_eq_bit0 {a : R} : 0 = bit0 a ↔ a = 0 :=
by { rw [eq_comm], exact bit0_eq_zero }

lemma bit0_ne_zero : bit0 a ≠ 0 ↔ a ≠ 0 := bit0_eq_zero.not
lemma zero_ne_bit0 : 0 ≠ bit0 a ↔ a ≠ 0 := zero_eq_bit0.not

end

section
variables {R : Type*} [non_assoc_ring R] [no_zero_divisors R] [char_zero R]

lemma neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
neg_eq_iff_add_eq_zero.trans add_self_eq_zero

lemma eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
eq_neg_iff_add_eq_zero.trans add_self_eq_zero

lemma nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b :=
begin
  rw [←sub_eq_zero, ←mul_sub, mul_eq_zero, sub_eq_zero] at h,
  exact_mod_cast h,
end

lemma nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b :=
by simpa [w] using nat_mul_inj h

lemma bit0_injective : function.injective (bit0 : R → R) :=
λ a b h, begin
  dsimp [bit0] at h,
  simp only [(two_mul a).symm, (two_mul b).symm] at h,
  refine nat_mul_inj' _ two_ne_zero,
  exact_mod_cast h,
end

lemma bit1_injective : function.injective (bit1 : R → R) :=
λ a b h, begin
  simp only [bit1, add_left_inj] at h,
  exact bit0_injective h,
end

@[simp] lemma bit0_eq_bit0 {a b : R} : bit0 a = bit0 b ↔ a = b :=
bit0_injective.eq_iff

@[simp] lemma bit1_eq_bit1 {a b : R} : bit1 a = bit1 b ↔ a = b :=
bit1_injective.eq_iff

@[simp]
lemma bit1_eq_one {a : R} : bit1 a = 1 ↔ a = 0 :=
by rw [show (1 : R) = bit1 0, by simp, bit1_eq_bit1]

@[simp]
lemma one_eq_bit1 {a : R} : 1 = bit1 a ↔ a = 0 :=
by { rw [eq_comm], exact bit1_eq_one }

end

section
variables {R : Type*} [division_ring R] [char_zero R]

@[simp] lemma half_add_self (a : R) : (a + a) / 2 = a :=
by rw [← mul_two, mul_div_cancel a two_ne_zero]

@[simp] lemma add_halves' (a : R) : a / 2 + a / 2 = a :=
by rw [← add_div, half_add_self]

lemma sub_half (a : R) : a - a / 2 = a / 2 :=
by rw [sub_eq_iff_eq_add, add_halves']

lemma half_sub (a : R) : a / 2 - a = - (a / 2) :=
by rw [← neg_sub, sub_half]

end

namespace with_top

instance {R : Type*} [add_monoid_with_one R] [char_zero R] : char_zero (with_top R) :=
{ cast_injective := λ m n h, by rwa [← coe_nat, ← coe_nat n, coe_eq_coe, nat.cast_inj] at h }

end with_top

section ring_hom

variables {R S : Type*} [non_assoc_semiring R] [non_assoc_semiring S]

lemma ring_hom.char_zero (ϕ : R →+* S) [hS : char_zero S] : char_zero R :=
⟨λ a b h, char_zero.cast_injective (by rw [←map_nat_cast ϕ, ←map_nat_cast ϕ, h])⟩

lemma ring_hom.char_zero_iff {ϕ : R →+* S} (hϕ : function.injective ϕ) :
  char_zero R ↔ char_zero S :=
⟨λ hR, ⟨by introsI a b h; rwa [← @nat.cast_inj R, ← hϕ.eq_iff, map_nat_cast ϕ, map_nat_cast ϕ]⟩,
  λ hS, by exactI ϕ.char_zero⟩

lemma ring_hom.injective_nat (f : ℕ →+* R) [char_zero R] :
  function.injective f :=
subsingleton.elim (nat.cast_ring_hom _) f ▸ nat.cast_injective

end ring_hom
