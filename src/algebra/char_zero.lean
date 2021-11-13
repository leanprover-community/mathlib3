/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import data.nat.cast
import data.fintype.basic
import tactic.wlog

/-!
# Characteristic zero

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main definition

`char_zero` is the typeclass of an additive monoid with one such that the natural homomorphism
from the natural numbers into it is injective.

## Main statements

* A linearly ordered semiring has characteristic zero.
* Characteristic zero implies that the additive monoid is infinite.

## TODO

* Once order of a group is defined for infinite additive monoids redefine or at least connect to
  order of `1` in the additive monoid with one.
* Unify with `char_p` (possibly using an out-parameter)
-/

/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.) -/
class char_zero (R : Type*) [add_monoid R] [has_one R] : Prop :=
(cast_injective : function.injective (coe : ℕ → R))

theorem char_zero_of_inj_zero {R : Type*} [add_left_cancel_monoid R] [has_one R]
  (H : ∀ n:ℕ, (n:R) = 0 → n = 0) : char_zero R :=
⟨λ m n, begin
   assume h,
   wlog hle : m ≤ n,
   rcases nat.le.dest hle with ⟨k, rfl⟩,
   rw [nat.cast_add, eq_comm, add_right_eq_self] at h,
   rw [H k h, add_zero]
 end⟩

/-- Note this is not an instance as `char_zero` implies `nontrivial`,
and this would risk forming a loop. -/
lemma ordered_semiring.to_char_zero {R : Type*} [ordered_semiring R] [nontrivial R] :
  char_zero R :=
⟨nat.strict_mono_cast.injective⟩

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_char_zero {R : Type*}
  [linear_ordered_semiring R] : char_zero R :=
ordered_semiring.to_char_zero

namespace nat
variables {R : Type*} [add_monoid R] [has_one R] [char_zero R]

theorem cast_injective : function.injective (coe : ℕ → R) :=
char_zero.cast_injective

/-- `nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def cast_embedding : ℕ ↪ R := ⟨coe, cast_injective⟩

@[simp, norm_cast] theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
cast_injective.eq_iff

@[simp, norm_cast] theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 :=
by rw [← cast_zero, cast_inj]

@[norm_cast] theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

lemma cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 :=
by exact_mod_cast n.succ_ne_zero

@[simp, norm_cast]
theorem cast_dvd_char_zero {k : Type*} [field k] [char_zero k] {m n : ℕ}
  (n_dvd : n ∣ m) : ((m / n : ℕ) : k) = m / n :=
begin
  by_cases hn : n = 0,
  { subst hn,
    simp },
  { exact cast_dvd n_dvd (cast_ne_zero.mpr hn), },
end

end nat

section

variables (M : Type*) [add_monoid M] [has_one M] [char_zero M]

@[priority 100] -- see Note [lower instance priority]
instance char_zero.infinite : infinite M :=
infinite.of_injective coe nat.cast_injective

variable {M}

@[field_simps] lemma two_ne_zero' : (2:M) ≠ 0 :=
have ((2:ℕ):M) ≠ 0, from nat.cast_ne_zero.2 dec_trivial,
by rwa [nat.cast_two] at this

end

section
variables {R : Type*} [semiring R] [no_zero_divisors R] [char_zero R]

@[simp]
lemma add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 :=
by simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero', false_or]

@[simp]
lemma bit0_eq_zero {a : R} : bit0 a = 0 ↔ a = 0 := add_self_eq_zero
@[simp]
lemma zero_eq_bit0 {a : R} : 0 = bit0 a ↔ a = 0 :=
by { rw [eq_comm], exact bit0_eq_zero }
end

section
variables {R : Type*} [ring R] [no_zero_divisors R] [char_zero R]

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
by rw [← mul_two, mul_div_cancel a two_ne_zero']

@[simp] lemma add_halves' (a : R) : a / 2 + a / 2 = a :=
by rw [← add_div, half_add_self]

lemma sub_half (a : R) : a - a / 2 = a / 2 :=
by rw [sub_eq_iff_eq_add, add_halves']

lemma half_sub (a : R) : a / 2 - a = - (a / 2) :=
by rw [← neg_sub, sub_half]

end

namespace with_top

instance {R : Type*} [add_monoid R] [has_one R] [char_zero R] : char_zero (with_top R) :=
{ cast_injective := λ m n h, by rwa [← coe_nat, ← coe_nat n, coe_eq_coe, nat.cast_inj] at h }

end with_top

section ring_hom

variables {R S : Type*} [semiring R] [semiring S]

lemma ring_hom.char_zero (ϕ : R →+* S) [hS : char_zero S] : char_zero R :=
⟨λ a b h, char_zero.cast_injective (by rw [←ϕ.map_nat_cast, ←ϕ.map_nat_cast, h])⟩

lemma ring_hom.char_zero_iff {ϕ : R →+* S} (hϕ : function.injective ϕ) :
  char_zero R ↔ char_zero S :=
⟨λ hR, ⟨λ a b h, by rwa [←@nat.cast_inj R _ _ hR, ←hϕ.eq_iff, ϕ.map_nat_cast, ϕ.map_nat_cast]⟩,
  λ hS, by exactI ϕ.char_zero⟩

end ring_hom
