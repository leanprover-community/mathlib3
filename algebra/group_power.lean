/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis

The power operation on monoids and groups. We separate this from group, because it depends on
nat, which in turn depends on other parts of algebra.

We have "pow a n" for natural number powers, and "gpow a i" for integer powers. The notation
a^n is used for the first, but users can locally redefine it to gpow when needed.

Note: power adopts the convention that 0^0=1.
-/
import data.nat.basic data.int.basic algebra.group

local attribute [simp] mul_comm mul_assoc mul_left_comm

universe u
variable {α : Type u}

@[simp] theorem inv_one [division_ring α] : (1⁻¹ : α) = 1 := by rw [inv_eq_one_div, one_div_one]

@[simp] theorem inv_inv' [discrete_field α] {a:α} : a⁻¹⁻¹ = a :=
by rw [inv_eq_one_div, inv_eq_one_div, div_div_eq_mul_div]; simp [div_one]

def monoid.pow [monoid α] (a : α) : ℕ → α
| 0     := 1
| (n+1) := a * monoid.pow n
attribute [to_additive add_monoid.smul._main] monoid.pow._main
attribute [to_additive add_monoid.smul] monoid.pow

local infix ` ^ ` := monoid.pow
local infix ` • `:73 := add_monoid.smul

 /- monoid -/
section monoid
variables [monoid α] {β : Type u} [add_monoid β]

@[simp, to_additive add_monoid.smul_zero]
theorem pow_zero (a : α) : a^0 = 1 := rfl

theorem pow_succ (a : α) (n : ℕ) : a^(n+1) = a * a^n := rfl
theorem smul_succ (a : β) (n : ℕ) : a•(n+1) = a + a • n := rfl
attribute [to_additive smul_succ] pow_succ

theorem pow_one (a : α) : a^1 = a := mul_one _
theorem add_monoid.smul_one (a : β) : a•1 = a := add_zero _
attribute [to_additive add_monoid.smul_one] pow_one

@[to_additive smul_add_comm']
theorem pow_mul_comm' (a : α) (n : ℕ) : a^n * a = a * a^n :=
by induction n with n ih; simp [*, pow_succ]

theorem pow_succ' (a : α) (n : ℕ) : a^(n+1) = a^n * a :=
by simp [pow_succ, pow_mul_comm']
theorem smul_succ' (a : β) (n : ℕ) : a•(n+1) = a•n + a :=
by simp [smul_succ, smul_add_comm']
attribute [to_additive smul_succ'] pow_succ'

@[to_additive add_monoid.smul_add]
theorem pow_add (a : α) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n; simp [*, pow_succ', nat.add_succ]

@[simp] theorem one_pow (n : ℕ) : (1 : α)^n = (1:α) :=
by induction n; simp [*, pow_succ]
@[simp] theorem add_monoid.zero_smul (n : ℕ) : (0 : β)•n = (0:β) :=
by induction n; simp [*, smul_succ]
attribute [to_additive add_monoid.zero_smul] one_pow

theorem pow_mul (a : α) (m : ℕ) : ∀ n, a^(m * n) = (a^m)^n
| 0     := by simp
| (n+1) := by rw [nat.mul_succ, pow_add, pow_succ', pow_mul]
theorem add_monoid.smul_mul (a : β) (m : ℕ) : ∀ n, a•(m * n) = (a•m)•n
| 0     := by simp
| (n+1) := by rw [nat.mul_succ, add_monoid.smul_add, smul_succ', add_monoid.smul_mul]
attribute [to_additive add_monoid.smul_mul] pow_mul

@[to_additive smul_bit0]
theorem pow_bit0 (a : α) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _

theorem pow_bit1 (a : α) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]
theorem smul_bit1 (a : β) (n : ℕ) : a • bit1 n = a•n + a•n + a :=
by rw [bit1, smul_succ', smul_bit0]
attribute [to_additive smul_bit1] pow_bit1

@[to_additive smul_add_comm]
theorem pow_mul_comm (a : α) (m n : ℕ)  : a^m * a^n = a^n * a^m :=
by rw [←pow_add, ←pow_add, add_comm]

@[simp] theorem list.prod_repeat (a : α) : ∀ (n : ℕ), (list.repeat a n).prod = a ^ n
| 0 := rfl
| (n+1) := by simp [pow_succ, list.prod_repeat n]
@[simp] theorem list.sum_repeat (a : β) : ∀ (n : ℕ), (list.repeat a n).sum = a • n
| 0 := rfl
| (n+1) := by simp [smul_succ, list.sum_repeat n]
attribute [to_additive list.sum_repeat] list.prod_repeat

end monoid

theorem nat.pow_eq_pow (p q : ℕ) : nat.pow p q = p ^ q :=
by induction q; [refl, simp [nat.pow_succ, pow_succ, *]]

/- commutative monoid -/

section comm_monoid
variables [comm_monoid α] {β : Type*} [add_comm_monoid β]

theorem mul_pow (a b : α) : ∀ n, (a * b)^n = a^n * b^n
| 0     := by simp
| (n+1) := by simp [pow_succ]; rw mul_pow
theorem add_monoid.add_smul (a b : β) : ∀ n, (a + b)•n = a•n + b•n
| 0     := by simp
| (n+1) := by simp [smul_succ]; rw add_monoid.add_smul
attribute [to_additive add_monoid.add_smul] mul_pow

end comm_monoid

section group
variables [group α] {β : Type*} [add_group β]

section nat

theorem inv_pow (a : α) : ∀n, (a⁻¹)^n = (a^n)⁻¹
| 0     := by simp
| (n+1) := by rw [pow_succ', pow_succ, mul_inv_rev, inv_pow]
theorem add_monoid.neg_smul (a : β) : ∀n, (-a)•n = -(a•n)
| 0     := by simp
| (n+1) := by rw [smul_succ', smul_succ, neg_add_rev, add_monoid.neg_smul]
attribute [to_additive add_monoid.neg_smul] inv_pow

@[to_additive add_monoid.smul_sub]
theorem pow_sub (a : α) {m n : ℕ} (h : m ≥ n) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq h2

@[to_additive add_monoid.smul_neg_comm]
theorem pow_inv_comm (a : α) (m n) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
by rw inv_pow; exact inv_comm_of_comm (pow_mul_comm _ _ _)
end nat

open int

def gpow (a : α) : ℤ → α
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹
attribute [to_additive gsmul._main] gpow._main
attribute [to_additive gsmul] gpow
attribute [to_additive gsmul._main.equations._eqn_1] gpow._main.equations._eqn_1
attribute [to_additive gsmul._main.equations._eqn_2] gpow._main.equations._eqn_2
attribute [to_additive gsmul.equations._eqn_1] gpow.equations._eqn_1
attribute [to_additive gsmul.equations._eqn_2] gpow.equations._eqn_2

local attribute [ematch] le_of_lt
open nat

@[to_additive gsmul_add_aux]
private lemma gpow_add_aux (a : α) (m n : nat) :
  gpow a ((of_nat m) + -[1+n]) = gpow a (of_nat m) * gpow a (-[1+n]) :=
or.elim (nat.lt_or_ge m (nat.succ n))
 (assume : m < succ n,
  have m ≤ n, from le_of_lt_succ this,
  suffices gpow a -[1+ n-m] = (gpow a (of_nat m)) * (gpow a -[1+n]), by simp [*, of_nat_add_neg_succ_of_nat_of_lt],
  suffices (a^(nat.succ (n - m)))⁻¹ = (gpow a (of_nat m)) * (gpow a -[1+n]), from this,
  suffices (a^(nat.succ n - m))⁻¹ = (gpow a (of_nat m)) * (gpow a -[1+n]), by rw ←succ_sub; assumption,
  by rw pow_sub; finish [gpow])
 (assume : m ≥ succ n,
  suffices gpow a (of_nat (m - succ n)) = (gpow a (of_nat m)) * (gpow a -[1+ n]),
    by rw [of_nat_add_neg_succ_of_nat_of_ge]; assumption,
  suffices a ^ (m - succ n) = a^m * (a^succ n)⁻¹, from this,
  by rw pow_sub; assumption)

@[to_additive gsmul_add]
theorem gpow_add (a : α) : ∀i j : int, gpow a (i + j) = gpow a i * gpow a j
| (of_nat m) (of_nat n) := pow_add _ _ _
| (of_nat m) -[1+n]     := gpow_add_aux _ _ _
| -[1+m]     (of_nat n) := begin rw [add_comm, gpow_add_aux], unfold gpow, rw [←inv_pow, pow_inv_comm] end
| -[1+m]     -[1+n]     :=
  suffices (a ^ (m + succ (succ n)))⁻¹ = (a ^ succ m)⁻¹ * (a ^ succ n)⁻¹, from this,
  by rw [←succ_add_eq_succ_add, add_comm, _root_.pow_add, mul_inv_rev]

@[to_additive gsmul_add_comm]
theorem gpow_mul_comm (a : α) (i j : ℤ) : gpow a i * gpow a j = gpow a j * gpow a i :=
by rw [←gpow_add, ←gpow_add, add_comm]
end group

theorem pow_ne_zero [integral_domain α] {a : α} {n : ℕ} (h : a ≠ 0) : a ^ n ≠ 0 :=
by induction n with n ih; simp [pow_succ, mul_eq_zero_iff_eq_zero_or_eq_zero, *]

section discrete_field
variables [discrete_field α] {a b c : α} {n : ℕ}

theorem pow_inv (ha : a ≠ 0) : a⁻¹ ^ n = (a ^ n)⁻¹ :=
by induction n with n ih; simp [pow_succ, mul_inv', pow_ne_zero, *]

end discrete_field

section ordered_ring
variable [linear_ordered_ring α]

theorem pow_pos {a : α} (H : a > 0) : ∀ (n : ℕ), a ^ n > 0
| 0     := by simp; apply zero_lt_one
| (n+1) := begin simp [_root_.pow_succ], apply mul_pos, assumption, apply pow_pos end

theorem pow_nonneg {a : α} (H : a ≥ 0) : ∀ (n : ℕ), a ^ n ≥ 0
| 0     := by simp; apply zero_le_one
| (n+1) := begin simp [_root_.pow_succ], apply mul_nonneg, assumption, apply pow_nonneg end

theorem pow_ge_one_of_ge_one {a : α} (H : a ≥ 1) : ∀ (n : ℕ), a ^ n ≥ 1
| 0     := by simp; apply le_refl
| (n+1) :=
  begin
   simp [_root_.pow_succ], rw ←(one_mul (1 : α)),
   apply mul_le_mul,
   assumption,
   apply pow_ge_one_of_ge_one,
   apply zero_le_one,
   transitivity, apply zero_le_one, assumption
  end

theorem pow_le_pow {a : α} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
let ⟨k, hk⟩ := nat.le.dest h in
calc a ^ n = a ^ n * 1 : by simp
  ... ≤ a ^ n * a ^ k : mul_le_mul_of_nonneg_left
    (pow_ge_one_of_ge_one ha _)
    (pow_nonneg (le_trans zero_le_one ha) _)
  ... = a ^ m : by rw [←hk, pow_add]

end ordered_ring
