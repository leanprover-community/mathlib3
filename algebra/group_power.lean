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
import algebra.char_zero data.int.basic algebra.group algebra.ordered_field data.list.basic

universe u
variable {α : Type u}

@[simp] theorem inv_one [division_ring α] : (1⁻¹ : α) = 1 := by rw [inv_eq_one_div, one_div_one]

@[simp] theorem inv_inv' [discrete_field α] {a:α} : a⁻¹⁻¹ = a :=
by rw [inv_eq_one_div, inv_eq_one_div, div_div_eq_mul_div]; simp [div_one]

/-- The power operation in a monoid. `a^n = a*a*...*a` n times. -/
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

@[simp] theorem pow_one (a : α) : a^1 = a := mul_one _
@[simp] theorem add_monoid.smul_one (a : β) : a•1 = a := add_zero _
attribute [to_additive add_monoid.smul_one] pow_one

@[to_additive smul_add_comm']
theorem pow_mul_comm' (a : α) (n : ℕ) : a^n * a = a * a^n :=
by induction n with n ih; simp [*, pow_succ, mul_assoc]

theorem pow_succ' (a : α) (n : ℕ) : a^(n+1) = a^n * a :=
by simp [pow_succ, pow_mul_comm']
theorem smul_succ' (a : β) (n : ℕ) : a•(n+1) = a•n + a :=
by simp [smul_succ, smul_add_comm']
attribute [to_additive smul_succ'] pow_succ'

theorem pow_two (a : α) : a^2 = a * a :=
by simp [pow_succ]
theorem smul_two (a : β) : a•2 = a + a :=
by simp [smul_succ]
attribute [to_additive smul_two] pow_two

@[to_additive add_monoid.smul_add]
theorem pow_add (a : α) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n; simp [*, pow_succ', nat.add_succ, mul_assoc]

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

@[simp] theorem add_monoid.one_smul [has_one β] : ∀ n, (1 : β) • n = n :=
nat.eq_cast _ (add_monoid.smul_zero _) (add_monoid.smul_one _) (add_monoid.smul_add _)

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
by induction q; [refl, simp [nat.pow_succ, pow_succ, mul_comm, *]]

@[simp] theorem nat.smul_eq_mul (m n : ℕ) : m • n = m * n :=
by induction n; simp [smul_succ', nat.mul_succ, *]

/- commutative monoid -/

section comm_monoid
variables [comm_monoid α] {β : Type*} [add_comm_monoid β]

theorem mul_pow (a b : α) : ∀ n, (a * b)^n = a^n * b^n
| 0     := by simp
| (n+1) := by simp [pow_succ, mul_assoc, mul_left_comm]; rw mul_pow
theorem add_monoid.add_smul (a b : β) : ∀ n, (a + b)•n = a•n + b•n
| 0     := by simp
| (n+1) := by simp [smul_succ]; rw add_monoid.add_smul
attribute [to_additive add_monoid.add_smul] mul_pow

end comm_monoid

section group
variables [group α] {β : Type*} [add_group β]

section nat

@[simp] theorem inv_pow (a : α) : ∀n, (a⁻¹)^n = (a^n)⁻¹
| 0     := by simp
| (n+1) := by rw [pow_succ', pow_succ, mul_inv_rev, inv_pow]
@[simp] theorem add_monoid.neg_smul (a : β) : ∀n, (-a)•n = -(a•n)
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

/--
The power operation in a group. This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
@[simp] def gpow (a : α) : ℤ → α
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹
attribute [to_additive gsmul._main] gpow._main
attribute [to_additive gsmul] gpow
attribute [to_additive gsmul._main.equations._eqn_1] gpow._main.equations._eqn_1
attribute [to_additive gsmul._main.equations._eqn_2] gpow._main.equations._eqn_2
attribute [simp, to_additive gsmul.equations._eqn_1] gpow.equations._eqn_1
attribute [simp, to_additive gsmul.equations._eqn_2] gpow.equations._eqn_2

@[simp, to_additive smul_coe_nat]
theorem gpow_coe_nat (a : α) (n : ℕ) : gpow a n = a ^ n := rfl

local attribute [ematch] le_of_lt
open nat

@[simp, to_additive gsmul_zero]
theorem gpow_zero (a : α) : gpow a 0 = 1 := rfl

@[simp] theorem gpow_one (a : α) : gpow a 1 = a := mul_one _
@[simp] theorem gsmul_one (a : β) : gsmul a 1 = a := add_zero _
attribute [to_additive gsmul_one] gpow_one

@[simp, to_additive zero_gsmul]
theorem one_gpow : ∀ (n : ℤ), gpow (1 : α) n = (1:α)
| (n : ℕ) := one_pow _
| -[1+ n] := by simp

@[simp] theorem gpow_neg (a : α) : ∀ (n : ℤ), gpow a (-n) = (gpow a n)⁻¹
| (n+1:ℕ) := rfl
| 0       := one_inv.symm
| -[1+ n] := (inv_inv _).symm
@[simp] theorem gsmul_neg (a : β) : ∀ (n : ℤ), gsmul a (-n) = -gsmul a n
| (n+1:ℕ) := rfl
| 0       := neg_zero.symm
| -[1+ n] := (neg_neg _).symm
attribute [to_additive gsmul_neg] gpow_neg

theorem gpow_neg_one (x : α) : gpow x (-1) = x⁻¹ := by simp
theorem gsmul_neg_one (x : β) : gsmul x (-1) = -x := by simp
attribute [to_additive gsmul_neg_one] gpow_neg_one

@[to_additive neg_gsmul]
theorem inv_gpow (a : α) : ∀n, gpow (a⁻¹) n = (gpow a n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := by simp [inv_pow]

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
by rw [← gpow_add, ← gpow_add, add_comm]

theorem gpow_mul (a : α) : ∀ m n : ℤ, gpow a (m * n) = gpow (gpow a m) n
| (m : ℕ) (n : ℕ) := pow_mul _ _ _
| (m : ℕ) -[1+ n] := (gpow_neg _ (m * succ n)).trans $
  show (a^ (m * succ n))⁻¹ = _, by rw pow_mul; refl
| -[1+ m] (n : ℕ) := (gpow_neg _ (succ m * n)).trans $
  show (a^ (succ m * n))⁻¹ = _, by simp [pow_mul]
| -[1+ m] -[1+ n] := (pow_mul a (succ m) (succ n)).trans $ by simp
theorem gsmul_mul (a : β) : ∀ m n : ℤ, gsmul a (m * n) = gsmul (gsmul a m) n
| (m : ℕ) (n : ℕ) := add_monoid.smul_mul _ _ _
| (m : ℕ) -[1+ n] := (gsmul_neg _ (m * succ n)).trans $
  show -(a•(m * succ n)) = _, by rw add_monoid.smul_mul; refl
| -[1+ m] (n : ℕ) := (gsmul_neg _ (succ m * n)).trans $
  show -(a•(succ m * n)) = _, by simp [add_monoid.smul_mul]
| -[1+ m] -[1+ n] := (add_monoid.smul_mul a (succ m) (succ n)).trans $ by simp
attribute [to_additive gsmul_mul] gpow_mul

@[to_additive gsmul_bit0]
theorem gpow_bit0 (a : α) (n : ℤ) : gpow a (bit0 n) = gpow a n * gpow a n := gpow_add _ _ _

theorem gpow_bit1 (a : α) (n : ℤ) : gpow a (bit1 n) = gpow a n * gpow a n * a :=
by rw [bit1, gpow_add]; simp [gpow_bit0]
theorem gsmul_bit1 (a : β) (n : ℤ) : gsmul a (bit1 n) = gsmul a n + gsmul a n + a :=
by rw [bit1, gsmul_add]; simp [gsmul_bit0]
attribute [to_additive gsmul_bit1] gpow_bit1

end group

theorem add_monoid.smul_eq_mul [semiring α] (a : α) : ∀ n, a • n = a * n
| 0 := by simp
| (n+1) := by simp [add_monoid.smul_eq_mul n, mul_add, smul_succ']

theorem add_monoid.smul_eq_mul' [semiring α] (a : α) (n) : a • n = n * a :=
by rw [add_monoid.smul_eq_mul, nat.mul_cast_comm]

theorem add_monoid.mul_smul_assoc [semiring α] (a b : α) (n) : (a * b) • n = a * b • n :=
by rw [add_monoid.smul_eq_mul, add_monoid.smul_eq_mul, mul_assoc]

theorem add_monoid.mul_smul_right [semiring α] (a b : α) (n) : (a * b) • n = a • n * b :=
by rw [add_monoid.smul_eq_mul', add_monoid.smul_eq_mul', mul_assoc]

theorem gsmul_eq_mul [ring α] (a : α) : ∀ n, gsmul a n = a * n
| (n : ℕ) := by simp [add_monoid.smul_eq_mul]
| -[1+ n] := by simp [add_monoid.smul_eq_mul, -add_comm, mul_add]

theorem gsmul_eq_mul' [ring α] (a : α) (n) : gsmul a n = n * a :=
by rw [gsmul_eq_mul, int.mul_cast_comm]

theorem mul_gsmul_assoc [ring α] (a b : α) (n) : gsmul (a * b) n = a * gsmul b n :=
by rw [gsmul_eq_mul, gsmul_eq_mul, mul_assoc]

theorem mul_gsmul_right [ring α] (a b : α) (n) : gsmul (a * b) n = gsmul a n * b :=
by rw [gsmul_eq_mul', gsmul_eq_mul', mul_assoc]

theorem pow_ne_zero [domain α] {a : α} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
by induction n with n ih; simp [pow_succ, mul_eq_zero, *]

@[simp] theorem one_div_pow [division_ring α] {a : α} (ha : a ≠ 0) : ∀ n, (1 / a) ^ n = 1 / a ^ n
| 0     := by simp
| (n+1) := by rw [pow_succ', pow_succ,
  ← division_ring.one_div_mul_one_div (pow_ne_zero n ha) ha, one_div_pow]

@[simp] theorem division_ring.inv_pow [division_ring α] {a : α} (ha : a ≠ 0) (n) : a⁻¹ ^ n = (a ^ n)⁻¹ :=
by simp [inv_eq_one_div, -one_div_eq_inv, ha]

@[simp] theorem div_pow [field α] (a : α) {b : α} (hb : b ≠ 0) (n) : (a / b) ^ n = a ^ n / b ^ n :=
by rw [div_eq_mul_one_div, mul_pow, one_div_pow hb, ← div_eq_mul_one_div]

theorem add_monoid.smul_nonneg [ordered_comm_monoid α] {a : α} (H : 0 ≤ a) : ∀ n, 0 ≤ a • n
| 0     := le_refl _
| (n+1) := add_nonneg' H (add_monoid.smul_nonneg n)

lemma pow_abs [decidable_linear_ordered_comm_ring α] (a : α) (n) : (abs a)^n = abs (a^n) := 
by induction n; simp [*, monoid.pow, abs_mul]

lemma pow_inv [division_ring α] (a : α) : ∀ n, a ≠ 0 → (a^n)⁻¹ = (a⁻¹)^n
| 0     ha := by simp [pow_zero]
| (n+1) ha := by rw [pow_succ, pow_succ', mul_inv_eq (pow_ne_zero _ ha) ha, pow_inv _ ha]

section linear_ordered_semiring
variable [linear_ordered_semiring α]

theorem pow_pos {a : α} (H : 0 < a) : ∀ (n : ℕ), 0 < a ^ n
| 0     := by simp [zero_lt_one]
| (n+1) := by simpa [pow_succ] using mul_pos H (pow_pos _)

theorem pow_nonneg {a : α} (H : 0 ≤ a) : ∀ (n : ℕ), 0 ≤ a ^ n
| 0     := by simp [zero_le_one]
| (n+1) := by simpa [pow_succ] using mul_nonneg H (pow_nonneg _)

theorem one_le_pow_of_one_le {a : α} (H : 1 ≤ a) : ∀ (n : ℕ), 1 ≤ a ^ n
| 0     := by simp; apply le_refl
| (n+1) :=
  begin
   simp [pow_succ], rw ← one_mul (1 : α),
   apply mul_le_mul,
   assumption,
   apply one_le_pow_of_one_le,
   apply zero_le_one,
   transitivity, apply zero_le_one, assumption
  end

theorem pow_ge_one_add_mul {a : α} (H : a ≥ 0) :
  ∀ (n : ℕ), 1 + a • n ≤ (1 + a) ^ n
| 0     := by simp
| (n+1) := begin
  rw [pow_succ', smul_succ'],
  refine le_trans _ (mul_le_mul_of_nonneg_right
    (pow_ge_one_add_mul n) (add_nonneg zero_le_one H)),
  rw [mul_add, mul_one, ← add_assoc, add_le_add_iff_left],
  simpa using mul_le_mul_of_nonneg_right
    ((le_add_iff_nonneg_right 1).2 (add_monoid.smul_nonneg H n)) H
end

theorem pow_le_pow {a : α} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
let ⟨k, hk⟩ := nat.le.dest h in
calc a ^ n = a ^ n * 1 : by simp
  ... ≤ a ^ n * a ^ k : mul_le_mul_of_nonneg_left
    (one_le_pow_of_one_le ha _)
    (pow_nonneg (le_trans zero_le_one ha) _)
  ... = a ^ m : by rw [←hk, pow_add]

end linear_ordered_semiring

theorem pow_ge_one_add_sub_mul [linear_ordered_ring α]
  {a : α} (H : a ≥ 1) (n : ℕ) : 1 + (a - 1) • n ≤ a ^ n :=
by simpa using pow_ge_one_add_mul (sub_nonneg.2 H) n
