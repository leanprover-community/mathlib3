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

universes u v
variable {α : Type u}

@[simp] theorem inv_one [division_ring α] : (1⁻¹ : α) = 1 := by rw [inv_eq_one_div, one_div_one]

@[simp] theorem inv_inv' [discrete_field α] {a:α} : a⁻¹⁻¹ = a :=
by rw [inv_eq_one_div, inv_eq_one_div, div_div_eq_mul_div]; simp [div_one]

/-- The power operation in a monoid. `a^n = a*a*...*a` n times. -/
def monoid.pow [monoid α] (a : α) : ℕ → α
| 0     := 1
| (n+1) := a * monoid.pow n

def add_monoid.smul [add_monoid α] (n : ℕ) (a : α) : α :=
@monoid.pow (multiplicative α) _ a n

precedence `•`:70
local infix ` • ` := add_monoid.smul

@[priority 5] instance monoid.has_pow [monoid α] : has_pow α ℕ := ⟨monoid.pow⟩

 /- monoid -/
section monoid
variables [monoid α] {β : Type u} [add_monoid β]

@[simp] theorem pow_zero (a : α) : a^0 = 1 := rfl
@[simp] theorem add_monoid.zero_smul (a : β) : 0 • a = 0 := rfl
attribute [to_additive add_monoid.zero_smul] pow_zero

theorem pow_succ (a : α) (n : ℕ) : a^(n+1) = a * a^n := rfl
theorem succ_smul (a : β) (n : ℕ) : (n+1)•a = a + n•a := rfl
attribute [to_additive succ_smul] pow_succ

@[simp] theorem pow_one (a : α) : a^1 = a := mul_one _
@[simp] theorem add_monoid.one_smul (a : β) : 1•a = a := add_zero _
attribute [to_additive add_monoid.one_smul] pow_one

theorem pow_mul_comm' (a : α) (n : ℕ) : a^n * a = a * a^n :=
by induction n with n ih; simp [*, pow_succ, mul_assoc]
theorem smul_add_comm' : ∀ (a : β) (n : ℕ), n•a + a = a + n•a :=
@pow_mul_comm' (multiplicative β) _

theorem pow_succ' (a : α) (n : ℕ) : a^(n+1) = a^n * a :=
by simp [pow_succ, pow_mul_comm']
theorem succ_smul' (a : β) (n : ℕ) : (n+1)•a = n•a + a :=
by simp [succ_smul, smul_add_comm']
attribute [to_additive succ_smul'] pow_succ'

theorem pow_two (a : α) : a^2 = a * a :=
by simp [pow_succ]
theorem two_smul (a : β) : 2•a = a + a :=
by simp [succ_smul]
attribute [to_additive two_smul] pow_two

theorem pow_add (a : α) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n; simp [*, pow_succ', nat.add_succ, mul_assoc]
theorem add_monoid.add_smul : ∀ (a : β) (m n : ℕ), (m + n)•a = m•a + n•a :=
@pow_add (multiplicative β) _
attribute [to_additive add_monoid.add_smul] pow_add

@[simp] theorem one_pow (n : ℕ) : (1 : α)^n = (1:α) :=
by induction n; simp [*, pow_succ]
@[simp] theorem add_monoid.smul_zero (n : ℕ) : n•(0 : β) = (0:β) :=
by induction n; simp [*, succ_smul]
attribute [to_additive add_monoid.smul_zero] one_pow

theorem pow_mul (a : α) (m : ℕ) : ∀ n, a^(m * n) = (a^m)^n
| 0     := by simp
| (n+1) := by rw [nat.mul_succ, pow_add, pow_succ', pow_mul]
theorem add_monoid.mul_smul' : ∀ (a : β) (m n : ℕ), m * n • a = n•(m•a) :=
@pow_mul (multiplicative β) _
attribute [to_additive add_monoid.mul_smul'] pow_mul

theorem pow_mul' (a : α) (m n : ℕ) : a^(m * n) = (a^n)^m :=
by rw [mul_comm, pow_mul]
theorem add_monoid.mul_smul (a : β) (m n : ℕ) : m * n • a = m•(n•a) :=
by rw [mul_comm, add_monoid.mul_smul']
attribute [to_additive add_monoid.mul_smul] pow_mul'

@[simp] theorem add_monoid.smul_one [has_one β] : ∀ n : ℕ, n • (1 : β) = n :=
nat.eq_cast _ (add_monoid.zero_smul _) (add_monoid.one_smul _) (add_monoid.add_smul _)

theorem pow_bit0 (a : α) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _
theorem bit0_smul (a : β) (n : ℕ) : bit0 n • a = n•a + n•a := add_monoid.add_smul _ _ _
attribute [to_additive bit0_smul] pow_bit0

theorem pow_bit1 (a : α) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]
theorem bit1_smul : ∀ (a : β) (n : ℕ), bit1 n • a = n•a + n•a + a :=
@pow_bit1 (multiplicative β) _
attribute [to_additive bit1_smul] pow_bit1

theorem pow_mul_comm (a : α) (m n : ℕ) : a^m * a^n = a^n * a^m :=
by rw [←pow_add, ←pow_add, add_comm]
theorem smul_add_comm : ∀ (a : β) (m n : ℕ), m•a + n•a = n•a + m•a :=
@pow_mul_comm (multiplicative β) _
attribute [to_additive smul_add_comm] pow_mul_comm

@[simp] theorem list.prod_repeat (a : α) : ∀ (n : ℕ), (list.repeat a n).prod = a ^ n
| 0 := rfl
| (n+1) := by simp [pow_succ, list.prod_repeat n]
@[simp] theorem list.sum_repeat : ∀ (a : β) (n : ℕ), (list.repeat a n).sum = n • a :=
@list.prod_repeat (multiplicative β) _
attribute [to_additive list.sum_repeat] list.prod_repeat

end monoid

@[simp] theorem nat.pow_eq_pow (p q : ℕ) :
  @has_pow.pow _ _ monoid.has_pow p q = p ^ q :=
by induction q; [refl, simp [nat.pow_succ, pow_succ, mul_comm, *]]

@[simp] theorem nat.smul_eq_mul (m n : ℕ) : m • n = m * n :=
by rw mul_comm; induction m; simp [succ_smul', nat.mul_succ, *]

/- commutative monoid -/

section comm_monoid
variables [comm_monoid α] {β : Type*} [add_comm_monoid β]

theorem mul_pow (a b : α) : ∀ n:ℕ, (a * b)^n = a^n * b^n
| 0     := by simp
| (n+1) := by simp [pow_succ, mul_assoc, mul_left_comm]; rw mul_pow
theorem add_monoid.smul_add : ∀ (a b : β) (n : ℕ), n•(a + b) = n•a + n•b :=
@mul_pow (multiplicative β) _
attribute [to_additive add_monoid.add_smul] mul_pow

end comm_monoid

section group
variables [group α] {β : Type*} [add_group β]

section nat

@[simp] theorem inv_pow (a : α) : ∀n:ℕ, (a⁻¹)^n = (a^n)⁻¹
| 0     := by simp
| (n+1) := by rw [pow_succ', pow_succ, mul_inv_rev, inv_pow]
@[simp] theorem add_monoid.neg_smul : ∀ (a : β) (n : ℕ), n•(-a) = -(n•a) :=
@inv_pow (multiplicative β) _
attribute [to_additive add_monoid.neg_smul] inv_pow

theorem pow_sub (a : α) {m n : ℕ} (h : m ≥ n) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq h2
theorem add_monoid.smul_sub : ∀ (a : β) {m n : ℕ}, m ≥ n → (m - n)•a = m•a - n•a :=
@pow_sub (multiplicative β) _
attribute [to_additive add_monoid.smul_sub] inv_pow

theorem pow_inv_comm (a : α) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
by rw inv_pow; exact inv_comm_of_comm (pow_mul_comm _ _ _)
theorem add_monoid.smul_neg_comm : ∀ (a : β) (m n : ℕ), m•(-a) + n•a = n•a + m•(-a) :=
@pow_inv_comm (multiplicative β) _
attribute [to_additive add_monoid.smul_neg_comm] pow_inv_comm
end nat

open int

/--
The power operation in a group. This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
def gpow (a : α) : ℤ → α
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

def gsmul (n : ℤ) (a : β) : β :=
@gpow (multiplicative β) _ a n

@[priority 10] instance group.has_pow : has_pow α ℤ := ⟨gpow⟩

local infix ` • `:70 := gsmul
local infix ` •ℕ `:70 := add_monoid.smul

@[simp] theorem gpow_coe_nat (a : α) (n : ℕ) : a ^ (n:ℤ) = a ^ n := rfl
@[simp] theorem gsmul_coe_nat (a : β) (n : ℕ) : (n:ℤ) • a = n •ℕ a := rfl
attribute [to_additive gsmul_coe_nat] gpow_coe_nat

@[simp] theorem gpow_of_nat (a : α) (n : ℕ) : a ^ of_nat n = a ^ n := rfl
@[simp] theorem gsmul_of_nat (a : β) (n : ℕ) : of_nat n • a = n •ℕ a := rfl
attribute [to_additive gsmul_of_nat] gpow_of_nat

@[simp] theorem gpow_neg_succ (a : α) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl
@[simp] theorem gsmul_neg_succ (a : β) (n : ℕ) : -[1+n] • a = - (n.succ •ℕ a) := rfl
attribute [to_additive gsmul_neg_succ] gpow_neg_succ

local attribute [ematch] le_of_lt
open nat

@[simp] theorem gpow_zero (a : α) : a ^ (0:ℤ) = 1 := rfl
@[simp] theorem zero_gsmul (a : β) : (0:ℤ) • a = 0 := rfl
attribute [to_additive zero_gsmul] gpow_zero

@[simp] theorem gpow_one (a : α) : a ^ (1:ℤ) = a := mul_one _
@[simp] theorem one_gsmul (a : β) : (1:ℤ) • a = a := add_zero _
attribute [to_additive one_gsmul] gpow_one

@[simp] theorem one_gpow : ∀ (n : ℤ), (1 : α) ^ n = 1
| (n : ℕ) := one_pow _
| -[1+ n] := by simp
@[simp] theorem gsmul_zero : ∀ (n : ℤ), n • (0 : β) = 0 :=
@one_gpow (multiplicative β) _
attribute [to_additive gsmul_zero] one_gpow

@[simp] theorem gpow_neg (a : α) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := rfl
| 0       := one_inv.symm
| -[1+ n] := (inv_inv _).symm
@[simp] theorem neg_gsmul : ∀ (a : β) (n : ℤ), -n • a = -(n • a) :=
@gpow_neg (multiplicative β) _
attribute [to_additive neg_gsmul] gpow_neg

theorem gpow_neg_one (x : α) : x ^ (-1:ℤ) = x⁻¹ := by simp
theorem neg_one_gsmul (x : β) : (-1:ℤ) • x = -x := by simp
attribute [to_additive neg_one_gsmul] gpow_neg_one

@[to_additive neg_gsmul]
theorem inv_gpow (a : α) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := by simp [inv_pow]

private lemma gpow_add_aux (a : α) (m n : nat) :
  a ^ ((of_nat m) + -[1+n]) = a ^ of_nat m * a ^ -[1+n] :=
or.elim (nat.lt_or_ge m (nat.succ n))
 (assume : m < succ n,
  have m ≤ n, from le_of_lt_succ this,
  suffices a ^ -[1+ n-m] = a ^ of_nat m * a ^ -[1+n], by simp [*, of_nat_add_neg_succ_of_nat_of_lt],
  suffices (a ^ nat.succ (n - m))⁻¹ = a ^ of_nat m * a ^ -[1+n], from this,
  suffices (a ^ (nat.succ n - m))⁻¹ = a ^ of_nat m * a ^ -[1+n], by rw ←succ_sub; assumption,
  by rw pow_sub; finish [gpow])
 (assume : m ≥ succ n,
  suffices a ^ (of_nat (m - succ n)) = (a ^ (of_nat m)) * (a ^ -[1+ n]),
    by rw [of_nat_add_neg_succ_of_nat_of_ge]; assumption,
  suffices a ^ (m - succ n) = a ^ m * (a ^ n.succ)⁻¹, from this,
  by rw pow_sub; assumption)

theorem gpow_add (a : α) : ∀ (i j : ℤ), a ^ (i + j) = a ^ i * a ^ j
| (of_nat m) (of_nat n) := pow_add _ _ _
| (of_nat m) -[1+n]     := gpow_add_aux _ _ _
| -[1+m]     (of_nat n) := by rw [add_comm, gpow_add_aux,
  gpow_neg_succ, gpow_of_nat, ← inv_pow, ← pow_inv_comm]
| -[1+m]     -[1+n]     :=
  suffices (a ^ (m + succ (succ n)))⁻¹ = (a ^ m.succ)⁻¹ * (a ^ n.succ)⁻¹, from this,
  by rw [← succ_add_eq_succ_add, add_comm, _root_.pow_add, mul_inv_rev]

theorem add_gsmul : ∀ (a : β) (i j : ℤ), (i + j) • a = i • a + j • a :=
@gpow_add (multiplicative β) _

theorem gpow_mul_comm (a : α) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
by rw [← gpow_add, ← gpow_add, add_comm]
theorem gsmul_add_comm : ∀ (a : β) (i j), i • a + j • a = j • a + i • a :=
@gpow_mul_comm (multiplicative β) _
attribute [to_additive gsmul_add_comm] gpow_mul_comm

theorem gpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := pow_mul _ _ _
| (m : ℕ) -[1+ n] := (gpow_neg _ (m * succ n)).trans $
  show (a ^ (m * succ n))⁻¹ = _, by rw pow_mul; refl
| -[1+ m] (n : ℕ) := (gpow_neg _ (succ m * n)).trans $
  show (a ^ (m.succ * n))⁻¹ = _, by simp [pow_mul]
| -[1+ m] -[1+ n] := (pow_mul a (succ m) (succ n)).trans $ by simp
theorem gsmul_mul' : ∀ (a : β) (m n : ℤ), m * n • a = n • (m • a) :=
@gpow_mul (multiplicative β) _
attribute [to_additive gsmul_mul'] gpow_mul

theorem gpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, gpow_mul]
theorem gsmul_mul (a : β) (m n : ℤ) : m * n • a = m • (n • a) :=
by rw [mul_comm, gsmul_mul']
attribute [to_additive gsmul_mul] gpow_mul'

theorem gpow_bit0 (a : α) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n := gpow_add _ _ _
theorem bit0_gsmul (a : β) (n : ℤ) : bit0 n • a = n • a + n • a := gpow_add _ _ _
attribute [to_additive bit0_gsmul] gpow_bit0

theorem gpow_bit1 (a : α) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
by rw [bit1, gpow_add]; simp [gpow_bit0]
theorem bit1_gsmul : ∀ (a : β) (n : ℤ), bit1 n • a = n • a + n • a + a :=
@gpow_bit1 (multiplicative β) _
attribute [to_additive bit1_gsmul] gpow_bit1

end group

namespace is_group_hom
variables {β : Type v} [group α] [group β] (f : α → β) [is_group_hom f]

theorem pow (a : α) (n : ℕ) : f (a ^ n) = f a ^ n :=
by induction n; simp [*, pow_succ, is_group_hom.mul f, is_group_hom.one f]

theorem gpow (a : α) (n : ℤ) : f (a ^ n) = f a ^ n :=
by cases n; simp [is_group_hom.pow f, is_group_hom.inv f]

end is_group_hom

local infix ` •ℤ `:70 := gsmul

section comm_monoid
variables [comm_group α] {β : Type*} [add_comm_group β]

theorem mul_gpow (a b : α) : ∀ n:ℤ, (a * b)^n = a^n * b^n
| (n : ℕ) := mul_pow a b n
| -[1+ n] := by simp [pow_succ, mul_pow, mul_inv, mul_comm, mul_left_comm]
theorem gsmul_add : ∀ (a b : β) (n : ℤ), n •ℤ (a + b) = n •ℤ a + n •ℤ b :=
@mul_gpow (multiplicative β) _
attribute [to_additive gsmul_add] mul_gpow

end comm_monoid

theorem add_monoid.smul_eq_mul' [semiring α] (a : α) : ∀ n : ℕ, n • a = a * n
| 0 := by simp
| (n+1) := by simp [add_monoid.smul_eq_mul' n, mul_add, succ_smul']

theorem add_monoid.smul_eq_mul [semiring α] (n : ℕ) (a : α) : n • a = n * a :=
by rw [add_monoid.smul_eq_mul', nat.mul_cast_comm]

theorem add_monoid.mul_smul_left [semiring α] (a b : α) (n : ℕ) : n • (a * b) = a * (n • b) :=
by rw [add_monoid.smul_eq_mul', add_monoid.smul_eq_mul', mul_assoc]

theorem add_monoid.mul_smul_assoc [semiring α] (a b : α) (n : ℕ) : n • (a * b) = n • a * b :=
by rw [add_monoid.smul_eq_mul, add_monoid.smul_eq_mul, mul_assoc]

lemma zero_pow [semiring α] : ∀ {n : ℕ}, 0 < n → (0 : α) ^ n = 0
| (n+1) _ := zero_mul _

@[simp] theorem nat.cast_pow [semiring α] (n m : ℕ) : (↑(n ^ m) : α) = ↑n ^ m :=
by induction m; simp [*, nat.succ_eq_add_one, nat.pow_add, pow_add]

@[simp] theorem int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m :=
by induction m; simp [*, pow_succ', nat.pow_succ]

theorem is_semiring_hom.map_pow {β} [semiring α] [semiring β]
  (f : α → β) [is_semiring_hom f] (x : α) (n : ℕ) : f (x ^ n) = f x ^ n :=
by induction n; simp [*, is_semiring_hom.map_one f, is_semiring_hom.map_mul f, pow_succ]

theorem neg_one_pow_eq_or {R} [ring R] : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := by simp
| (n+1) := by cases neg_one_pow_eq_or n; simp [pow_succ, h]

theorem gsmul_eq_mul [ring α] (a : α) : ∀ n, n •ℤ a = n * a
| (n : ℕ) := by simp [add_monoid.smul_eq_mul]
| -[1+ n] := by simp [add_monoid.smul_eq_mul, -add_comm, add_mul]

theorem gsmul_eq_mul' [ring α] (a : α) (n : ℤ) : n •ℤ a = a * n :=
by rw [gsmul_eq_mul, int.mul_cast_comm]

theorem mul_gsmul_left [ring α] (a b : α) (n : ℤ) : n •ℤ (a * b) = a * (n •ℤ b) :=
by rw [gsmul_eq_mul', gsmul_eq_mul', mul_assoc]

theorem mul_gsmul_assoc [ring α] (a b : α) (n : ℤ) : n •ℤ (a * b) = n •ℤ a * b :=
by rw [gsmul_eq_mul, gsmul_eq_mul, mul_assoc]

@[simp] theorem int.cast_pow [ring α] (n : ℤ) (m : ℕ) : (↑(n ^ m) : α) = ↑n ^ m :=
by induction m; simp [*, nat.succ_eq_add_one,pow_add]

theorem pow_ne_zero [domain α] {a : α} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
by induction n with n ih; simp [pow_succ, mul_eq_zero, *]

@[simp] theorem one_div_pow [division_ring α] {a : α} (ha : a ≠ 0) : ∀ n : ℕ, (1 / a) ^ n = 1 / a ^ n
| 0     := by simp
| (n+1) := by rw [pow_succ', pow_succ,
  ← division_ring.one_div_mul_one_div (pow_ne_zero n ha) ha, one_div_pow]

@[simp] theorem division_ring.inv_pow [division_ring α] {a : α} (ha : a ≠ 0) (n : ℕ) : a⁻¹ ^ n = (a ^ n)⁻¹ :=
by simp [inv_eq_one_div, -one_div_eq_inv, ha]

@[simp] theorem div_pow [field α] (a : α) {b : α} (hb : b ≠ 0) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n :=
by rw [div_eq_mul_one_div, mul_pow, one_div_pow hb, ← div_eq_mul_one_div]

theorem add_monoid.smul_nonneg [ordered_comm_monoid α] {a : α} (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ n • a
| 0     := le_refl _
| (n+1) := add_nonneg' H (add_monoid.smul_nonneg n)

lemma pow_abs [decidable_linear_ordered_comm_ring α] (a : α) (n : ℕ) : (abs a)^n = abs (a^n) :=
by induction n; simp [*, pow_succ, abs_mul]

lemma pow_inv [division_ring α] (a : α) : ∀ n : ℕ, a ≠ 0 → (a^n)⁻¹ = (a⁻¹)^n
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
  ∀ (n : ℕ), 1 + n • a ≤ (1 + a) ^ n
| 0     := by simp
| (n+1) := begin
  rw [pow_succ', succ_smul'],
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

theorem pow_two_nonneg [linear_ordered_ring α] (a : α) : 0 ≤ a ^ 2 :=
by rw pow_two; exact mul_self_nonneg _

theorem pow_ge_one_add_sub_mul [linear_ordered_ring α]
  {a : α} (H : a ≥ 1) (n : ℕ) : 1 + n • (a - 1) ≤ a ^ n :=
by simpa using pow_ge_one_add_mul (sub_nonneg.2 H) n

namespace int

lemma units_pow_two (u : units ℤ) : u ^ 2 = 1 :=
(units_eq_one_or u).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

lemma units_pow_eq_pow_mod_two (u : units ℤ) (n : ℕ) : u ^ n = u ^ (n % 2) :=
by conv {to_lhs, rw ← nat.mod_add_div n 2}; simp [pow_add, pow_mul, units_pow_two]

end int