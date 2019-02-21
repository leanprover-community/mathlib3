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
import algebra.char_zero algebra.group algebra.ordered_field
import data.int.basic data.list.basic

universes u v
variable {α : Type u}

@[simp] theorem inv_one [division_ring α] : (1⁻¹ : α) = 1 := by rw [inv_eq_one_div, one_div_one]

@[simp] theorem inv_inv' [discrete_field α] {a:α} : a⁻¹⁻¹ = a :=
by rw [inv_eq_one_div, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_one]

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
by induction n with n ih; [rw [pow_zero, one_mul, mul_one],
  rw [pow_succ, mul_assoc, ih]]
theorem smul_add_comm' : ∀ (a : β) (n : ℕ), n•a + a = a + n•a :=
@pow_mul_comm' (multiplicative β) _

theorem pow_succ' (a : α) (n : ℕ) : a^(n+1) = a^n * a :=
by rw [pow_succ, pow_mul_comm']
theorem succ_smul' (a : β) (n : ℕ) : (n+1)•a = n•a + a :=
by rw [succ_smul, smul_add_comm']
attribute [to_additive succ_smul'] pow_succ'

theorem pow_two (a : α) : a^2 = a * a :=
show a*(a*1)=a*a, by rw mul_one
theorem two_smul (a : β) : 2•a = a + a :=
show a+(a+0)=a+a, by rw add_zero
attribute [to_additive two_smul] pow_two

theorem pow_add (a : α) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [add_zero, pow_zero, mul_one],
  rw [pow_succ, ← pow_mul_comm', ← mul_assoc, ← ih, ← pow_succ']]; refl
theorem add_monoid.add_smul : ∀ (a : β) (m n : ℕ), (m + n)•a = m•a + n•a :=
@pow_add (multiplicative β) _
attribute [to_additive add_monoid.add_smul] pow_add

@[simp] theorem one_pow (n : ℕ) : (1 : α)^n = (1:α) :=
by induction n with n ih; [refl, rw [pow_succ, ih, one_mul]]
@[simp] theorem add_monoid.smul_zero (n : ℕ) : n•(0 : β) = (0:β) :=
by induction n with n ih; [refl, rw [succ_smul, ih, zero_add]]
attribute [to_additive add_monoid.smul_zero] one_pow

theorem pow_mul (a : α) (m n : ℕ) : a^(m * n) = (a^m)^n :=
by induction n with n ih; [rw mul_zero, rw [nat.mul_succ, pow_add, pow_succ', ih]]; refl
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

@[simp] theorem list.prod_repeat (a : α) (n : ℕ) : (list.repeat a n).prod = a ^ n :=
by induction n with n ih; [refl, rw [list.repeat_succ, list.prod_cons, ih]]; refl
@[simp] theorem list.sum_repeat : ∀ (a : β) (n : ℕ), (list.repeat a n).sum = n • a :=
@list.prod_repeat (multiplicative β) _
attribute [to_additive list.sum_repeat] list.prod_repeat

@[simp] lemma units.coe_pow (u : units α) (n : ℕ) : ((u ^ n : units α) : α) = u ^ n :=
by induction n; simp [*, pow_succ]

end monoid

@[simp] theorem nat.pow_eq_pow (p q : ℕ) :
  @has_pow.pow _ _ monoid.has_pow p q = p ^ q :=
by induction q with q ih; [refl, rw [nat.pow_succ, pow_succ, mul_comm, ih]]

@[simp] theorem nat.smul_eq_mul (m n : ℕ) : m • n = m * n :=
by induction m with m ih; [rw [add_monoid.zero_smul, zero_mul],
  rw [succ_smul', ih, nat.succ_mul]]

/- commutative monoid -/

section comm_monoid
variables [comm_monoid α] {β : Type*} [add_comm_monoid β]

theorem mul_pow (a b : α) (n : ℕ) : (a * b)^n = a^n * b^n :=
by induction n with n ih; [exact (mul_one _).symm,
  simp only [pow_succ, ih, mul_assoc, mul_left_comm]]
theorem add_monoid.smul_add : ∀ (a b : β) (n : ℕ), n•(a + b) = n•a + n•b :=
@mul_pow (multiplicative β) _
attribute [to_additive add_monoid.add_smul] mul_pow

instance pow.is_monoid_hom (n : ℕ) : is_monoid_hom ((^ n) : α → α) :=
by refine_struct {..}; simp [mul_pow, one_pow]

instance add_monoid.smul.is_add_monoid_hom (n : ℕ) : is_add_monoid_hom (add_monoid.smul n : β → β) :=
by refine_struct {..}; simp [add_monoid.smul_zero, add_monoid.smul_add]

attribute [to_additive add_monoid.smul.is_add_monoid_hom] pow.is_monoid_hom

end comm_monoid

section group
variables [group α] {β : Type*} [add_group β]

section nat

@[simp] theorem inv_pow (a : α) (n : ℕ) : (a⁻¹)^n = (a^n)⁻¹ :=
by induction n with n ih; [exact one_inv.symm,
  rw [pow_succ', pow_succ, ih, mul_inv_rev]]
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
| -[1+ n] := show _⁻¹=(1:α), by rw [_root_.one_pow, one_inv]
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

theorem gpow_neg_one (x : α) : x ^ (-1:ℤ) = x⁻¹ := congr_arg has_inv.inv $ pow_one x
theorem neg_one_gsmul (x : β) : (-1:ℤ) • x = -x := congr_arg has_neg.neg $ add_monoid.one_smul x
attribute [to_additive neg_one_gsmul] gpow_neg_one

theorem inv_gpow (a : α) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := congr_arg has_inv.inv $ inv_pow a (n+1)

private lemma gpow_add_aux (a : α) (m n : nat) :
  a ^ ((of_nat m) + -[1+n]) = a ^ of_nat m * a ^ -[1+n] :=
or.elim (nat.lt_or_ge m (nat.succ n))
 (assume h1 : m < succ n,
  have h2 : m ≤ n, from le_of_lt_succ h1,
  suffices a ^ -[1+ n-m] = a ^ of_nat m * a ^ -[1+n],
    by rwa [of_nat_add_neg_succ_of_nat_of_lt h1],
  show (a ^ nat.succ (n - m))⁻¹ = a ^ of_nat m * a ^ -[1+n],
  by rw [← succ_sub h2, pow_sub _ (le_of_lt h1), mul_inv_rev, inv_inv]; refl)
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

theorem gpow_add_one (a : α) (i : ℤ) : a ^ (i + 1) = a ^ i * a :=
by rw [gpow_add, gpow_one]
theorem add_one_gsmul : ∀ (a : β) (i : ℤ), (i + 1) • a = i • a + a :=
@gpow_add_one (multiplicative β) _
attribute [to_additive add_one_gsmul] gpow_add_one

theorem gpow_one_add (a : α) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [gpow_add, gpow_one]
theorem one_add_gsmul : ∀ (a : β) (i : ℤ), (1 + i) • a = a + i • a :=
@gpow_one_add (multiplicative β) _
attribute [to_additive one_add_gsmul] gpow_one_add

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
  show (a ^ (m.succ * n))⁻¹ = _, by rw [pow_mul, ← inv_pow]; refl
| -[1+ m] -[1+ n] := (pow_mul a (succ m) (succ n)).trans $
  show _ = (_⁻¹^_)⁻¹, by rw [inv_pow, inv_inv]
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

theorem gsmul_neg (a : β) (n : ℤ) : gsmul n (- a) = - gsmul n a :=
begin
  induction n using int.induction_on with z ih z ih,
  { simp },
  { rw [add_comm] {occs := occurrences.pos [1]}, simp [add_gsmul, ih, -add_comm] },
  { rw [sub_eq_add_neg, add_comm] {occs := occurrences.pos [1]},
    simp [ih, add_gsmul, neg_gsmul, -add_comm] }
end
attribute [to_additive gsmul_neg] gpow_neg

end group

namespace is_group_hom
variables {β : Type v} [group α] [group β] (f : α → β) [is_group_hom f]

theorem pow (a : α) (n : ℕ) : f (a ^ n) = f a ^ n :=
by induction n with n ih; [exact is_group_hom.one f,
  rw [pow_succ, is_group_hom.mul f, ih]]; refl

theorem gpow (a : α) (n : ℤ) : f (a ^ n) = f a ^ n :=
by cases n; [exact is_group_hom.pow f _ _,
  exact (is_group_hom.inv f _).trans (congr_arg _ $ is_group_hom.pow f _ _)]

end is_group_hom

namespace is_add_group_hom
variables {β : Type v} [add_group α] [add_group β] (f : α → β) [is_add_group_hom f]

theorem smul (a : α) (n : ℕ) : f (n • a) = n • f a :=
by induction n with n ih; [exact is_add_group_hom.zero f,
  rw [succ_smul, is_add_group_hom.add f, ih]]; refl

theorem gsmul (a : α) (n : ℤ) : f (gsmul n a) = gsmul n (f a) :=
begin
  induction n using int.induction_on with z ih z ih,
  { simp [is_add_group_hom.zero f] },
  { simp [is_add_group_hom.add f, add_gsmul, ih] },
  { simp [is_add_group_hom.add f, is_add_group_hom.neg f, add_gsmul, ih] }
end

end is_add_group_hom

local infix ` •ℤ `:70 := gsmul

section comm_monoid
variables [comm_group α] {β : Type*} [add_comm_group β]

theorem mul_gpow (a b : α) : ∀ n:ℤ, (a * b)^n = a^n * b^n
| (n : ℕ) := mul_pow a b n
| -[1+ n] := show _⁻¹=_⁻¹*_⁻¹, by rw [mul_pow, mul_inv_rev, mul_comm]
theorem gsmul_add : ∀ (a b : β) (n : ℤ), n •ℤ (a + b) = n •ℤ a + n •ℤ b :=
@mul_gpow (multiplicative β) _
attribute [to_additive gsmul_add] mul_gpow

theorem gsmul_sub : ∀ (a b : β) (n : ℤ), gsmul n (a - b) = gsmul n a - gsmul n b :=
by simp [gsmul_add, gsmul_neg]

instance gpow.is_group_hom (n : ℤ) : is_group_hom ((^ n) : α → α) :=
⟨λ _ _, mul_gpow _ _ n⟩

instance gsmul.is_add_group_hom (n : ℤ) : is_add_group_hom (gsmul n : β → β) :=
⟨λ _ _, gsmul_add _ _ n⟩

attribute [to_additive gsmul.is_add_group_hom] gpow.is_group_hom

end comm_monoid

section group

@[instance]
theorem is_add_group_hom_gsmul
  {α β} [add_group α] [add_comm_group β] (f : α → β) [is_add_group_hom f] (z : ℤ) :
  is_add_group_hom (λa, gsmul z (f a)) :=
⟨assume a b, by rw [is_add_group_hom.add f, gsmul_add]⟩

end group

@[simp] lemma with_bot.coe_smul [add_monoid α] (a : α) (n : ℕ) :
  ((add_monoid.smul n a : α) : with_bot α) = add_monoid.smul n a :=
by induction n; simp [*, succ_smul]; refl

theorem add_monoid.smul_eq_mul' [semiring α] (a : α) (n : ℕ) : n • a = a * n :=
by induction n with n ih; [rw [add_monoid.zero_smul, nat.cast_zero, mul_zero],
  rw [succ_smul', ih, nat.cast_succ, mul_add, mul_one]]

theorem add_monoid.smul_eq_mul [semiring α] (n : ℕ) (a : α) : n • a = n * a :=
by rw [add_monoid.smul_eq_mul', nat.mul_cast_comm]

theorem add_monoid.mul_smul_left [semiring α] (a b : α) (n : ℕ) : n • (a * b) = a * (n • b) :=
by rw [add_monoid.smul_eq_mul', add_monoid.smul_eq_mul', mul_assoc]

theorem add_monoid.mul_smul_assoc [semiring α] (a b : α) (n : ℕ) : n • (a * b) = n • a * b :=
by rw [add_monoid.smul_eq_mul, add_monoid.smul_eq_mul, mul_assoc]

lemma zero_pow [semiring α] : ∀ {n : ℕ}, 0 < n → (0 : α) ^ n = 0
| (n+1) _ := zero_mul _

@[simp] theorem nat.cast_pow [semiring α] (n m : ℕ) : (↑(n ^ m) : α) = ↑n ^ m :=
by induction m with m ih; [exact nat.cast_one, rw [nat.pow_succ, pow_succ', nat.cast_mul, ih]]

@[simp] theorem int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m :=
by induction m with m ih; [exact int.coe_nat_one, rw [nat.pow_succ, pow_succ', int.coe_nat_mul, ih]]

theorem int.nat_abs_pow (n : ℤ) (k : ℕ) : int.nat_abs (n ^ k) = (int.nat_abs n) ^ k :=
by induction k with k ih; [refl, rw [pow_succ', int.nat_abs_mul, nat.pow_succ, ih]]

theorem is_semiring_hom.map_pow {β} [semiring α] [semiring β]
  (f : α → β) [is_semiring_hom f] (x : α) (n : ℕ) : f (x ^ n) = f x ^ n :=
by induction n with n ih; [exact is_semiring_hom.map_one f,
  rw [pow_succ, pow_succ, is_semiring_hom.map_mul f, ih]]

theorem neg_one_pow_eq_or {R} [ring R] : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := or.inl rfl
| (n+1) := (neg_one_pow_eq_or n).swap.imp
  (λ h, by rw [pow_succ, h, neg_one_mul, neg_neg])
  (λ h, by rw [pow_succ, h, mul_one])

lemma pow_dvd_pow [comm_semiring α] (a : α) {m n : ℕ} (h : m ≤ n) :
  a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, nat.add_sub_cancel' h]⟩

theorem gsmul_eq_mul [ring α] (a : α) : ∀ n, n •ℤ a = n * a
| (n : ℕ) := add_monoid.smul_eq_mul _ _
| -[1+ n] := show -(_•_)=-_*_, by rw [neg_mul_eq_neg_mul_symm, add_monoid.smul_eq_mul, nat.cast_succ]

theorem gsmul_eq_mul' [ring α] (a : α) (n : ℤ) : n •ℤ a = a * n :=
by rw [gsmul_eq_mul, int.mul_cast_comm]

theorem mul_gsmul_left [ring α] (a b : α) (n : ℤ) : n •ℤ (a * b) = a * (n •ℤ b) :=
by rw [gsmul_eq_mul', gsmul_eq_mul', mul_assoc]

theorem mul_gsmul_assoc [ring α] (a b : α) (n : ℤ) : n •ℤ (a * b) = n •ℤ a * b :=
by rw [gsmul_eq_mul, gsmul_eq_mul, mul_assoc]

@[simp] theorem int.cast_pow [ring α] (n : ℤ) (m : ℕ) : (↑(n ^ m) : α) = ↑n ^ m :=
by induction m with m ih; [exact int.cast_one,
  rw [pow_succ, pow_succ, int.cast_mul, ih]]

lemma neg_one_pow_eq_pow_mod_two [ring α] {n : ℕ} : (-1 : α) ^ n = -1 ^ (n % 2) :=
by rw [← nat.mod_add_div n 2, pow_add, pow_mul]; simp [pow_two]

theorem pow_eq_zero [domain α] {x : α} {n : ℕ} (H : x^n = 0) : x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  exact or.cases_on (mul_eq_zero.1 H) id ih
end

theorem pow_ne_zero [domain α] {a : α} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero h

@[simp] theorem one_div_pow [division_ring α] {a : α} (ha : a ≠ 0) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n :=
by induction n with n ih; [exact (div_one _).symm,
  rw [pow_succ', ih, division_ring.one_div_mul_one_div (pow_ne_zero _ ha) ha]]; refl

@[simp] theorem division_ring.inv_pow [division_ring α] {a : α} (ha : a ≠ 0) (n : ℕ) : a⁻¹ ^ n = (a ^ n)⁻¹ :=
by simpa only [inv_eq_one_div] using one_div_pow ha n

@[simp] theorem div_pow [field α] (a : α) {b : α} (hb : b ≠ 0) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n :=
by rw [div_eq_mul_one_div, mul_pow, one_div_pow hb, ← div_eq_mul_one_div]

theorem add_monoid.smul_nonneg [ordered_comm_monoid α] {a : α} (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ n • a
| 0     := le_refl _
| (n+1) := add_nonneg' H (add_monoid.smul_nonneg n)

lemma pow_abs [decidable_linear_ordered_comm_ring α] (a : α) (n : ℕ) : (abs a)^n = abs (a^n) :=
by induction n with n ih; [exact (abs_one).symm,
  rw [pow_succ, pow_succ, ih, abs_mul]]

lemma inv_pow' [discrete_field α] (a : α) (n : ℕ) : (a ^ n)⁻¹ = a⁻¹ ^ n :=
by induction n; simp [*, pow_succ, mul_inv', mul_comm]

lemma pow_inv [division_ring α] (a : α) : ∀ n : ℕ, a ≠ 0 → (a^n)⁻¹ = (a⁻¹)^n
| 0     ha := inv_one
| (n+1) ha := by rw [pow_succ, pow_succ', mul_inv_eq (pow_ne_zero _ ha) ha, pow_inv _ ha]

namespace add_monoid
variable [ordered_comm_monoid α]

theorem smul_le_smul {a : α} {n m : ℕ} (ha : 0 ≤ a) (h : n ≤ m) : n • a ≤ m • a :=
let ⟨k, hk⟩ := nat.le.dest h in
calc n • a = n • a + 0 : (add_zero _).symm
  ... ≤ n • a + k • a : add_le_add_left' (smul_nonneg ha _)
  ... = m • a : by rw [← hk, add_smul]

lemma smul_le_smul_of_le_right {a b : α} (hab : a ≤ b) : ∀ i : ℕ, i • a ≤ i • b
| 0 := by simp
| (k+1) := add_le_add' hab (smul_le_smul_of_le_right _)

end add_monoid

section linear_ordered_semiring
variable [linear_ordered_semiring α]

theorem pow_pos {a : α} (H : 0 < a) : ∀ (n : ℕ), 0 < a ^ n
| 0     := zero_lt_one
| (n+1) := mul_pos H (pow_pos _)

theorem pow_nonneg {a : α} (H : 0 ≤ a) : ∀ (n : ℕ), 0 ≤ a ^ n
| 0     := zero_le_one
| (n+1) := mul_nonneg H (pow_nonneg _)

theorem pow_lt_pow_of_lt_left {x y : α} {n : ℕ} (Hxy : x < y) (Hxpos : 0 ≤ x) (Hnpos : 0 < n) : x ^ n < y ^ n :=
begin
  cases lt_or_eq_of_le Hxpos,
  { rw ←nat.sub_add_cancel Hnpos,
    induction (n - 1), { simpa only [pow_one] },
    rw [pow_add, pow_add, nat.succ_eq_add_one, pow_one, pow_one],
    apply mul_lt_mul ih (le_of_lt Hxy) h (le_of_lt (pow_pos (lt_trans h Hxy) _)) },
  { rw [←h, zero_pow Hnpos], apply pow_pos (by rwa ←h at Hxy : 0 < y),}
end

theorem pow_right_inj {x y : α} {n : ℕ} (Hxpos : 0 ≤ x) (Hypos : 0 ≤ y) (Hnpos : 0 < n) (Hxyn : x ^ n = y ^ n) : x = y :=
begin
  rcases lt_trichotomy x y with hxy | rfl | hyx,
  { exact absurd Hxyn (ne_of_lt (pow_lt_pow_of_lt_left hxy Hxpos Hnpos)) },
  { refl },
  { exact absurd Hxyn (ne_of_gt (pow_lt_pow_of_lt_left hyx Hypos Hnpos)) },
end

theorem one_le_pow_of_one_le {a : α} (H : 1 ≤ a) : ∀ (n : ℕ), 1 ≤ a ^ n
| 0     := le_refl _
| (n+1) := by simpa only [mul_one] using mul_le_mul H (one_le_pow_of_one_le n)
    zero_le_one (le_trans zero_le_one H)

theorem pow_ge_one_add_mul {a : α} (H : a ≥ 0) :
  ∀ (n : ℕ), 1 + n • a ≤ (1 + a) ^ n
| 0     := le_of_eq $ add_zero _
| (n+1) := begin
  rw [pow_succ', succ_smul'],
  refine le_trans _ (mul_le_mul_of_nonneg_right
    (pow_ge_one_add_mul n) (add_nonneg zero_le_one H)),
  rw [mul_add, mul_one, ← add_assoc, add_le_add_iff_left],
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    ((le_add_iff_nonneg_right 1).2 (add_monoid.smul_nonneg H n)) H
end

theorem pow_le_pow {a : α} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
let ⟨k, hk⟩ := nat.le.dest h in
calc a ^ n = a ^ n * 1 : (mul_one _).symm
  ... ≤ a ^ n * a ^ k : mul_le_mul_of_nonneg_left
    (one_le_pow_of_one_le ha _)
    (pow_nonneg (le_trans zero_le_one ha) _)
  ... = a ^ m : by rw [←hk, pow_add]

lemma pow_le_pow_of_le_left  {a b : α} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0 := by simp
| (k+1) := mul_le_mul hab (pow_le_pow_of_le_left _) (pow_nonneg ha _) (le_trans ha hab)

private lemma pow_lt_pow_of_lt_one_aux {a : α} (h : 0 < a) (ha : a < 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k + 1) < a ^ i
| 0 := begin simp, rw ←one_mul (a^i), exact mul_lt_mul ha (le_refl _) (pow_pos h _) zero_le_one end
| (k+1) :=
  begin
    rw ←one_mul (a^i),
    apply mul_lt_mul ha _ _ zero_le_one,
    { apply le_of_lt, apply pow_lt_pow_of_lt_one_aux },
    { show 0 < a ^ (i + (k + 1) + 0), apply pow_pos h }
  end

private lemma pow_le_pow_of_le_one_aux {a : α}  (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
| 0 := by simp
| (k+1) := by rw [←add_assoc, ←one_mul (a^i)];
              exact mul_le_mul ha (pow_le_pow_of_le_one_aux _) (pow_nonneg h _) zero_le_one

lemma pow_lt_pow_of_lt_one  {a : α} (h : 0 < a) (ha : a < 1)
  {i j : ℕ} (hij : i < j) : a ^ j < a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt hij in
by rw hk; exact pow_lt_pow_of_lt_one_aux h ha _ _

lemma pow_le_pow_of_le_one  {a : α} (h : 0 ≤ a) (ha : a ≤ 1)
  {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_le hij in
by rw hk; exact pow_le_pow_of_le_one_aux h ha _ _

lemma pow_le_one {x : α} : ∀ (n : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1), x ^ n ≤ 1
| 0     h0 h1 := le_refl (1 : α)
| (n+1) h0 h1 := mul_le_one h1 (pow_nonneg h0 _) (pow_le_one n h0 h1)

end linear_ordered_semiring
theorem pow_two_nonneg [linear_ordered_ring α] (a : α) : 0 ≤ a ^ 2 :=
by rw pow_two; exact mul_self_nonneg _

theorem pow_ge_one_add_sub_mul [linear_ordered_ring α]
  {a : α} (H : a ≥ 1) (n : ℕ) : 1 + n • (a - 1) ≤ a ^ n :=
by simpa only [add_sub_cancel'_right] using pow_ge_one_add_mul (sub_nonneg.2 H) n

namespace int

lemma units_pow_two (u : units ℤ) : u ^ 2 = 1 :=
(units_eq_one_or u).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

lemma units_pow_eq_pow_mod_two (u : units ℤ) (n : ℕ) : u ^ n = u ^ (n % 2) :=
by conv {to_lhs, rw ← nat.mod_add_div n 2}; rw [pow_add, pow_mul, units_pow_two, one_pow, mul_one]

end int

@[simp] lemma neg_square {α} [ring α] (z : α) : (-z)^2 = z^2 :=
by simp [pow, monoid.pow]

lemma div_sq_cancel {α} [field α] {a : α} (ha : a ≠ 0) (b : α) : a^2 * b / a = a * b :=
by rw [pow_two, mul_assoc, mul_div_cancel_left _ ha]
