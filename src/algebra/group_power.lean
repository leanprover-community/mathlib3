/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import data.int.basic
import data.equiv.basic

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

## Notation

The class `has_pow α β` provides the notation `a^b` for powers.
We define instances of `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/

universes u v w x y z u₁ u₂

variables {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-- The power operation in a monoid. `a^n = a*a*...*a` n times. -/
def monoid.pow [has_mul M] [has_one M] (a : M) : ℕ → M
| 0     := 1
| (n+1) := a * monoid.pow n

/-- The scalar multiplication in an additive monoid.
`n • a = a+a+...+a` n times. -/
def add_monoid.smul [has_add A] [has_zero A] (n : ℕ) (a : A) : A :=
@monoid.pow (multiplicative A) _ { one := (0 : A) } a n

precedence `•`:70
localized "infix ` • ` := add_monoid.smul" in add_monoid

@[priority 5] instance monoid.has_pow [monoid M] : has_pow M ℕ := ⟨monoid.pow⟩

/-!
### (Additive) monoid
-/
section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp] theorem pow_zero (a : M) : a^0 = 1 := rfl
@[simp] theorem add_monoid.zero_smul (a : A) : 0 • a = 0 := rfl

theorem pow_succ (a : M) (n : ℕ) : a^(n+1) = a * a^n := rfl
theorem succ_smul (a : A) (n : ℕ) : (n+1)•a = a + n•a := rfl

@[simp] theorem pow_one (a : M) : a^1 = a := mul_one _
@[simp] theorem add_monoid.one_smul (a : A) : 1•a = a := add_zero _

@[simp] lemma pow_ite (P : Prop) [decidable P] (a : M) (b c : ℕ) :
  a ^ (if P then b else c) = if P then a ^ b else a ^ c :=
by split_ifs; refl

@[simp] lemma ite_pow (P : Prop) [decidable P] (a b : M) (c : ℕ) :
  (if P then a else b) ^ c = if P then a ^ c else b ^ c :=
by split_ifs; refl

@[simp] lemma pow_boole (P : Prop) [decidable P] (a : M) :
  a ^ (if P then 1 else 0) = if P then a else 1 :=
by simp

theorem pow_mul_comm' (a : M) (n : ℕ) : a^n * a = a * a^n :=
by induction n with n ih; [rw [pow_zero, one_mul, mul_one],
  rw [pow_succ, mul_assoc, ih]]
theorem smul_add_comm' : ∀ (a : A) (n : ℕ), n•a + a = a + n•a :=
@pow_mul_comm' (multiplicative A) _

theorem pow_succ' (a : M) (n : ℕ) : a^(n+1) = a^n * a :=
by rw [pow_succ, pow_mul_comm']
theorem succ_smul' (a : A) (n : ℕ) : (n+1)•a = n•a + a :=
by rw [succ_smul, smul_add_comm']

theorem pow_two (a : M) : a^2 = a * a :=
show a*(a*1)=a*a, by rw mul_one
theorem two_smul' (a : A) : 2•a = a + a :=
show a+(a+0)=a+a, by rw add_zero

theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [add_zero, pow_zero, mul_one],
  rw [pow_succ, ← pow_mul_comm', ← mul_assoc, ← ih, ← pow_succ']]; refl
theorem add_monoid.add_smul : ∀ (a : A) (m n : ℕ), (m + n)•a = m•a + n•a :=
@pow_add (multiplicative A) _

@[simp] theorem one_pow (n : ℕ) : (1 : M)^n = 1 :=
by induction n with n ih; [refl, rw [pow_succ, ih, one_mul]]
@[simp] theorem add_monoid.smul_zero (n : ℕ) : n•(0 : A) = 0 :=
by induction n with n ih; [refl, rw [succ_smul, ih, zero_add]]

theorem pow_mul (a : M) (m n : ℕ) : a^(m * n) = (a^m)^n :=
by induction n with n ih; [rw mul_zero, rw [nat.mul_succ, pow_add, pow_succ', ih]]; refl
theorem add_monoid.mul_smul' : ∀ (a : A) (m n : ℕ), m * n • a = n•(m•a) :=
@pow_mul (multiplicative A) _

theorem pow_mul' (a : M) (m n : ℕ) : a^(m * n) = (a^n)^m :=
by rw [mul_comm, pow_mul]
theorem add_monoid.mul_smul (a : A) (m n : ℕ) : m * n • a = m•(n•a) :=
by rw [mul_comm, add_monoid.mul_smul']

@[simp] theorem add_monoid.smul_one [has_one A] : ∀ n : ℕ, n • (1 : A) = n :=
add_monoid_hom.eq_nat_cast
  ⟨λ n, n • (1 : A), add_monoid.zero_smul _, λ _ _, add_monoid.add_smul _ _ _⟩
  (add_monoid.one_smul _)

theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _
theorem bit0_smul (a : A) (n : ℕ) : bit0 n • a = n•a + n•a := add_monoid.add_smul _ _ _

theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]
theorem bit1_smul : ∀ (a : A) (n : ℕ), bit1 n • a = n•a + n•a + a :=
@pow_bit1 (multiplicative A) _

theorem pow_mul_comm (a : M) (m n : ℕ) : a^m * a^n = a^n * a^m :=
by rw [←pow_add, ←pow_add, add_comm]
theorem smul_add_comm : ∀ (a : A) (m n : ℕ), m•a + n•a = n•a + m•a :=
@pow_mul_comm (multiplicative A) _

@[simp, priority 500]
theorem list.prod_repeat (a : M) (n : ℕ) : (list.repeat a n).prod = a ^ n :=
by induction n with n ih; [refl, rw [list.repeat_succ, list.prod_cons, ih]]; refl
@[simp, priority 500]
theorem list.sum_repeat : ∀ (a : A) (n : ℕ), (list.repeat a n).sum = n • a :=
@list.prod_repeat (multiplicative A) _

theorem monoid_hom.map_pow (f : M →* N) (a : M) : ∀(n : ℕ), f (a ^ n) = (f a) ^ n
| 0     := f.map_one
| (n+1) := by rw [pow_succ, pow_succ, f.map_mul, monoid_hom.map_pow]

theorem monoid_hom.iterate_map_pow (f : M →* M) (a) (n m : ℕ) : f^[n] (a^m) = (f^[n] a)^m :=
show f^[n] ((λ x, x^m) a) = (λ x, x^m) (f^[n] a),
from nat.iterate₁ $ λ x, f.map_pow x m

theorem add_monoid_hom.map_smul (f : A →+ B) (a : A) (n : ℕ) : f (n • a) = n • f a :=
f.to_multiplicative.map_pow a n

theorem add_monoid_hom.iterate_map_smul (f : A →+ A) (a : A) (n m : ℕ) :
  f^[n] (m • a) = m • (f^[n] a) :=
f.to_multiplicative.iterate_map_pow a n m

theorem is_monoid_hom.map_pow (f : M → N) [is_monoid_hom f] (a : M) :
  ∀(n : ℕ), f (a ^ n) = (f a) ^ n :=
(monoid_hom.of f).map_pow a

theorem is_add_monoid_hom.map_smul (f : A → B) [is_add_monoid_hom f] (a : A) (n : ℕ) :
  f (n • a) = n • f a :=
(add_monoid_hom.of f).map_smul a n

@[simp, norm_cast] lemma units.coe_pow (u : units M) (n : ℕ) : ((u ^ n : units M) : M) = u ^ n :=
(units.coe_hom M).map_pow u n

end monoid

@[simp] theorem nat.pow_eq_pow (p q : ℕ) :
  @has_pow.pow _ _ monoid.has_pow p q = p ^ q :=
by induction q with q ih; [refl, rw [nat.pow_succ, pow_succ, mul_comm, ih]]

@[simp] theorem nat.smul_eq_mul (m n : ℕ) : m • n = m * n :=
by induction m with m ih; [rw [add_monoid.zero_smul, zero_mul],
  rw [succ_smul', ih, nat.succ_mul]]

/-!
### Commutative (additive) monoid
-/

section comm_monoid
variables [comm_monoid M] [add_comm_monoid A]

theorem mul_pow (a b : M) (n : ℕ) : (a * b)^n = a^n * b^n :=
by induction n with n ih; [exact (mul_one _).symm,
  simp only [pow_succ, ih, mul_assoc, mul_left_comm]]
theorem add_monoid.smul_add : ∀ (a b : A) (n : ℕ), n•(a + b) = n•a + n•b :=
@mul_pow (multiplicative A) _

instance pow.is_monoid_hom (n : ℕ) : is_monoid_hom ((^ n) : M → M) :=
{ map_mul := λ _ _, mul_pow _ _ _, map_one := one_pow _ }

instance add_monoid.smul.is_add_monoid_hom (n : ℕ) : is_add_monoid_hom (add_monoid.smul n : A → A) :=
{ map_add := λ _ _, add_monoid.smul_add _ _ _, map_zero := add_monoid.smul_zero _ }

end comm_monoid

section group
variables [group G] [group H] [add_group A] [add_group B]

section nat

@[simp] theorem inv_pow (a : G) (n : ℕ) : (a⁻¹)^n = (a^n)⁻¹ :=
by induction n with n ih; [exact one_inv.symm,
  rw [pow_succ', pow_succ, ih, mul_inv_rev]]
@[simp] theorem add_monoid.neg_smul : ∀ (a : A) (n : ℕ), n•(-a) = -(n•a) :=
@inv_pow (multiplicative A) _

theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq h2
theorem add_monoid.smul_sub : ∀ (a : A) {m n : ℕ}, n ≤ m → (m - n)•a = m•a - n•a :=
@pow_sub (multiplicative A) _

theorem pow_inv_comm (a : G) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
by rw inv_pow; exact inv_comm_of_comm (pow_mul_comm _ _ _)
theorem add_monoid.smul_neg_comm : ∀ (a : A) (m n : ℕ), m•(-a) + n•a = n•a + m•(-a) :=
@pow_inv_comm (multiplicative A) _
end nat

open int

/--
The power operation in a group. This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
def gpow (a : G) : ℤ → G
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

/--
The scalar multiplication by integers on an additive group.
This extends `add_monoid.smul` to negative integers
with the definition `(-n) • a = -(n • a)`.
-/
def gsmul (n : ℤ) (a : A) : A :=
@gpow (multiplicative A) _ a n

@[priority 10] instance group.has_pow : has_pow G ℤ := ⟨gpow⟩

localized "infix ` • `:70 := gsmul" in add_group
localized "infix ` •ℕ `:70 := add_monoid.smul" in smul
localized "infix ` •ℤ `:70 := gsmul" in smul

@[simp] theorem gpow_coe_nat (a : G) (n : ℕ) : a ^ (n:ℤ) = a ^ n := rfl
@[simp] theorem gsmul_coe_nat (a : A) (n : ℕ) : (n:ℤ) • a = n •ℕ a := rfl

theorem gpow_of_nat (a : G) (n : ℕ) : a ^ of_nat n = a ^ n := rfl
theorem gsmul_of_nat (a : A) (n : ℕ) : of_nat n • a = n •ℕ a := rfl

@[simp] theorem gpow_neg_succ (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl
@[simp] theorem gsmul_neg_succ (a : A) (n : ℕ) : -[1+n] • a = - (n.succ •ℕ a) := rfl

local attribute [ematch] le_of_lt
open nat

@[simp] theorem gpow_zero (a : G) : a ^ (0:ℤ) = 1 := rfl
@[simp] theorem zero_gsmul (a : A) : (0:ℤ) • a = 0 := rfl

@[simp] theorem gpow_one (a : G) : a ^ (1:ℤ) = a := mul_one _
@[simp] theorem one_gsmul (a : A) : (1:ℤ) • a = a := add_zero _

@[simp] theorem one_gpow : ∀ (n : ℤ), (1 : G) ^ n = 1
| (n : ℕ) := one_pow _
| -[1+ n] := show _⁻¹=(1:G), by rw [_root_.one_pow, one_inv]
@[simp] theorem gsmul_zero : ∀ (n : ℤ), n • (0 : A) = 0 :=
@one_gpow (multiplicative A) _

@[simp] theorem gpow_neg (a : G) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := rfl
| 0       := one_inv.symm
| -[1+ n] := (inv_inv _).symm

@[simp] theorem neg_gsmul : ∀ (a : A) (n : ℤ), -n • a = -(n • a) :=
@gpow_neg (multiplicative A) _

theorem gpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ := congr_arg has_inv.inv $ pow_one x
theorem neg_one_gsmul (x : A) : (-1:ℤ) • x = -x := congr_arg has_neg.neg $ add_monoid.one_smul x

theorem gsmul_one [has_one A] (n : ℤ) : n • (1 : A) = n :=
by cases n; simp

theorem inv_gpow (a : G) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := congr_arg has_inv.inv $ inv_pow a (n+1)
theorem gsmul_neg (a : A) (n : ℤ) : gsmul n (- a) = - gsmul n a :=
@inv_gpow (multiplicative A) _ a n

private lemma gpow_add_aux (a : G) (m n : nat) :
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

theorem gpow_add (a : G) : ∀ (i j : ℤ), a ^ (i + j) = a ^ i * a ^ j
| (of_nat m) (of_nat n) := pow_add _ _ _
| (of_nat m) -[1+n]     := gpow_add_aux _ _ _
| -[1+m]     (of_nat n) := by rw [add_comm, gpow_add_aux,
  gpow_neg_succ, gpow_of_nat, ← inv_pow, ← pow_inv_comm]
| -[1+m]     -[1+n]     :=
  suffices (a ^ (m + succ (succ n)))⁻¹ = (a ^ m.succ)⁻¹ * (a ^ n.succ)⁻¹, from this,
  by rw [← succ_add_eq_succ_add, add_comm, _root_.pow_add, mul_inv_rev]

theorem add_gsmul : ∀ (a : A) (i j : ℤ), (i + j) • a = i • a + j • a :=
@gpow_add (multiplicative A) _

theorem gpow_add_one (a : G) (i : ℤ) : a ^ (i + 1) = a ^ i * a :=
by rw [gpow_add, gpow_one]
theorem add_one_gsmul : ∀ (a : A) (i : ℤ), (i + 1) • a = i • a + a :=
@gpow_add_one (multiplicative A) _

theorem gpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [gpow_add, gpow_one]
theorem one_add_gsmul : ∀ (a : A) (i : ℤ), (1 + i) • a = a + i • a :=
@gpow_one_add (multiplicative A) _

theorem gpow_mul_comm (a : G) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
by rw [← gpow_add, ← gpow_add, add_comm]
theorem gsmul_add_comm : ∀ (a : A) (i j), i • a + j • a = j • a + i • a :=
@gpow_mul_comm (multiplicative A) _

theorem gpow_mul (a : G) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := pow_mul _ _ _
| (m : ℕ) -[1+ n] := (gpow_neg _ (m * succ n)).trans $
  show (a ^ (m * succ n))⁻¹ = _, by rw pow_mul; refl
| -[1+ m] (n : ℕ) := (gpow_neg _ (succ m * n)).trans $
  show (a ^ (m.succ * n))⁻¹ = _, by rw [pow_mul, ← inv_pow]; refl
| -[1+ m] -[1+ n] := (pow_mul a (succ m) (succ n)).trans $
  show _ = (_⁻¹^_)⁻¹, by rw [inv_pow, inv_inv]
theorem gsmul_mul' : ∀ (a : A) (m n : ℤ), m * n • a = n • (m • a) :=
@gpow_mul (multiplicative A) _

theorem gpow_mul' (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, gpow_mul]
theorem gsmul_mul (a : A) (m n : ℤ) : m * n • a = m • (n • a) :=
by rw [mul_comm, gsmul_mul']

theorem gpow_bit0 (a : G) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n := gpow_add _ _ _
theorem bit0_gsmul (a : A) (n : ℤ) : bit0 n • a = n • a + n • a := gpow_add _ _ _

theorem gpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
by rw [bit1, gpow_add]; simp [gpow_bit0]
theorem bit1_gsmul : ∀ (a : A) (n : ℤ), bit1 n • a = n • a + n • a + a :=
@gpow_bit1 (multiplicative A) _

theorem monoid_hom.map_gpow (f : G →* H) (a : G) (n : ℤ) : f (a ^ n) = f a ^ n :=
by cases n; [exact f.map_pow _ _, exact (f.map_inv _).trans (congr_arg _ $ f.map_pow _ _)]

theorem add_monoid_hom.map_gsmul (f : A →+ B) (a : A) (n : ℤ) : f (n • a) = n • f a :=
f.to_multiplicative.map_gpow a n

end group

open_locale smul

section comm_group
variables [comm_group G] [add_comm_group A]

theorem mul_gpow (a b : G) : ∀ n:ℤ, (a * b)^n = a^n * b^n
| (n : ℕ) := mul_pow a b n
| -[1+ n] := show _⁻¹=_⁻¹*_⁻¹, by rw [mul_pow, mul_inv_rev, mul_comm]
theorem gsmul_add : ∀ (a b : A) (n : ℤ), n •ℤ (a + b) = n •ℤ a + n •ℤ b :=
@mul_gpow (multiplicative A) _

theorem gsmul_sub (a b : A) (n : ℤ) : gsmul n (a - b) = gsmul n a - gsmul n b :=
by simp only [gsmul_add, gsmul_neg, sub_eq_add_neg]

instance gpow.is_group_hom (n : ℤ) : is_group_hom ((^ n) : G → G) :=
{ map_mul := λ _ _, mul_gpow _ _ n }

instance gsmul.is_add_group_hom (n : ℤ) : is_add_group_hom (gsmul n : A → A) :=
{ map_add := λ _ _, gsmul_add _ _ n }

end comm_group

@[simp] lemma with_bot.coe_smul [add_monoid A] (a : A) (n : ℕ) :
  ((add_monoid.smul n a : A) : with_bot A) = add_monoid.smul n a :=
add_monoid_hom.map_smul ⟨_, with_bot.coe_zero, with_bot.coe_add⟩ a n

theorem add_monoid.smul_eq_mul' [semiring R] (a : R) (n : ℕ) : n • a = a * n :=
by induction n with n ih; [rw [add_monoid.zero_smul, nat.cast_zero, mul_zero],
  rw [succ_smul', ih, nat.cast_succ, mul_add, mul_one]]

theorem add_monoid.smul_eq_mul [semiring R] (n : ℕ) (a : R) : n • a = n * a :=
by rw [add_monoid.smul_eq_mul', nat.mul_cast_comm]

theorem add_monoid.mul_smul_left [semiring R] (a b : R) (n : ℕ) : n • (a * b) = a * (n • b) :=
by rw [add_monoid.smul_eq_mul', add_monoid.smul_eq_mul', mul_assoc]

theorem add_monoid.mul_smul_assoc [semiring R] (a b : R) (n : ℕ) : n • (a * b) = n • a * b :=
by rw [add_monoid.smul_eq_mul, add_monoid.smul_eq_mul, mul_assoc]

lemma zero_pow [semiring R] : ∀ {n : ℕ}, 0 < n → (0 : R) ^ n = 0
| (n+1) _ := zero_mul _

@[simp, norm_cast] theorem nat.cast_pow [semiring R] (n m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
by induction m with m ih; [exact nat.cast_one, rw [nat.pow_succ, pow_succ', nat.cast_mul, ih]]

@[simp, norm_cast] theorem int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m :=
by induction m with m ih; [exact int.coe_nat_one, rw [nat.pow_succ, pow_succ', int.coe_nat_mul, ih]]

theorem int.nat_abs_pow (n : ℤ) (k : ℕ) : int.nat_abs (n ^ k) = (int.nat_abs n) ^ k :=
by induction k with k ih; [refl, rw [pow_succ', int.nat_abs_mul, nat.pow_succ, ih]]

namespace ring_hom

variables [semiring R] [semiring S]

@[simp] lemma map_pow (f : R →+* S) (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
f.to_monoid_hom.map_pow a

variable (f : R →+* R)

lemma iterate_map_pow (a) (n m : ℕ) : f^[n] (a^m) = (f^[n] a)^m :=
f.to_monoid_hom.iterate_map_pow a n m

lemma iterate_map_smul (a) (n m : ℕ) : f^[n] (m • a) = m • (f^[n] a) :=
f.to_add_monoid_hom.iterate_map_smul a n m

end ring_hom

lemma is_semiring_hom.map_pow [semiring R] [semiring S] (f : R → S) [is_semiring_hom f] (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
is_monoid_hom.map_pow f a

theorem neg_one_pow_eq_or [ring R] : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := or.inl rfl
| (n+1) := (neg_one_pow_eq_or n).swap.imp
  (λ h, by rw [pow_succ, h, neg_one_mul, neg_neg])
  (λ h, by rw [pow_succ, h, mul_one])

lemma pow_dvd_pow [comm_semiring R] (a : R) {m n : ℕ} (h : m ≤ n) :
  a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, nat.add_sub_cancel' h]⟩

theorem gsmul_eq_mul [ring R] (a : R) : ∀ n, n •ℤ a = n * a
| (n : ℕ) := add_monoid.smul_eq_mul _ _
| -[1+ n] := show -(_•_)=-_*_, by rw [neg_mul_eq_neg_mul_symm, add_monoid.smul_eq_mul, nat.cast_succ]

theorem gsmul_eq_mul' [ring R] (a : R) (n : ℤ) : n •ℤ a = a * n :=
by rw [gsmul_eq_mul, int.mul_cast_comm]

theorem mul_gsmul_left [ring R] (a b : R) (n : ℤ) : n •ℤ (a * b) = a * (n •ℤ b) :=
by rw [gsmul_eq_mul', gsmul_eq_mul', mul_assoc]

theorem mul_gsmul_assoc [ring R] (a b : R) (n : ℤ) : n •ℤ (a * b) = n •ℤ a * b :=
by rw [gsmul_eq_mul, gsmul_eq_mul, mul_assoc]

@[simp]
lemma gsmul_int_int (a b : ℤ) : a •ℤ b = a * b := by simp [gsmul_eq_mul]

lemma gsmul_int_one (n : ℤ) : n •ℤ 1 = n := by simp

@[simp, norm_cast] theorem int.cast_pow [ring R] (n : ℤ) (m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
by induction m with m ih; [exact int.cast_one,
  rw [pow_succ, pow_succ, int.cast_mul, ih]]

lemma neg_one_pow_eq_pow_mod_two [ring R] {n : ℕ} : (-1 : R) ^ n = -1 ^ (n % 2) :=
by rw [← nat.mod_add_div n 2, pow_add, pow_mul]; simp [pow_two]

theorem sq_sub_sq [comm_ring R] (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by rw [pow_two, pow_two, mul_self_sub_mul_self]

theorem pow_eq_zero [domain R] {x : R} {n : ℕ} (H : x^n = 0) : x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  exact or.cases_on (mul_eq_zero.1 H) id ih
end

@[field_simps] theorem pow_ne_zero [domain R] {a : R} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero h

theorem add_monoid.smul_nonneg [ordered_add_comm_monoid R] {a : R} (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ n • a
| 0     := le_refl _
| (n+1) := add_nonneg' H (add_monoid.smul_nonneg n)

lemma pow_abs [decidable_linear_ordered_comm_ring R] (a : R) (n : ℕ) : (abs a)^n = abs (a^n) :=
by induction n with n ih; [exact (abs_one).symm,
  rw [pow_succ, pow_succ, ih, abs_mul]]

lemma abs_neg_one_pow [decidable_linear_ordered_comm_ring R] (n : ℕ) : abs ((-1 : R)^n) = 1 :=
by rw [←pow_abs, abs_neg, abs_one, one_pow]

namespace add_monoid
variable [ordered_add_comm_monoid A]

theorem smul_le_smul {a : A} {n m : ℕ} (ha : 0 ≤ a) (h : n ≤ m) : n • a ≤ m • a :=
let ⟨k, hk⟩ := nat.le.dest h in
calc n • a = n • a + 0 : (add_zero _).symm
  ... ≤ n • a + k • a : add_le_add_left' (smul_nonneg ha _)
  ... = m • a : by rw [← hk, add_smul]

lemma smul_le_smul_of_le_right {a b : A} (hab : a ≤ b) : ∀ i : ℕ, i • a ≤ i • b
| 0 := by simp
| (k+1) := add_le_add' hab (smul_le_smul_of_le_right _)

end add_monoid

namespace canonically_ordered_semiring
variable [canonically_ordered_comm_semiring R]

theorem pow_pos {a : R} (H : 0 < a) : ∀ n : ℕ, 0 < a ^ n
| 0     := canonically_ordered_semiring.zero_lt_one
| (n+1) := canonically_ordered_semiring.mul_pos.2 ⟨H, pow_pos n⟩

lemma pow_le_pow_of_le_left {a b : R} (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := canonically_ordered_semiring.mul_le_mul hab (pow_le_pow_of_le_left k)

theorem one_le_pow_of_one_le {a : R} (H : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n :=
by simpa only [one_pow] using pow_le_pow_of_le_left H n

theorem pow_le_one {a : R} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1:=
by simpa only [one_pow] using pow_le_pow_of_le_left H n

end canonically_ordered_semiring

section linear_ordered_semiring
variable [linear_ordered_semiring R]

theorem pow_pos {a : R} (H : 0 < a) : ∀ (n : ℕ), 0 < a ^ n
| 0     := zero_lt_one
| (n+1) := mul_pos H (pow_pos _)

theorem pow_nonneg {a : R} (H : 0 ≤ a) : ∀ (n : ℕ), 0 ≤ a ^ n
| 0     := zero_le_one
| (n+1) := mul_nonneg H (pow_nonneg _)

theorem pow_lt_pow_of_lt_left {x y : R} {n : ℕ} (Hxy : x < y) (Hxpos : 0 ≤ x) (Hnpos : 0 < n) :
  x ^ n < y ^ n :=
begin
  cases lt_or_eq_of_le Hxpos,
  { rw ←nat.sub_add_cancel Hnpos,
    induction (n - 1), { simpa only [pow_one] },
    rw [pow_add, pow_add, nat.succ_eq_add_one, pow_one, pow_one],
    apply mul_lt_mul ih (le_of_lt Hxy) h (le_of_lt (pow_pos (lt_trans h Hxy) _)) },
  { rw [←h, zero_pow Hnpos], apply pow_pos (by rwa ←h at Hxy : 0 < y),}
end

theorem pow_right_inj {x y : R} {n : ℕ} (Hxpos : 0 ≤ x) (Hypos : 0 ≤ y) (Hnpos : 0 < n)
  (Hxyn : x ^ n = y ^ n) : x = y :=
begin
  rcases lt_trichotomy x y with hxy | rfl | hyx,
  { exact absurd Hxyn (ne_of_lt (pow_lt_pow_of_lt_left hxy Hxpos Hnpos)) },
  { refl },
  { exact absurd Hxyn (ne_of_gt (pow_lt_pow_of_lt_left hyx Hypos Hnpos)) },
end

theorem one_le_pow_of_one_le {a : R} (H : 1 ≤ a) : ∀ (n : ℕ), 1 ≤ a ^ n
| 0     := le_refl _
| (n+1) := by simpa only [mul_one] using mul_le_mul H (one_le_pow_of_one_le n)
    zero_le_one (le_trans zero_le_one H)

/-- Bernoulli's inequality. This version works for semirings but requires
an additional hypothesis `0 ≤ a * a`. -/
theorem one_add_mul_le_pow' {a : R} (Hsqr : 0 ≤ a * a) (H : 0 ≤ 1 + a) :
  ∀ (n : ℕ), 1 + n • a ≤ (1 + a) ^ n
| 0     := le_of_eq $ add_zero _
| (n+1) :=
calc 1 + (n + 1) • a ≤ (1 + a) * (1 + n • a) :
  by simpa [succ_smul, mul_add, add_mul, add_monoid.mul_smul_left, add_comm, add_left_comm]
    using add_monoid.smul_nonneg Hsqr n
... ≤ (1 + a)^(n+1) : mul_le_mul_of_nonneg_left (one_add_mul_le_pow' n) H

theorem pow_le_pow {a : R} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
let ⟨k, hk⟩ := nat.le.dest h in
calc a ^ n = a ^ n * 1 : (mul_one _).symm
  ... ≤ a ^ n * a ^ k : mul_le_mul_of_nonneg_left
    (one_le_pow_of_one_le ha _)
    (pow_nonneg (le_trans zero_le_one ha) _)
  ... = a ^ m : by rw [←hk, pow_add]

lemma pow_lt_pow {a : R} {n m : ℕ} (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
begin
  have h' : 1 ≤ a := le_of_lt h,
  have h'' : 0 < a := lt_trans zero_lt_one h,
  cases m, cases h2, rw [pow_succ, ←one_mul (a ^ n)],
  exact mul_lt_mul h (pow_le_pow h' (nat.le_of_lt_succ h2)) (pow_pos h'' _) (le_of_lt h'')
end

lemma pow_le_pow_of_le_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := mul_le_mul hab (pow_le_pow_of_le_left _) (pow_nonneg ha _) (le_trans ha hab)

lemma lt_of_pow_lt_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
lt_of_not_ge $ λ hn, not_lt_of_ge (pow_le_pow_of_le_left hb hn _) h

private lemma pow_lt_pow_of_lt_one_aux {a : R} (h : 0 < a) (ha : a < 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k + 1) < a ^ i
| 0 :=
  begin
    simp only [add_zero],
    rw ←one_mul (a^i), exact mul_lt_mul ha (le_refl _) (pow_pos h _) zero_le_one
  end
| (k+1) :=
  begin
    rw ←one_mul (a^i),
    apply mul_lt_mul ha _ _ zero_le_one,
    { apply le_of_lt, apply pow_lt_pow_of_lt_one_aux },
    { show 0 < a ^ (i + (k + 1) + 0), apply pow_pos h }
  end

private lemma pow_le_pow_of_le_one_aux {a : R}  (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
| 0 := by simp
| (k+1) := by rw [←add_assoc, ←one_mul (a^i)];
              exact mul_le_mul ha (pow_le_pow_of_le_one_aux _) (pow_nonneg h _) zero_le_one

lemma pow_lt_pow_of_lt_one  {a : R} (h : 0 < a) (ha : a < 1)
  {i j : ℕ} (hij : i < j) : a ^ j < a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt hij in
by rw hk; exact pow_lt_pow_of_lt_one_aux h ha _ _

lemma pow_le_pow_of_le_one  {a : R} (h : 0 ≤ a) (ha : a ≤ 1)
  {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_le hij in
by rw hk; exact pow_le_pow_of_le_one_aux h ha _ _

lemma pow_le_one {x : R} : ∀ (n : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1), x ^ n ≤ 1
| 0     h0 h1 := le_refl (1 : R)
| (n+1) h0 h1 := mul_le_one h1 (pow_nonneg h0 _) (pow_le_one n h0 h1)

end linear_ordered_semiring

theorem pow_two_nonneg [linear_ordered_ring R] (a : R) : 0 ≤ a ^ 2 :=
by { rw pow_two, exact mul_self_nonneg _ }

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow [linear_ordered_ring R] {a : R} (H : -2 ≤ a) :
  ∀ (n : ℕ), 1 + n • a ≤ (1 + a) ^ n
| 0     := le_of_eq $ add_zero _
| 1     := by simp
| (n+2) :=
have H' : 0 ≤ 2 + a,
  from neg_le_iff_add_nonneg.1 H,
have 0 ≤ n • (a * a * (2 + a)) + a * a,
  from add_nonneg (add_monoid.smul_nonneg (mul_nonneg (mul_self_nonneg a) H') n)
    (mul_self_nonneg a),
calc 1 + (n + 2) • a ≤ 1 + (n + 2) • a + (n • (a * a * (2 + a)) + a * a) :
  (le_add_iff_nonneg_right _).2 this
... = (1 + a) * (1 + a) * (1 + n • a) :
  by { simp only [add_mul, mul_add, mul_two, mul_one, one_mul, succ_smul, add_monoid.smul_add,
         add_monoid.mul_smul_assoc, (add_monoid.mul_smul_left _ _ _).symm],
       ac_refl }
... ≤ (1 + a) * (1 + a) * (1 + a)^n :
  mul_le_mul_of_nonneg_left (one_add_mul_le_pow n) (mul_self_nonneg (1 + a))
... = (1 + a)^(n + 2) : by simp only [pow_succ, mul_assoc]

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_sub_mul_le_pow [linear_ordered_ring R]
  {a : R} (H : -1 ≤ a) (n : ℕ) : 1 + n • (a - 1) ≤ a ^ n :=
have -2 ≤ a - 1, by { rw [bit0, neg_add], exact sub_le_sub_right H 1 },
by simpa only [add_sub_cancel'_right] using one_add_mul_le_pow this n

namespace int

lemma units_pow_two (u : units ℤ) : u ^ 2 = 1 :=
(units_eq_one_or u).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

lemma units_pow_eq_pow_mod_two (u : units ℤ) (n : ℕ) : u ^ n = u ^ (n % 2) :=
by conv {to_lhs, rw ← nat.mod_add_div n 2}; rw [pow_add, pow_mul, units_pow_two, one_pow, mul_one]

end int

@[simp] lemma neg_square {α} [ring α] (z : α) : (-z)^2 = z^2 :=
by simp [pow, monoid.pow]

lemma of_add_smul [add_monoid A] (x : A) (n : ℕ) :
  multiplicative.of_add (n • x) = (multiplicative.of_add x)^n := rfl

lemma of_add_gsmul [add_group A] (x : A) (n : ℤ) :
  multiplicative.of_add (n •ℤ x) = (multiplicative.of_add x)^n := rfl

variables (M G A)

/-- Monoid homomorphisms from `multiplicative ℕ` are defined by the image
of `multiplicative.of_add 1`. -/
def powers_hom [monoid M] : M ≃ (multiplicative ℕ →* M) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, pow_zero x, λ m n, pow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := pow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_pow, ← of_add_smul] } }

/-- Monoid homomorphisms from `multiplicative ℤ` are defined by the image
of `multiplicative.of_add 1`. -/
def gpowers_hom [group G] : G ≃ (multiplicative ℤ →* G) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, gpow_zero x, λ m n, gpow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := gpow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_gpow, ← of_add_gsmul ] } }

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiples_hom [add_monoid A] : A ≃ (ℕ →+ A) :=
{ to_fun := λ x, ⟨λ n, n • x, add_monoid.zero_smul x, λ m n, add_monoid.add_smul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := add_monoid.one_smul,
  right_inv := λ f, add_monoid_hom.ext $ λ n, by simp [← f.map_smul] }

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def gmultiples_hom [add_group A] : A ≃ (ℤ →+ A) :=
{ to_fun := λ x, ⟨λ n, n •ℤ x, zero_gsmul x, λ m n, add_gsmul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := one_gsmul,
  right_inv := λ f, add_monoid_hom.ext $ λ n, by simp [← f.map_gsmul] }

variables {M G A}

@[simp] lemma powers_hom_apply [monoid M] (x : M) (n : multiplicative ℕ) :
  powers_hom M x n = x ^ n.to_add := rfl

@[simp] lemma powers_hom_symm_apply [monoid M] (f : multiplicative ℕ →* M) :
  (powers_hom M).symm f = f (multiplicative.of_add 1) := rfl

lemma mnat_monoid_hom_eq [monoid M] (f : multiplicative ℕ →* M) (n : multiplicative ℕ) :
  f n = (f (multiplicative.of_add 1)) ^ n.to_add :=
by rw [← powers_hom_symm_apply, ← powers_hom_apply, equiv.apply_symm_apply]

lemma mnat_monoid_hom_ext [monoid M] ⦃f g : multiplicative ℕ →* M⦄
  (h : f (multiplicative.of_add 1) = g (multiplicative.of_add 1)) : f = g :=
monoid_hom.ext $ λ n, by rw [mnat_monoid_hom_eq f, mnat_monoid_hom_eq g, h]
