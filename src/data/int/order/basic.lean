/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.int.basic
import data.int.cast.basic
import algebra.ring.divisibility
import algebra.order.group.abs
import algebra.order.ring.char_zero
import tactic.assert_exists

/-!
# Order instances on the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains:
* instances on `ℤ`. The stronger one is `int.linear_ordered_comm_ring`.
* basic lemmas about integers that involve order properties.

## Recursors

* `int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `int.induction_on`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `int.induction_on'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

open nat

namespace int

instance : linear_ordered_comm_ring ℤ :=
{ add_le_add_left := @int.add_le_add_left,
  mul_pos         := @int.mul_pos,
  zero_le_one     := le_of_lt int.zero_lt_one,
  .. int.comm_ring, .. int.linear_order, .. int.nontrivial }

/-! ### Extra instances to short-circuit type class resolution
-/
instance : ordered_comm_ring ℤ  := strict_ordered_comm_ring.to_ordered_comm_ring'
instance : ordered_ring ℤ       := strict_ordered_ring.to_ordered_ring'
instance : linear_ordered_add_comm_group ℤ := by apply_instance

end int


namespace int

theorem abs_eq_nat_abs : ∀ a : ℤ, |a| = nat_abs a
| (n : ℕ) := abs_of_nonneg $ coe_zero_le _
| -[1+ n] := abs_of_nonpos $ le_of_lt $ neg_succ_lt_zero _

@[simp, norm_cast] lemma coe_nat_abs (n : ℤ) : (n.nat_abs : ℤ) = |n| := n.abs_eq_nat_abs.symm

lemma _root_.nat.cast_nat_abs {α : Type*} [add_group_with_one α] (n : ℤ) : (n.nat_abs : α) = ↑|n| :=
by rw [←int.coe_nat_abs, int.cast_coe_nat]

theorem nat_abs_abs (a : ℤ) : nat_abs (|a|) = nat_abs a :=
by rw [abs_eq_nat_abs]; refl

theorem sign_mul_abs (a : ℤ) : sign a * |a| = a :=
by rw [abs_eq_nat_abs, sign_mul_nat_abs]

theorem coe_nat_eq_zero {n : ℕ} : (n : ℤ) = 0 ↔ n = 0 := nat.cast_eq_zero

theorem coe_nat_ne_zero {n : ℕ} : (n : ℤ) ≠ 0 ↔ n ≠ 0 := by simp

lemma coe_nat_ne_zero_iff_pos {n : ℕ} : (n : ℤ) ≠ 0 ↔ 0 < n :=
⟨λ h, nat.pos_of_ne_zero (coe_nat_ne_zero.1 h),
λ h, (ne_of_lt (coe_nat_lt.2 h)).symm⟩

@[norm_cast] lemma abs_coe_nat (n : ℕ) : |(n : ℤ)| = n := abs_of_nonneg (coe_nat_nonneg n)

/-! ### succ and pred -/

theorem lt_succ_self (a : ℤ) : a < succ a :=
lt_add_of_pos_right _ zero_lt_one

theorem pred_self_lt (a : ℤ) : pred a < a :=
sub_lt_self _ zero_lt_one

theorem lt_add_one_iff {a b : ℤ} : a < b + 1 ↔ a ≤ b :=
add_le_add_iff_right _

lemma le_add_one {a b : ℤ} (h : a ≤ b) : a ≤ b + 1 :=
le_of_lt (int.lt_add_one_iff.mpr h)

theorem sub_one_lt_iff {a b : ℤ} : a - 1 < b ↔ a ≤ b :=
sub_lt_iff_lt_add.trans lt_add_one_iff

theorem le_sub_one_iff {a b : ℤ} : a ≤ b - 1 ↔ a < b :=
le_sub_iff_add_le

@[simp] lemma abs_lt_one_iff {a : ℤ} : |a| < 1 ↔ a = 0 :=
⟨λ a0, let ⟨hn, hp⟩ := abs_lt.mp a0 in (le_of_lt_add_one (by exact hp)).antisymm hn,
  λ a0, (abs_eq_zero.mpr a0).le.trans_lt zero_lt_one⟩

lemma abs_le_one_iff {a : ℤ} : |a| ≤ 1 ↔ a = 0 ∨ a = 1 ∨ a = -1 :=
by rw [le_iff_lt_or_eq, abs_lt_one_iff, abs_eq (zero_le_one' ℤ)]

lemma one_le_abs {z : ℤ} (h₀: z ≠ 0) : 1 ≤ |z| :=
add_one_le_iff.mpr (abs_pos.mpr h₀)

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
@[elab_as_eliminator]
protected def induction_on' {C : ℤ → Sort*} (z : ℤ) (b : ℤ)
  (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1)) (Hp : ∀ k ≤ b, C k → C (k - 1)) : C z :=
begin
  -- Note that we use `convert` here where possible as we are constructing data, and this reduces
  -- the number of times `eq.mpr` appears in the term.
  rw ←sub_add_cancel z b,
  induction (z - b) with n n,
  { induction n with n ih,
    { convert H0 using 1,
      rw [of_nat_zero, zero_add] },
    convert Hs _ (le_add_of_nonneg_left (of_nat_nonneg _)) ih using 1,
    rw [of_nat_succ, add_assoc, add_comm 1 b, ←add_assoc] },
  { induction n with n ih,
    { convert Hp _ le_rfl H0 using 1,
      rw [neg_succ_of_nat_eq, ←of_nat_eq_coe, of_nat_zero, zero_add, neg_add_eq_sub] },
    { convert Hp _ (le_of_lt (add_lt_of_neg_of_le (neg_succ_lt_zero _) le_rfl)) ih using 1,
      rw [neg_succ_of_nat_coe', nat.succ_eq_add_one, ←neg_succ_of_nat_coe, sub_add_eq_add_sub] } }
end

/-- See `int.induction_on'` for an induction in both directions. -/
protected lemma le_induction {P : ℤ → Prop} {m : ℤ} (h0 : P m)
  (h1 : ∀ (n : ℤ), m ≤ n → P n → P (n + 1)) (n : ℤ) :
  m ≤ n → P n :=
begin
  apply int.induction_on' n m,
  { intro _, exact h0, },
  { intros k hle hi _, exact h1 k hle (hi hle), },
  { intros _ hle _ hle',
    exfalso,
    exact lt_irrefl k (le_sub_one_iff.mp (hle.trans hle')), },
end

/-- See `int.induction_on'` for an induction in both directions. -/
protected lemma le_induction_down {P : ℤ → Prop} {m : ℤ} (h0 : P m)
  (h1 : ∀ (n : ℤ), n ≤ m → P n → P (n - 1)) (n : ℤ) :
  n ≤ m → P n :=
begin
  apply int.induction_on' n m,
  { intro _, exact h0, },
  { intros _ hle _ hle',
    exfalso,
    exact lt_irrefl k (add_one_le_iff.mp (hle'.trans hle)), },
  { intros k hle hi _,
    exact h1 k hle (hi hle), },
end

/-! ### nat abs -/

variables {a b : ℤ} {n : ℕ}

attribute [simp] nat_abs nat_abs_of_nat nat_abs_zero nat_abs_one

@[simp] lemma nat_abs_dvd_iff_dvd {a b : ℤ} : a.nat_abs ∣ b.nat_abs ↔ a ∣ b :=
begin
  refine ⟨_, λ ⟨k, hk⟩, ⟨k.nat_abs, hk.symm ▸ nat_abs_mul a k⟩⟩,
  rintro ⟨k, hk⟩,
  rw [←nat_abs_of_nat k, ←nat_abs_mul, nat_abs_eq_nat_abs_iff, neg_mul_eq_mul_neg] at hk,
  cases hk; exact ⟨_, hk⟩
end

/-! ### `/`  -/

protected theorem div_nonpos {a b : ℤ} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a / b ≤ 0 :=
nonpos_of_neg_nonneg $ by rw [← int.div_neg]; exact int.div_nonneg Ha (neg_nonneg_of_nonpos Hb)

theorem div_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < |b|) : a / b = 0 :=
match b, |b|, abs_eq_nat_abs b, H2 with
| (n : ℕ), ._, rfl, H2 := div_eq_zero_of_lt H1 H2
| -[1+ n], ._, rfl, H2 := neg_injective $ by rw [← int.div_neg]; exact div_eq_zero_of_lt H1 H2
end

protected theorem add_mul_div_right (a b : ℤ) {c : ℤ} (H : c ≠ 0) :
  (a + b * c) / c = a / c + b :=
have ∀ {k n : ℕ} {a : ℤ}, (a + n * k.succ) / k.succ = a / k.succ + n, from
λ k n a, match a with
| (m : ℕ) := congr_arg of_nat $ nat.add_mul_div_right _ _ k.succ_pos
| -[1+ m] := show ((n * k.succ:ℕ) - m.succ : ℤ) / k.succ =
                  n - (m / k.succ + 1 : ℕ), begin
  cases lt_or_ge m (n*k.succ) with h h,
  { rw [← int.coe_nat_sub h,
        ← int.coe_nat_sub ((nat.div_lt_iff_lt_mul k.succ_pos).2 h)],
    apply congr_arg of_nat,
    rw [mul_comm, nat.mul_sub_div], rwa mul_comm },
  { change (↑(n * nat.succ k) - (m + 1) : ℤ) / ↑(nat.succ k) =
           ↑n - ((m / nat.succ k : ℕ) + 1),
    rw [← sub_sub, ← sub_sub, ← neg_sub (m:ℤ), ← neg_sub _ (n:ℤ),
        ← int.coe_nat_sub h,
        ← int.coe_nat_sub ((nat.le_div_iff_mul_le k.succ_pos).2 h),
        ← neg_succ_of_nat_coe', ← neg_succ_of_nat_coe'],
    { apply congr_arg neg_succ_of_nat,
      rw [mul_comm, nat.sub_mul_div], rwa mul_comm } }
  end
end,
have ∀ {a b c : ℤ}, 0 < c → (a + b * c) / c = a / c + b, from
λ a b c H, match c, eq_succ_of_zero_lt H, b with
| ._, ⟨k, rfl⟩, (n : ℕ) := this
| ._, ⟨k, rfl⟩, -[1+ n] :=
  show (a - n.succ * k.succ) / k.succ = (a / k.succ) - n.succ, from
  eq_sub_of_add_eq $ by rw [← this, sub_add_cancel]
end,
match lt_trichotomy c 0 with
| or.inl hlt          := neg_inj.1 $ by rw [← int.div_neg, neg_add, ← int.div_neg, ← neg_mul_neg];
                         apply this (neg_pos_of_neg hlt)
| or.inr (or.inl heq) := absurd heq H
| or.inr (or.inr hgt) := this hgt
end

protected theorem add_mul_div_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b ≠ 0) :
    (a + b * c) / b = a / b + c :=
by rw [mul_comm, int.add_mul_div_right _ _ H]

@[simp] protected theorem mul_div_cancel (a : ℤ) {b : ℤ} (H : b ≠ 0) : a * b / b = a :=
by have := int.add_mul_div_right 0 a H;
   rwa [zero_add, int.zero_div, zero_add] at this

@[simp] protected theorem mul_div_cancel_left {a : ℤ} (b : ℤ) (H : a ≠ 0) : a * b / a = b :=
by rw [mul_comm, int.mul_div_cancel _ H]

@[simp] protected theorem div_self {a : ℤ} (H : a ≠ 0) : a / a = 1 :=
by have := int.mul_div_cancel 1 H; rwa one_mul at this

local attribute [simp] int.zero_div int.div_zero

protected theorem add_div_of_dvd_right {a b c : ℤ} (H : c ∣ b) :
  (a + b) / c = a / c + b / c :=
begin
  by_cases h1 : c = 0,
  { simp [h1] },
  cases H with k hk,
  rw hk,
  change c ≠ 0 at h1,
  rw [mul_comm c k, int.add_mul_div_right _ _ h1, ←zero_add (k * c), int.add_mul_div_right _ _ h1,
      int.zero_div, zero_add]
end

protected theorem add_div_of_dvd_left {a b c : ℤ} (H : c ∣ a) :
  (a + b) / c = a / c + b / c :=
by rw [add_comm, int.add_div_of_dvd_right H, add_comm]

/-! ### mod -/

@[simp] theorem mod_abs (a b : ℤ) : a % (|b|) = a % b :=
abs_by_cases (λ i, a % i = a % b) rfl (mod_neg _ _)

theorem mod_nonneg : ∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
| (m : ℕ) n H := coe_zero_le _
| -[1+ m] n H :=
  sub_nonneg_of_le $ coe_nat_le_coe_nat_of_le $ nat.mod_lt _ (nat_abs_pos_of_ne_zero H)

theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : 0 < b) : a % b < b :=
match a, b, eq_succ_of_zero_lt H with
| (m : ℕ), ._, ⟨n, rfl⟩ := coe_nat_lt_coe_nat_of_lt (nat.mod_lt _ (nat.succ_pos _))
| -[1+ m], ._, ⟨n, rfl⟩ := sub_lt_self _ (coe_nat_lt_coe_nat_of_lt $ nat.succ_pos _)
end

theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < |b| :=
by rw [← mod_abs]; exact mod_lt_of_pos _ (abs_pos.2 H)

@[simp] theorem add_mul_mod_self {a b c : ℤ} : (a + b * c) % c = a % c :=
if cz : c = 0 then by rw [cz, mul_zero, add_zero] else
by rw [mod_def, mod_def, int.add_mul_div_right _ _ cz,
       mul_add, mul_comm, add_sub_add_right_eq_sub]

@[simp] theorem add_mul_mod_self_left (a b c : ℤ) : (a + b * c) % b = a % b :=
by rw [mul_comm, add_mul_mod_self]

@[simp] theorem add_mod_self {a b : ℤ} : (a + b) % b = a % b :=
by have := add_mul_mod_self_left a b 1; rwa mul_one at this

@[simp] theorem add_mod_self_left {a b : ℤ} : (a + b) % a = b % a :=
by rw [add_comm, add_mod_self]

@[simp] theorem mod_add_mod (m n k : ℤ) : (m % n + k) % n = (m + k) % n :=
by have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm;
   rwa [add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : ℤ) : (m + n % k) % k = (m + n) % k :=
by rw [add_comm, mod_add_mod, add_comm]

lemma add_mod (a b n : ℤ) : (a + b) % n = ((a % n) + (b % n)) % n :=
by rw [add_mod_mod, mod_add_mod]

theorem add_mod_eq_add_mod_right {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (m + i) % n = (k + i) % n :=
by rw [← mod_add_mod, ← mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (i + m) % n = (i + k) % n :=
by rw [add_comm, add_mod_eq_add_mod_right _ H, add_comm]

theorem mod_add_cancel_right {m n k : ℤ} (i) : (m + i) % n = (k + i) % n ↔
  m % n = k % n :=
⟨λ H, by have := add_mod_eq_add_mod_right (-i) H;
      rwa [add_neg_cancel_right, add_neg_cancel_right] at this,
 add_mod_eq_add_mod_right _⟩

theorem mod_add_cancel_left {m n k i : ℤ} :
  (i + m) % n = (i + k) % n ↔ m % n = k % n :=
by rw [add_comm, add_comm i, mod_add_cancel_right]

theorem mod_sub_cancel_right {m n k : ℤ} (i) : (m - i) % n = (k - i) % n ↔
  m % n = k % n :=
mod_add_cancel_right _

@[simp] theorem mul_mod_left (a b : ℤ) : (a * b) % b = 0 :=
by rw [← zero_add (a * b), add_mul_mod_self, zero_mod]

@[simp] theorem mul_mod_right (a b : ℤ) : (a * b) % a = 0 :=
by rw [mul_comm, mul_mod_left]

lemma mul_mod (a b n : ℤ) : (a * b) % n = ((a % n) * (b % n)) % n :=
begin
  conv_lhs
  { rw [←mod_add_div a n, ←mod_add_div' b n, right_distrib, left_distrib, left_distrib,
        mul_assoc, mul_assoc, ←left_distrib n _ _, add_mul_mod_self_left, ← mul_assoc,
        add_mul_mod_self] }
end

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem mod_self {a : ℤ} : a % a = 0 :=
by have := mul_mod_left 1 a; rwa one_mul at this

@[simp] theorem mod_mod_of_dvd (n : ℤ) {m k : ℤ} (h : m ∣ k) : n % k % m = n % m :=
begin
  conv { to_rhs, rw ←mod_add_div n k },
  rcases h with ⟨t, rfl⟩, rw [mul_assoc, add_mul_mod_self_left]
end

@[simp] theorem mod_mod (a b : ℤ) : a % b % b = a % b :=
by conv {to_rhs, rw [← mod_add_div a b, add_mul_mod_self_left]}

lemma sub_mod (a b n : ℤ) : (a - b) % n = ((a % n) - (b % n)) % n :=
begin
  apply (mod_add_cancel_right b).mp,
  rw [sub_add_cancel, ← add_mod_mod, sub_add_cancel, mod_mod]
end

/-- See also `int.div_mod_equiv` for a similar statement as an `equiv`. -/
protected theorem div_mod_unique {a b r q : ℤ} (h : 0 < b) :
  a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < b :=
begin
  split,
  { rintro ⟨rfl, rfl⟩,
    exact ⟨mod_add_div a b, mod_nonneg _ h.ne.symm, mod_lt_of_pos _ h⟩, },
  { rintro ⟨rfl, hz, hb⟩,
    split,
    { rw [int.add_mul_div_left r q (ne_of_gt h), div_eq_zero_of_lt hz hb],
      simp, },
    { rw [add_mul_mod_self_left, mod_eq_of_lt hz hb] } },
end

local attribute [simp] int.zero_mod

theorem mod_eq_mod_iff_mod_sub_eq_zero {m n k : ℤ} : m % n = k % n ↔ (m - k) % n = 0 :=
(mod_sub_cancel_right k).symm.trans $ by simp

@[simp] lemma neg_mod_two (i : ℤ) : (-i) % 2 = i % 2 :=
begin
  apply int.mod_eq_mod_iff_mod_sub_eq_zero.mpr,
  convert int.mul_mod_right 2 (-i),
  simp only [two_mul, sub_eq_add_neg]
end

/-! ### properties of `/` and `%` -/

theorem lt_div_add_one_mul_self (a : ℤ) {b : ℤ} (H : 0 < b) : a < (a / b + 1) * b :=
by { rw [add_mul, one_mul, mul_comm, ← sub_lt_iff_lt_add', ← mod_def],
  exact mod_lt_of_pos _ H }

theorem abs_div_le_abs : ∀ (a b : ℤ), |a / b| ≤ |a| :=
suffices ∀ (a : ℤ) (n : ℕ), |a / n| ≤ |a|, from
λ a b, match b, eq_coe_or_neg b with
| ._, ⟨n, or.inl rfl⟩ := this _ _
| ._, ⟨n, or.inr rfl⟩ := by rw [int.div_neg, abs_neg]; apply this
end,
λ a n, by rw [abs_eq_nat_abs, abs_eq_nat_abs]; exact
coe_nat_le_coe_nat_of_le (match a, n with
| (m : ℕ), n := nat.div_le_self _ _
| -[1+ m], 0 := nat.zero_le _
| -[1+ m], n+1 := nat.succ_le_succ (nat.div_le_self _ _)
end)

theorem div_le_self {a : ℤ} (b : ℤ) (Ha : 0 ≤ a) : a / b ≤ a :=
by have := le_trans (le_abs_self _) (abs_div_le_abs a b);
   rwa [abs_of_nonneg Ha] at this

lemma mod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
have h : n % 2 < 2 := abs_of_nonneg (show 0 ≤ (2 : ℤ), from dec_trivial) ▸ int.mod_lt _ dec_trivial,
have h₁ : 0 ≤ n % 2 := int.mod_nonneg _ dec_trivial,
match (n % 2), h, h₁ with
| (0 : ℕ) := λ _ _, or.inl rfl
| (1 : ℕ) := λ _ _, or.inr rfl
| (k + 2 : ℕ) := λ h _, absurd h dec_trivial
| -[1+ a] := λ _ h₁, absurd h₁ dec_trivial
end

/-! ### dvd -/

theorem dvd_of_mod_eq_zero {a b : ℤ} (H : b % a = 0) : a ∣ b :=
⟨b / a, (mul_div_cancel_of_mod_eq_zero H).symm⟩

theorem mod_eq_zero_of_dvd : ∀ {a b : ℤ}, a ∣ b → b % a = 0
| a ._ ⟨c, rfl⟩ := mul_mod_right _ _

theorem dvd_iff_mod_eq_zero (a b : ℤ) : a ∣ b ↔ b % a = 0 :=
⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

/-- If `a % b = c` then `b` divides `a - c`. -/
lemma dvd_sub_of_mod_eq {a b c : ℤ} (h : a % b = c) : b ∣ a - c :=
begin
  have hx : a % b % b = c % b, { rw h },
  rw [mod_mod, ←mod_sub_cancel_right c, sub_self, zero_mod] at hx,
  exact dvd_of_mod_eq_zero hx
end

theorem nat_abs_dvd {a b : ℤ} : (a.nat_abs : ℤ) ∣ b ↔ a ∣ b :=
(nat_abs_eq a).elim (λ e, by rw ← e) (λ e, by rw [← neg_dvd, ← e])

theorem dvd_nat_abs {a b : ℤ} : a ∣ b.nat_abs ↔ a ∣ b :=
(nat_abs_eq b).elim (λ e, by rw ← e) (λ e, by rw [← dvd_neg, ← e])

instance decidable_dvd : @decidable_rel ℤ (∣) :=
assume a n, decidable_of_decidable_of_iff (by apply_instance) (dvd_iff_mod_eq_zero _ _).symm

protected theorem div_mul_cancel {a b : ℤ} (H : b ∣ a) : a / b * b = a :=
div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

protected theorem mul_div_cancel' {a b : ℤ} (H : a ∣ b) : a * (b / a) = b :=
by rw [mul_comm, int.div_mul_cancel H]

theorem div_dvd_div : ∀ {a b c : ℤ} (H1 : a ∣ b) (H2 : b ∣ c), b / a ∣ c / a
| a ._ ._ ⟨b, rfl⟩ ⟨c, rfl⟩ := if az : a = 0 then by simp [az] else
  by rw [int.mul_div_cancel_left _ az, mul_assoc, int.mul_div_cancel_left _ az];
     apply dvd_mul_right

protected theorem eq_mul_of_div_eq_right {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = b * c :=
by rw [← H2, int.mul_div_cancel' H1]

protected theorem div_eq_of_eq_mul_right {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = b * c) :
  a / b = c :=
by rw [H2, int.mul_div_cancel_left _ H1]

protected theorem eq_div_of_mul_eq_right {a b c : ℤ} (H1 : a ≠ 0) (H2 : a * b = c) :
  b = c / a :=
eq.symm $ int.div_eq_of_eq_mul_right H1 H2.symm

protected theorem div_eq_iff_eq_mul_right {a b c : ℤ} (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = b * c :=
⟨int.eq_mul_of_div_eq_right H', int.div_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : ℤ} (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = c * b :=
by rw mul_comm; exact int.div_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_left {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = c * b :=
by rw [mul_comm, int.eq_mul_of_div_eq_right H1 H2]

protected theorem div_eq_of_eq_mul_left {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = c * b) :
  a / b = c :=
int.div_eq_of_eq_mul_right H1 (by rw [mul_comm, H2])

protected lemma eq_zero_of_div_eq_zero {d n : ℤ} (h : d ∣ n) (H : n / d = 0) : n = 0 :=
by rw [← int.mul_div_cancel' h, H, mul_zero]

@[simp]
protected lemma div_left_inj {a b d : ℤ} (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  rw [←int.mul_div_cancel' hda, ←int.mul_div_cancel' hdb, h],
end

lemma abs_sign_of_nonzero {z : ℤ} (hz : z ≠ 0) : |z.sign| = 1 :=
by rw [abs_eq_nat_abs, nat_abs_sign_of_nonzero hz, int.coe_nat_one]

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) {n : ℤ} (hn : 0 < n) :
  (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬ n ∣ m :=
begin
  split,
  { rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩, rw [mul_lt_mul_left hn] at h1k h2k,
    rw [lt_add_one_iff, ← not_lt] at h2k, exact h2k h1k },
  { intro h, rw [dvd_iff_mod_eq_zero, ← ne.def] at h,
    have := (mod_nonneg m hn.ne.symm).lt_of_ne h.symm,
    simp only [← mod_add_div m n] {single_pass := tt},
    refine ⟨m / n, lt_add_of_pos_left _ this, _⟩,
    rw [add_comm _ (1 : ℤ), left_distrib, mul_one], exact add_lt_add_right (mod_lt_of_pos _ hn) _ }
end

local attribute [simp] int.div_zero

protected theorem mul_div_assoc (a : ℤ) : ∀ {b c : ℤ}, c ∣ b → (a * b) / c = a * (b / c)
| ._ c ⟨d, rfl⟩ := if cz : c = 0 then by simp [cz] else
  by rw [mul_left_comm, int.mul_div_cancel_left _ cz, int.mul_div_cancel_left _ cz]

protected theorem mul_div_assoc' (b : ℤ) {a c : ℤ} (h : c ∣ a) : a * b / c = a / c * b :=
by rw [mul_comm, int.mul_div_assoc _ h, mul_comm]

theorem neg_div_of_dvd : ∀ {a b : ℤ} (H : b ∣ a), -a / b = -(a / b)
| ._ b ⟨c, rfl⟩ := if bz : b = 0 then by simp [bz] else
  by rw [neg_mul_eq_mul_neg, int.mul_div_cancel_left _ bz, int.mul_div_cancel_left _ bz]

lemma sub_div_of_dvd (a : ℤ) {b c : ℤ} (hcb : c ∣ b) : (a - b) / c = a / c - b / c :=
begin
  rw [sub_eq_add_neg, sub_eq_add_neg, int.add_div_of_dvd_right ((dvd_neg c b).mpr hcb)],
  congr,
  exact neg_div_of_dvd hcb,
end

lemma sub_div_of_dvd_sub {a b c : ℤ} (hcab : c ∣ (a - b)) : (a - b) / c = a / c - b / c :=
by rw [eq_sub_iff_add_eq, ← int.add_div_of_dvd_left hcab, sub_add_cancel]

protected theorem sign_eq_div_abs (a : ℤ) : sign a = a / |a| :=
if az : a = 0 then by simp [az] else
(int.div_eq_of_eq_mul_left (mt abs_eq_zero.1 az)
  (sign_mul_abs _).symm).symm

/-! ### `/` and ordering -/

protected theorem div_mul_le (a : ℤ) {b : ℤ} (H : b ≠ 0) : a / b * b ≤ a :=
le_of_sub_nonneg $ by rw [mul_comm, ← mod_def]; apply mod_nonneg _ H

protected theorem div_le_of_le_mul {a b c : ℤ} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b :=
le_of_mul_le_mul_right (le_trans (int.div_mul_le _ (ne_of_gt H)) H') H

protected theorem mul_lt_of_lt_div {a b c : ℤ} (H : 0 < c) (H3 : a < b / c) : a * c < b :=
lt_of_not_ge $ mt (int.div_le_of_le_mul H) (not_le_of_gt H3)

protected theorem mul_le_of_le_div {a b c : ℤ} (H1 : 0 < c) (H2 : a ≤ b / c) : a * c ≤ b :=
le_trans (mul_le_mul_of_nonneg_right H2 (le_of_lt H1)) (int.div_mul_le _ (ne_of_gt H1))

protected theorem le_div_of_mul_le {a b c : ℤ} (H1 : 0 < c) (H2 : a * c ≤ b) : a ≤ b / c :=
le_of_lt_add_one $ lt_of_mul_lt_mul_right
  (lt_of_le_of_lt H2 (lt_div_add_one_mul_self _ H1)) (le_of_lt H1)

protected theorem le_div_iff_mul_le {a b c : ℤ} (H : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
⟨int.mul_le_of_le_div H, int.le_div_of_mul_le H⟩

protected theorem div_le_div {a b c : ℤ} (H : 0 < c) (H' : a ≤ b) : a / c ≤ b / c :=
int.le_div_of_mul_le H (le_trans (int.div_mul_le _ (ne_of_gt H)) H')

protected theorem div_lt_of_lt_mul {a b c : ℤ} (H : 0 < c) (H' : a < b * c) : a / c < b :=
lt_of_not_ge $ mt (int.mul_le_of_le_div H) (not_le_of_gt H')

protected theorem lt_mul_of_div_lt {a b c : ℤ} (H1 : 0 < c) (H2 : a / c < b) : a < b * c :=
lt_of_not_ge $ mt (int.le_div_of_mul_le H1) (not_le_of_gt H2)

protected theorem div_lt_iff_lt_mul {a b c : ℤ} (H : 0 < c) : a / c < b ↔ a < b * c :=
⟨int.lt_mul_of_div_lt H, int.div_lt_of_lt_mul H⟩

protected theorem le_mul_of_div_le {a b c : ℤ} (H1 : 0 ≤ b) (H2 : b ∣ a) (H3 : a / b ≤ c) :
  a ≤ c * b :=
by rw [← int.div_mul_cancel H2]; exact mul_le_mul_of_nonneg_right H3 H1

protected theorem lt_div_of_mul_lt {a b c : ℤ} (H1 : 0 ≤ b) (H2 : b ∣ c) (H3 : a * b < c) :
  a < c / b :=
lt_of_not_ge $ mt (int.le_mul_of_div_le H1 H2) (not_le_of_gt H3)

protected theorem lt_div_iff_mul_lt {a b : ℤ} (c : ℤ) (H : 0 < c) (H' : c ∣ b) :
  a < b / c ↔ a * c < b :=
⟨int.mul_lt_of_lt_div H, int.lt_div_of_mul_lt (le_of_lt H) H'⟩

theorem div_pos_of_pos_of_dvd {a b : ℤ} (H1 : 0 < a) (H2 : 0 ≤ b) (H3 : b ∣ a) : 0 < a / b :=
int.lt_div_of_mul_lt H2 H3 (by rwa zero_mul)

lemma nat_abs_eq_of_dvd_dvd {s t : ℤ} (hst : s ∣ t) (hts : t ∣ s) : nat_abs s = nat_abs t :=
nat.dvd_antisymm (nat_abs_dvd_iff_dvd.mpr hst) (nat_abs_dvd_iff_dvd.mpr hts)

theorem div_eq_div_of_mul_eq_mul {a b c d : ℤ} (H2 : d ∣ c) (H3 : b ≠ 0)
    (H4 : d ≠ 0) (H5 : a * d = b * c) :
  a / b = c / d :=
int.div_eq_of_eq_mul_right H3 $
by rw [← int.mul_div_assoc _ H2]; exact
(int.div_eq_of_eq_mul_left H4 H5.symm).symm

lemma div_dvd_of_dvd {s t : ℤ} (hst : s ∣ t) : (t / s) ∣ t :=
begin
  rcases eq_or_ne s 0 with rfl | hs,
  { simpa using hst },
  rcases hst with ⟨c, hc⟩,
  simp [hc, int.mul_div_cancel_left _ hs],
end

/-! ### to_nat -/

@[simp] theorem to_nat_le {a : ℤ} {n : ℕ} : to_nat a ≤ n ↔ a ≤ n :=
by rw [(coe_nat_le_coe_nat_iff _ _).symm, to_nat_eq_max, max_le_iff];
   exact and_iff_left (coe_zero_le _)

@[simp] theorem lt_to_nat {n : ℕ} {a : ℤ} : n < to_nat a ↔ (n : ℤ) < a :=
le_iff_le_iff_lt_iff_lt.1 to_nat_le

@[simp]
lemma coe_nat_nonpos_iff {n : ℕ} : (n : ℤ) ≤ 0 ↔ n = 0 :=
⟨ λ h, le_antisymm (int.coe_nat_le.mp (h.trans int.coe_nat_zero.le)) n.zero_le,
  λ h, (coe_nat_eq_zero.mpr h).le⟩

theorem to_nat_le_to_nat {a b : ℤ} (h : a ≤ b) : to_nat a ≤ to_nat b :=
by rw to_nat_le; exact le_trans h (le_to_nat b)

theorem to_nat_lt_to_nat {a b : ℤ} (hb : 0 < b) : to_nat a < to_nat b ↔ a < b :=
⟨λ h, begin cases a, exact lt_to_nat.1 h, exact lt_trans (neg_succ_of_nat_lt_zero a) hb, end,
 λ h, begin rw lt_to_nat, cases a, exact h, exact hb end⟩

theorem lt_of_to_nat_lt {a b : ℤ} (h : to_nat a < to_nat b) : a < b :=
(to_nat_lt_to_nat $ lt_to_nat.1 $ lt_of_le_of_lt (nat.zero_le _) h).1 h

@[simp]
lemma to_nat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.to_nat - 1 : ℕ) : ℤ) = i - 1 :=
by simp [h, le_of_lt h] with push_cast

@[simp]
lemma to_nat_eq_zero : ∀ {n : ℤ}, n.to_nat = 0 ↔ n ≤ 0
| (n : ℕ) := calc _ ↔ (n = 0) : ⟨(to_nat_coe_nat n).symm.trans, (to_nat_coe_nat n).trans⟩
                ... ↔ _       : coe_nat_nonpos_iff.symm
| -[1+ n] := show ((-((n : ℤ) + 1)).to_nat = 0) ↔ (-(n + 1) : ℤ) ≤ 0, from
calc _ ↔ true : ⟨λ _, trivial, λ h, to_nat_neg_nat _⟩
   ... ↔ _    : ⟨λ h, neg_nonpos_of_nonneg (coe_zero_le _), λ _, trivial⟩

@[simp] lemma to_nat_sub_of_le {a b : ℤ} (h : b ≤ a) : (to_nat (a - b) : ℤ) = a - b :=
int.to_nat_of_nonneg (sub_nonneg_of_le h)

end int

-- We should need only a minimal development of sets in order to get here.
assert_not_exists set.range
