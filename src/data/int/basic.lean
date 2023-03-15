/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.nat.basic
import order.monotone.basic

/-!
# Basic instances on the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains:
* instances on `ℤ`. The stronger one is `int.comm_ring`.
  See `data/int/defs/order` for `int.linear_ordered_comm_ring`.
* basic lemmas about the integers, but which do not use the ordered algebra hierarchy.
-/

open nat

namespace int

instance : inhabited ℤ := ⟨int.zero⟩

instance : nontrivial ℤ :=
⟨⟨0, 1, int.zero_ne_one⟩⟩

instance : comm_ring ℤ :=
{ add            := int.add,
  add_assoc      := int.add_assoc,
  zero           := int.zero,
  zero_add       := int.zero_add,
  add_zero       := int.add_zero,
  neg            := int.neg,
  add_left_neg   := int.add_left_neg,
  add_comm       := int.add_comm,
  mul            := int.mul,
  mul_assoc      := int.mul_assoc,
  one            := int.one,
  one_mul        := int.one_mul,
  mul_one        := int.mul_one,
  sub            := int.sub,
  left_distrib   := int.distrib_left,
  right_distrib  := int.distrib_right,
  mul_comm       := int.mul_comm,
  nat_cast       := int.of_nat,
  nat_cast_zero  := rfl,
  nat_cast_succ  := λ n, rfl,
  int_cast       := λ n, n,
  int_cast_of_nat := λ n, rfl,
  int_cast_neg_succ_of_nat := λ n, rfl,
  zsmul          := (*),
  zsmul_zero'    := int.zero_mul,
  zsmul_succ'    := λ n x, by rw [nat.succ_eq_add_one, nat.add_comm, of_nat_add, int.distrib_right,
                      of_nat_one, int.one_mul],
  zsmul_neg'     := λ n x, int.neg_mul_eq_neg_mul_symm (n.succ : ℤ) x }


/-! ### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `int.normed_comm_ring` being used to construct
these instances non-computably.
-/
-- instance : has_sub int            := by apply_instance -- This is in core
instance : add_comm_monoid ℤ    := by apply_instance
instance : add_monoid ℤ         := by apply_instance
instance : monoid ℤ             := by apply_instance
instance : comm_monoid ℤ        := by apply_instance
instance : comm_semigroup ℤ     := by apply_instance
instance : semigroup ℤ          := by apply_instance
instance : add_comm_group ℤ     := by apply_instance
instance : add_group ℤ          := by apply_instance
instance : add_comm_semigroup ℤ := by apply_instance
instance : add_semigroup ℤ      := by apply_instance
instance : comm_semiring ℤ      := by apply_instance
instance : semiring ℤ           := by apply_instance
instance : ring ℤ               := by apply_instance
instance : distrib ℤ            := by apply_instance

end int


namespace int

@[simp] lemma add_neg_one (i : ℤ) : i + -1 = i - 1 := rfl

@[simp] lemma default_eq_zero : default = (0 : ℤ) := rfl

meta instance : has_to_format ℤ := ⟨λ z, to_string z⟩

section
-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `int.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
local attribute [semireducible] reflected
meta instance reflect : has_reflect ℤ :=
int.mk_numeral `(ℤ) `(by apply_instance : has_zero ℤ) `(by apply_instance : has_one ℤ)
                    `(by apply_instance : has_add ℤ) `(by apply_instance : has_neg ℤ)
end

attribute [simp] int.bodd

@[simp] theorem add_def {a b : ℤ} : int.add a b = a + b := rfl
@[simp] theorem mul_def {a b : ℤ} : int.mul a b = a * b := rfl

@[simp] lemma neg_succ_not_nonneg (n : ℕ) : 0 ≤ -[1+ n] ↔ false :=
by { simp only [not_le, iff_false], exact int.neg_succ_lt_zero n, }

@[simp] lemma neg_succ_not_pos (n : ℕ) : 0 < -[1+ n] ↔ false :=
by simp only [not_lt, iff_false]

@[simp] lemma neg_succ_sub_one (n : ℕ) : -[1+ n] - 1 = -[1+ (n+1)] := rfl
@[simp] theorem coe_nat_mul_neg_succ (m n : ℕ) : (m : ℤ) * -[1+ n] = -(m * succ n) := rfl
@[simp] theorem neg_succ_mul_coe_nat (m n : ℕ) : -[1+ m] * n = -(succ m * n) := rfl
@[simp] theorem neg_succ_mul_neg_succ (m n : ℕ) : -[1+ m] * -[1+ n] = succ m * succ n := rfl

theorem coe_nat_le {m n : ℕ} : (↑m : ℤ) ≤ ↑n ↔ m ≤ n := coe_nat_le_coe_nat_iff m n
theorem coe_nat_lt {m n : ℕ} : (↑m : ℤ) < ↑n ↔ m < n := coe_nat_lt_coe_nat_iff m n
theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n := int.coe_nat_eq_coe_nat_iff m n

lemma coe_nat_strict_mono : strict_mono (coe : ℕ → ℤ) := λ _ _, int.coe_nat_lt.2

lemma coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := coe_nat_le.2 (nat.zero_le _)

@[simp] lemma neg_of_nat_ne_zero (n : ℕ) : -[1+ n] ≠ 0 := λ h, int.no_confusion h
@[simp] lemma zero_ne_neg_of_nat (n : ℕ) : 0 ≠ -[1+ n] := λ h, int.no_confusion h

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1

theorem nat_succ_eq_int_succ (n : ℕ) : (nat.succ n : ℤ) = int.succ n := rfl

theorem pred_succ (a : ℤ) : pred (succ a) = a := add_sub_cancel _ _

theorem succ_pred (a : ℤ) : succ (pred a) = a := sub_add_cancel _ _

theorem neg_succ (a : ℤ) : -succ a = pred (-a) := neg_add _ _

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
by rw [neg_succ, succ_pred]

theorem neg_pred (a : ℤ) : -pred a = succ (-a) :=
by rw [neg_eq_iff_eq_neg.mp (neg_succ (-a)), neg_neg]

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
by rw [neg_pred, pred_succ]

theorem pred_nat_succ (n : ℕ) : pred (nat.succ n) = n := pred_succ n

theorem neg_nat_succ (n : ℕ) : -(nat.succ n : ℤ) = pred (-n) := neg_succ n

theorem succ_neg_nat_succ (n : ℕ) : succ (-nat.succ n) = -n := succ_neg_succ n

theorem add_one_le_iff {a b : ℤ} : a + 1 ≤ b ↔ a < b := iff.rfl

@[norm_cast] lemma coe_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 :=
by { cases n, cases h, simp, }

@[elab_as_eliminator] protected lemma induction_on {p : ℤ → Prop}
  (i : ℤ) (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i :=
begin
  induction i,
  { induction i,
    { exact hz },
    { exact hp _ i_ih } },
  { have : ∀ n:ℕ, p (- n),
    { intro n, induction n,
      { simp [hz] },
      { convert hn _ n_ih using 1, simp [sub_eq_neg_add] } },
    exact this (i + 1) }
end

/-! ### nat abs -/

variables {a b : ℤ} {n : ℕ}

attribute [simp] nat_abs_of_nat nat_abs_zero nat_abs_one

theorem nat_abs_add_le (a b : ℤ) : nat_abs (a + b) ≤ nat_abs a + nat_abs b :=
begin
  have : ∀ (a b : ℕ), nat_abs (sub_nat_nat a (nat.succ b)) ≤ nat.succ (a + b),
  { refine (λ a b : ℕ, sub_nat_nat_elim a b.succ
      (λ m n i, n = b.succ → nat_abs i ≤ (m + b).succ) _ (λ i n e, _) rfl),
    { rintro i n rfl,
      rw [add_comm _ i, add_assoc],
      exact nat.le_add_right i (b.succ + b).succ },
    { apply succ_le_succ,
      rw [← succ.inj e, ← add_assoc, add_comm],
      apply nat.le_add_right } },
  cases a; cases b with b b; simp [nat_abs, nat.succ_add];
  try {refl}; [skip, rw add_comm a b]; apply this
end

lemma nat_abs_sub_le (a b : ℤ) : nat_abs (a - b) ≤ nat_abs a + nat_abs b :=
by { rw [sub_eq_add_neg, ← int.nat_abs_neg b], apply nat_abs_add_le }

theorem nat_abs_neg_of_nat (n : ℕ) : nat_abs (neg_of_nat n) = n :=
by cases n; refl

theorem nat_abs_mul (a b : ℤ) : nat_abs (a * b) = (nat_abs a) * (nat_abs b) :=
by cases a; cases b;
  simp only [← int.mul_def, int.mul, nat_abs_neg_of_nat, eq_self_iff_true, int.nat_abs]

lemma nat_abs_mul_nat_abs_eq {a b : ℤ} {c : ℕ} (h : a * b = (c : ℤ)) :
  a.nat_abs * b.nat_abs = c :=
by rw [← nat_abs_mul, h, nat_abs_of_nat]

lemma nat_abs_mul_self' (a : ℤ) : (nat_abs a * nat_abs a : ℤ) = a * a :=
by rw [← int.coe_nat_mul, nat_abs_mul_self]

theorem neg_succ_of_nat_eq' (m : ℕ) : -[1+ m] = -m - 1 :=
by simp [neg_succ_of_nat_eq, sub_eq_neg_add]

lemma nat_abs_ne_zero_of_ne_zero {z : ℤ} (hz : z ≠ 0) : z.nat_abs ≠ 0 :=
λ h, hz $ int.eq_zero_of_nat_abs_eq_zero h

@[simp] lemma nat_abs_eq_zero {a : ℤ} : a.nat_abs = 0 ↔ a = 0 :=
⟨int.eq_zero_of_nat_abs_eq_zero, λ h, h.symm ▸ rfl⟩

lemma nat_abs_ne_zero {a : ℤ} : a.nat_abs ≠ 0 ↔ a ≠ 0 := not_congr int.nat_abs_eq_zero

lemma nat_abs_lt_nat_abs_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) :
  a.nat_abs < b.nat_abs :=
begin
  lift b to ℕ using le_trans w₁ (le_of_lt w₂),
  lift a to ℕ using w₁,
  simpa [coe_nat_lt] using w₂,
end

lemma nat_abs_eq_nat_abs_iff {a b : ℤ} : a.nat_abs = b.nat_abs ↔ a = b ∨ a = -b :=
begin
  split; intro h,
  { cases int.nat_abs_eq a with h₁ h₁; cases int.nat_abs_eq b with h₂ h₂;
    rw [h₁, h₂]; simp [h], },
  { cases h; rw h, rw int.nat_abs_neg, },
end

lemma nat_abs_eq_iff {a : ℤ} {n : ℕ} : a.nat_abs = n ↔ a = n ∨ a = -n :=
by rw [←int.nat_abs_eq_nat_abs_iff, int.nat_abs_of_nat]

/-! ### `/`  -/

@[simp] theorem of_nat_div (m n : ℕ) : of_nat (m / n) = (of_nat m) / (of_nat n) := rfl

@[simp, norm_cast] theorem coe_nat_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := rfl

theorem neg_succ_of_nat_div (m : ℕ) {b : ℤ} (H : 0 < b) :
  -[1+m] / b = -(m / b + 1) :=
match b, eq_succ_of_zero_lt H with ._, ⟨n, rfl⟩ := rfl end

-- Will be generalized to Euclidean domains.
local attribute [simp]
protected theorem zero_div : ∀ (b : ℤ), 0 / b = 0
| (n:ℕ) := show of_nat _ = _, by simp
| -[1+ n] := show -of_nat _ = _, by simp

local attribute [simp] -- Will be generalized to Euclidean domains.
protected theorem div_zero : ∀ (a : ℤ), a / 0 = 0
| (n:ℕ) := show of_nat _ = _, by simp
| -[1+ n] := rfl

@[simp] protected theorem div_neg : ∀ (a b : ℤ), a / -b = -(a / b)
| (m : ℕ) 0       := show of_nat (m / 0) = -(m / 0 : ℕ), by rw nat.div_zero; refl
| (m : ℕ) (n+1:ℕ) := rfl
| (m : ℕ) -[1+ n] := (neg_neg _).symm
| -[1+ m] 0       := rfl
| -[1+ m] (n+1:ℕ) := rfl
| -[1+ m] -[1+ n] := rfl


theorem div_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b = -((-a - 1) / b + 1) :=
match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ :=
  by change (- -[1+ m] : ℤ) with (m+1 : ℤ); rw add_sub_cancel; refl
end

protected theorem div_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b :=
match a, b, eq_coe_of_zero_le Ha, eq_coe_of_zero_le Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ := coe_zero_le _
end

theorem div_neg' {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 :=
match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ := neg_succ_lt_zero _
end

@[simp] protected theorem div_one : ∀ (a : ℤ), a / 1 = a
| (n:ℕ) := congr_arg of_nat (nat.div_one _)
| -[1+ n] := congr_arg neg_succ_of_nat (nat.div_one _)

theorem div_eq_zero_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
match a, b, eq_coe_of_zero_le H1, eq_succ_of_zero_lt (lt_of_le_of_lt H1 H2), H2  with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 :=
  congr_arg of_nat $ nat.div_eq_of_lt $ lt_of_coe_nat_lt_coe_nat H2
end

/-! ### mod -/

theorem of_nat_mod (m n : nat) : (m % n : ℤ) = of_nat (m % n) := rfl

@[simp, norm_cast] theorem coe_nat_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl

theorem neg_succ_of_nat_mod (m : ℕ) {b : ℤ} (bpos : 0 < b) :
  -[1+m] % b = b - 1 - m % b :=
by rw [sub_sub, add_comm]; exact
match b, eq_succ_of_zero_lt bpos with ._, ⟨n, rfl⟩ := rfl end

@[simp] theorem mod_neg : ∀ (a b : ℤ), a % -b = a % b
| (m : ℕ) n := @congr_arg ℕ ℤ _ _ (λ i, ↑(m % i)) (nat_abs_neg _)
| -[1+ m] n := @congr_arg ℕ ℤ _ _ (λ i, sub_nat_nat i (nat.succ (m % i))) (nat_abs_neg _)

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem zero_mod (b : ℤ) : 0 % b = 0 := rfl

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem mod_zero : ∀ (a : ℤ), a % 0 = a
| (m : ℕ) := congr_arg of_nat $ nat.mod_zero _
| -[1+ m] := congr_arg neg_succ_of_nat $ nat.mod_zero _

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem mod_one : ∀ (a : ℤ), a % 1 = 0
| (m : ℕ) := congr_arg of_nat $ nat.mod_one _
| -[1+ m] := show (1 - (m % 1).succ : ℤ) = 0, by rw nat.mod_one; refl

theorem mod_eq_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
match a, b, eq_coe_of_zero_le H1, eq_coe_of_zero_le (le_trans H1 (le_of_lt H2)), H2 with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 :=
  congr_arg of_nat $ nat.mod_eq_of_lt (lt_of_coe_nat_lt_coe_nat H2)
end

theorem mod_add_div_aux (m n : ℕ) : (n - (m % n + 1) - (n * (m / n) + n) : ℤ) = -[1+ m] :=
begin
  rw [← sub_sub, neg_succ_of_nat_coe, sub_sub (n:ℤ), eq_comm, neg_eq_iff_eq_neg,
      neg_sub, sub_sub_self, add_right_comm],
  exact @congr_arg ℕ ℤ _ _ (λi, (i + 1 : ℤ)) (nat.mod_add_div _ _).symm
end

theorem mod_add_div : ∀ (a b : ℤ), a % b + b * (a / b) = a
| (m : ℕ) (n : ℕ) := congr_arg of_nat (nat.mod_add_div _ _)
| (m : ℕ) -[1+ n] := show (_ + -(n+1) * -((m) / (n + 1) : ℕ) : ℤ) = _,
  by rw [neg_mul_neg]; exact congr_arg of_nat (nat.mod_add_div _ _)
| -[1+ m] 0       := by rw [mod_zero, int.div_zero]; refl
| -[1+ m] (n+1:ℕ) := mod_add_div_aux m n.succ
| -[1+ m] -[1+ n] := mod_add_div_aux m n.succ

theorem div_add_mod (a b : ℤ) : b * (a / b) + a % b = a :=
(add_comm _ _).trans (mod_add_div _ _)

lemma mod_add_div' (m k : ℤ) : m % k + (m / k) * k = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : ℤ) : (m / k) * k + m % k = m :=
by { rw mul_comm, exact div_add_mod _ _ }

theorem mod_def (a b : ℤ) : a % b = a - b * (a / b) :=
eq_sub_of_add_eq (mod_add_div _ _)

/-! ### properties of `/` and `%` -/

@[simp] theorem mul_div_mul_of_pos {a : ℤ} (b c : ℤ) (H : 0 < a) : a * b / (a * c) = b / c :=
suffices ∀ (m k : ℕ) (b : ℤ), (m.succ * b / (m.succ * k) : ℤ) = b / k, from
match a, eq_succ_of_zero_lt H, c, eq_coe_or_neg c with
| ._, ⟨m, rfl⟩, ._, ⟨k, or.inl rfl⟩ := this _ _ _
| ._, ⟨m, rfl⟩, ._, ⟨k, or.inr rfl⟩ :=
  by rw [mul_neg, int.div_neg, int.div_neg];
     apply congr_arg has_neg.neg; apply this
end,
λ m k b, match b, k with
| (n : ℕ), k   := congr_arg of_nat (nat.mul_div_mul _ _ m.succ_pos)
| -[1+ n], 0   := by rw [int.coe_nat_zero, mul_zero, int.div_zero, int.div_zero]
| -[1+ n], k+1 := congr_arg neg_succ_of_nat $
  show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ, begin
    apply nat.div_eq_of_lt_le,
    { refine le_trans _ (nat.le_add_right _ _),
      rw [← nat.mul_div_mul _ _ m.succ_pos],
      apply nat.div_mul_le_self },
    { change m.succ * n.succ ≤ _,
      rw [mul_left_comm],
      apply nat.mul_le_mul_left,
      apply (nat.div_lt_iff_lt_mul k.succ_pos).1,
      apply nat.lt_succ_self }
  end
end

@[simp] theorem mul_div_mul_of_pos_left (a : ℤ) {b : ℤ} (H : 0 < b) (c : ℤ) :
  a * b / (c * b) = a / c :=
by rw [mul_comm, mul_comm c, mul_div_mul_of_pos _ _ H]

@[simp] theorem mul_mod_mul_of_pos {a : ℤ} (H : 0 < a) (b c : ℤ) : a * b % (a * c) = a * (b % c) :=
by rw [mod_def, mod_def, mul_div_mul_of_pos _ _ H, mul_sub_left_distrib, mul_assoc]

theorem mul_div_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : b * (a / b) = a :=
by have := mod_add_div a b; rwa [H, zero_add] at this

theorem div_mul_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : a / b * b = a :=
by rw [mul_comm, mul_div_cancel_of_mod_eq_zero H]

lemma nat_abs_sign (z : ℤ) :
  z.sign.nat_abs = if z = 0 then 0 else 1 :=
by rcases z with (_ | _) | _; refl

lemma nat_abs_sign_of_nonzero {z : ℤ} (hz : z ≠ 0) :
  z.sign.nat_abs = 1 :=
by rw [int.nat_abs_sign, if_neg hz]

lemma sign_coe_nat_of_nonzero {n : ℕ} (hn : n ≠ 0) :
  int.sign n = 1 :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn,
  exact int.sign_of_succ n
end

@[simp] lemma sign_neg (z : ℤ) :
  int.sign (-z) = -int.sign z :=
by rcases z with (_ | _)| _; refl

theorem div_sign : ∀ a b, a / sign b = a * sign b
| a (n+1:ℕ) := by unfold sign; simp
| a 0       := by simp [sign]
| a -[1+ n] := by simp [sign]

@[simp] theorem sign_mul : ∀ a b, sign (a * b) = sign a * sign b
| a       0       := by simp
| 0       b       := by simp
| (m+1:ℕ) (n+1:ℕ) := rfl
| (m+1:ℕ) -[1+ n] := rfl
| -[1+ m] (n+1:ℕ) := rfl
| -[1+ m] -[1+ n] := rfl

theorem mul_sign : ∀ (i : ℤ), i * sign i = nat_abs i
| (n+1:ℕ) := mul_one _
| 0       := mul_zero _
| -[1+ n] := mul_neg_one _

theorem of_nat_add_neg_succ_of_nat_of_lt {m n : ℕ} (h : m < n.succ) :
  of_nat m + -[1+n] = -[1+ n - m] :=
begin
  change sub_nat_nat _ _ = _,
  have h' : n.succ - m = (n - m).succ,
  apply succ_sub,
  apply le_of_lt_succ h,
  simp [*, sub_nat_nat]
end

@[simp] theorem neg_add_neg (m n : ℕ) : -[1+m] + -[1+n] = -[1+nat.succ(m+n)] := rfl

/-! ### to_nat -/

theorem to_nat_eq_max : ∀ (a : ℤ), (to_nat a : ℤ) = max a 0
| (n : ℕ) := (max_eq_left (coe_zero_le n)).symm
| -[1+ n] := (max_eq_right (le_of_lt (neg_succ_lt_zero n))).symm

@[simp] lemma to_nat_zero : (0 : ℤ).to_nat = 0 := rfl

@[simp] lemma to_nat_one : (1 : ℤ).to_nat = 1 := rfl

@[simp] theorem to_nat_of_nonneg {a : ℤ} (h : 0 ≤ a) : (to_nat a : ℤ) = a :=
by rw [to_nat_eq_max, max_eq_left h]

@[simp] theorem to_nat_coe_nat (n : ℕ) : to_nat ↑n = n := rfl

@[simp] lemma to_nat_coe_nat_add_one {n : ℕ} : ((n : ℤ) + 1).to_nat = n + 1 := rfl

theorem le_to_nat (a : ℤ) : a ≤ to_nat a :=
by rw [to_nat_eq_max]; apply le_max_left

@[simp]lemma le_to_nat_iff {n : ℕ} {z : ℤ} (h : 0 ≤ z) : n ≤ z.to_nat ↔ (n : ℤ) ≤ z :=
by rw [←int.coe_nat_le_coe_nat_iff, int.to_nat_of_nonneg h]

lemma to_nat_add {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  (a + b).to_nat = a.to_nat + b.to_nat :=
begin
  lift a to ℕ using ha,
  lift b to ℕ using hb,
  norm_cast,
end

lemma to_nat_add_nat {a : ℤ} (ha : 0 ≤ a) (n : ℕ) : (a + n).to_nat = a.to_nat + n :=
begin
  lift a to ℕ using ha,
  norm_cast,
end

@[simp]
lemma pred_to_nat : ∀ (i : ℤ), (i - 1).to_nat = i.to_nat - 1
| (0:ℕ)   := rfl
| (n+1:ℕ) := by simp
| -[1+ n] := rfl

@[simp] lemma to_nat_sub_to_nat_neg : ∀ (n : ℤ), ↑n.to_nat - ↑((-n).to_nat) = n
| (0 : ℕ)   := rfl
| (n+1 : ℕ) := show ↑(n+1) - (0:ℤ) = n+1, from sub_zero _
| -[1+ n]   := show 0 - (n+1 : ℤ)  = _,   from zero_sub _

@[simp] lemma to_nat_add_to_nat_neg_eq_nat_abs : ∀ (n : ℤ), (n.to_nat) + ((-n).to_nat) = n.nat_abs
| (0 : ℕ)   := rfl
| (n+1 : ℕ) := show (n+1) + 0 = n+1, from add_zero _
| -[1+ n]   := show 0 + (n+1) = n+1, from zero_add _

/-- If `n : ℕ`, then `int.to_nat' n = some n`, if `n : ℤ` is negative, then `int.to_nat' n = none`.
-/
def to_nat' : ℤ → option ℕ
| (n : ℕ) := some n
| -[1+ n] := none

theorem mem_to_nat' : ∀ (a : ℤ) (n : ℕ), n ∈ to_nat' a ↔ a = n
| (m : ℕ) n := option.some_inj.trans coe_nat_inj'.symm
| -[1+ m] n := by split; intro h; cases h

@[simp]
lemma to_nat_neg_nat : ∀ (n : ℕ), (-(n : ℤ)).to_nat = 0
| 0       := rfl
| (n + 1) := rfl

end int

attribute [irreducible] int.nonneg
