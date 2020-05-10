/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.cast

universe u
variable {α : Type u}

-- `mul_nonneg` and `mul_pos` in core are stated in terms of `≥` and `>`, so we restate them here
-- for use in syntactic tactics (e.g. `simp` and `rw`).
lemma mul_nonneg' [ordered_semiring α] {a b : α} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
mul_nonneg

lemma mul_pos' [ordered_semiring α] {a b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
mul_pos ha hb

section linear_ordered_semiring
variable [linear_ordered_semiring α]

/-- `0 < 2`: an alternative version of `two_pos` that only assumes `linear_ordered_semiring`. -/
lemma zero_lt_two : (0:α) < 2 :=
by { rw [← zero_add (0:α), bit0], exact add_lt_add zero_lt_one zero_lt_one }

@[simp] lemma mul_le_mul_left {a b c : α} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_left h' h, λ h', mul_le_mul_of_nonneg_left h' (le_of_lt h)⟩

@[simp] lemma mul_le_mul_right {a b c : α} (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_right h' h, λ h', mul_le_mul_of_nonneg_right h' (le_of_lt h)⟩

@[simp] lemma mul_lt_mul_left {a b c : α} (h : 0 < c) : c * a < c * b ↔ a < b :=
⟨lt_imp_lt_of_le_imp_le $ λ h', mul_le_mul_of_nonneg_left h' (le_of_lt h),
 λ h', mul_lt_mul_of_pos_left h' h⟩

@[simp] lemma mul_lt_mul_right {a b c : α} (h : 0 < c) : a * c < b * c ↔ a < b :=
⟨lt_imp_lt_of_le_imp_le $ λ h', mul_le_mul_of_nonneg_right h' (le_of_lt h),
 λ h', mul_lt_mul_of_pos_right h' h⟩

@[simp] lemma zero_le_mul_left {b c : α} (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b :=
by { convert mul_le_mul_left h, simp }

@[simp] lemma zero_le_mul_right {b c : α} (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b :=
by { convert mul_le_mul_right h, simp }

@[simp] lemma zero_lt_mul_left {b c : α} (h : 0 < c) : 0 < c * b ↔ 0 < b :=
by { convert mul_lt_mul_left h, simp }

@[simp] lemma zero_lt_mul_right {b c : α} (h : 0 < c) : 0 < b * c ↔ 0 < b :=
by { convert mul_lt_mul_right h, simp }

@[simp] lemma bit0_le_bit0 {a b : α} : bit0 a ≤ bit0 b ↔ a ≤ b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_le_mul_left zero_lt_two]

@[simp] lemma bit0_lt_bit0 {a b : α} : bit0 a < bit0 b ↔ a < b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_lt_mul_left zero_lt_two]

@[simp] lemma bit1_le_bit1 {a b : α} : bit1 a ≤ bit1 b ↔ a ≤ b :=
(add_le_add_iff_right 1).trans bit0_le_bit0

@[simp] lemma bit1_lt_bit1 {a b : α} : bit1 a < bit1 b ↔ a < b :=
(add_lt_add_iff_right 1).trans bit0_lt_bit0

@[simp] lemma one_le_bit1 {a : α} : (1 : α) ≤ bit1 a ↔ 0 ≤ a :=
by rw [bit1, le_add_iff_nonneg_left, bit0, ← two_mul, zero_le_mul_left zero_lt_two]

@[simp] lemma one_lt_bit1 {a : α} : (1 : α) < bit1 a ↔ 0 < a :=
by rw [bit1, lt_add_iff_pos_left, bit0, ← two_mul, zero_lt_mul_left zero_lt_two]

@[simp] lemma zero_le_bit0 {a : α} : (0 : α) ≤ bit0 a ↔ 0 ≤ a :=
by rw [bit0, ← two_mul, zero_le_mul_left zero_lt_two]

@[simp] lemma zero_lt_bit0 {a : α} : (0 : α) < bit0 a ↔ 0 < a :=
by rw [bit0, ← two_mul, zero_lt_mul_left zero_lt_two]

lemma mul_lt_mul'' {a b c d : α} (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) :
       a * b < c * d :=
(lt_or_eq_of_le h4).elim
  (λ b0, mul_lt_mul h1 (le_of_lt h2) b0 (le_trans h3 (le_of_lt h1)))
  (λ b0, by rw [← b0, mul_zero]; exact
    mul_pos (lt_of_le_of_lt h3 h1) (lt_of_le_of_lt h4 h2))

lemma le_mul_iff_one_le_left {a b : α} (hb : 0 < b) : b ≤ a * b ↔ 1 ≤ a :=
suffices 1 * b ≤ a * b ↔ 1 ≤ a, by rwa one_mul at this,
mul_le_mul_right hb

lemma lt_mul_iff_one_lt_left {a b : α} (hb : 0 < b) : b < a * b ↔ 1 < a :=
suffices 1 * b < a * b ↔ 1 < a, by rwa one_mul at this,
mul_lt_mul_right hb

lemma le_mul_iff_one_le_right {a b : α} (hb : 0 < b) : b ≤ b * a ↔ 1 ≤ a :=
suffices b * 1 ≤ b * a ↔ 1 ≤ a, by rwa mul_one at this,
mul_le_mul_left hb

lemma lt_mul_iff_one_lt_right {a b : α} (hb : 0 < b) : b < b * a ↔ 1 < a :=
suffices b * 1 < b * a ↔ 1 < a, by rwa mul_one at this,
mul_lt_mul_left hb

lemma lt_mul_of_one_lt_right' {a b : α} (hb : 0 < b) : 1 < a → b < b * a :=
(lt_mul_iff_one_lt_right hb).2

lemma le_mul_of_one_le_right' {a b : α} (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ b * a :=
suffices b * 1 ≤ b * a, by rwa mul_one at this,
mul_le_mul_of_nonneg_left h hb

lemma le_mul_of_one_le_left' {a b : α} (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b :=
suffices 1 * b ≤ a * b, by rwa one_mul at this,
mul_le_mul_of_nonneg_right h hb

theorem mul_nonneg_iff_right_nonneg_of_pos {a b : α} (h : 0 < a) : 0 ≤ b * a ↔ 0 ≤ b :=
⟨assume : 0 ≤ b * a, nonneg_of_mul_nonneg_right this h, assume : 0 ≤ b, mul_nonneg this $ le_of_lt h⟩

lemma bit1_pos {a : α} (h : 0 ≤ a) : 0 < bit1 a :=
lt_add_of_le_of_pos (add_nonneg h h) zero_lt_one

lemma bit1_pos' {a : α} (h : 0 < a) : 0 < bit1 a :=
bit1_pos (le_of_lt h)

lemma lt_add_one (a : α) : a < a + 1 :=
lt_add_of_le_of_pos (le_refl _) zero_lt_one

lemma lt_one_add (a : α) : a < 1 + a :=
by { rw [add_comm], apply lt_add_one }

lemma one_lt_two : 1 < (2 : α) := lt_add_one _

lemma one_lt_mul {a b : α} (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
(one_mul (1 : α)) ▸ mul_lt_mul' ha hb zero_le_one (lt_of_lt_of_le zero_lt_one ha)

lemma mul_le_one {a b : α} (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
begin rw ← one_mul (1 : α), apply mul_le_mul; {assumption <|> apply zero_le_one} end

lemma one_lt_mul_of_le_of_lt {a b : α} (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
calc 1 = 1 * 1 : by rw one_mul
... < a * b : mul_lt_mul' ha hb zero_le_one (lt_of_lt_of_le zero_lt_one ha)

lemma one_lt_mul_of_lt_of_le {a b : α} (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
calc 1 = 1 * 1 : by rw one_mul
... < a * b : mul_lt_mul ha hb zero_lt_one (le_trans zero_le_one (le_of_lt ha))

lemma mul_le_of_le_one_right {a b : α} (ha : 0 ≤ a) (hb1 : b ≤ 1) : a * b ≤ a :=
calc a * b ≤ a * 1 : mul_le_mul_of_nonneg_left hb1 ha
... = a : mul_one a

lemma mul_le_of_le_one_left {a b : α} (hb : 0 ≤ b) (ha1 : a ≤ 1) : a * b ≤ b :=
calc a * b ≤ 1 * b : mul_le_mul ha1 (le_refl b) hb zero_le_one
... = b : one_mul b

lemma mul_lt_one_of_nonneg_of_lt_one_left {a b : α}
  (ha0 : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
calc a * b ≤ a : mul_le_of_le_one_right ha0 hb
... < 1 : ha

lemma mul_lt_one_of_nonneg_of_lt_one_right {a b : α}
  (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
calc a * b ≤ b : mul_le_of_le_one_left hb0 ha
... < 1 : hb

lemma mul_le_iff_le_one_left {a b : α} (hb : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
⟨ λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_left hb).2 (not_lt_of_ge h)),
  λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_left hb).1 (not_lt_of_ge h)) ⟩

lemma mul_lt_iff_lt_one_left {a b : α} (hb : 0 < b) : a * b < b ↔ a < 1 :=
⟨ λ h, lt_of_not_ge (mt (le_mul_iff_one_le_left hb).2 (not_le_of_gt h)),
  λ h, lt_of_not_ge (mt (le_mul_iff_one_le_left hb).1 (not_le_of_gt h)) ⟩

lemma mul_le_iff_le_one_right {a b : α} (hb : 0 < b) : b * a ≤ b ↔ a ≤ 1 :=
⟨ λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_right hb).2 (not_lt_of_ge h)),
  λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_right hb).1 (not_lt_of_ge h)) ⟩

lemma mul_lt_iff_lt_one_right {a b : α} (hb : 0 < b) : b * a < b ↔ a < 1 :=
⟨ λ h, lt_of_not_ge (mt (le_mul_iff_one_le_right hb).2 (not_le_of_gt h)),
  λ h, lt_of_not_ge (mt (le_mul_iff_one_le_right hb).1 (not_le_of_gt h)) ⟩

lemma nonpos_of_mul_nonneg_left {a b : α} (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
le_of_not_gt (λ ha, absurd h (not_le_of_gt (mul_neg_of_pos_of_neg ha hb)))

lemma nonpos_of_mul_nonneg_right {a b : α} (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
le_of_not_gt (λ hb, absurd h (not_le_of_gt (mul_neg_of_neg_of_pos ha hb)))

lemma neg_of_mul_pos_left {a b : α} (h : 0 < a * b) (hb : b ≤ 0) : a < 0 :=
lt_of_not_ge (λ ha, absurd h (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha hb)))

lemma neg_of_mul_pos_right {a b : α} (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
lt_of_not_ge (λ hb, absurd h (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha hb)))

section mono

variables {β : Type*} [preorder β] {f g : β → α} {a : α}

lemma monotone_mul_left_of_nonneg (ha : 0 ≤ a) : monotone (λ x, a*x) :=
assume b c b_le_c, mul_le_mul_of_nonneg_left b_le_c ha

lemma monotone_mul_right_of_nonneg (ha : 0 ≤ a) : monotone (λ x, x*a) :=
assume b c b_le_c, mul_le_mul_of_nonneg_right b_le_c ha

lemma monotone.mul_const (hf : monotone f) (ha : 0 ≤ a) :
  monotone (λ x, (f x) * a) :=
(monotone_mul_right_of_nonneg ha).comp hf

lemma monotone.const_mul (hf : monotone f) (ha : 0 ≤ a) :
  monotone (λ x, a * (f x)) :=
(monotone_mul_left_of_nonneg ha).comp hf

lemma monotone.mul (hf : monotone f) (hg : monotone g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
  monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul (hf h) (hg h) (hg0 x) (hf0 y)

lemma strict_mono_mul_left_of_pos (ha : 0 < a) : strict_mono (λ x, a * x) :=
assume b c b_lt_c, (mul_lt_mul_left ha).2 b_lt_c

lemma strict_mono_mul_right_of_pos (ha : 0 < a) : strict_mono (λ x, x * a) :=
assume b c b_lt_c, (mul_lt_mul_right ha).2 b_lt_c

lemma strict_mono.mul_const (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, (f x) * a) :=
(strict_mono_mul_right_of_pos ha).comp hf

lemma strict_mono.const_mul (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, a * (f x)) :=
(strict_mono_mul_left_of_pos ha).comp hf

lemma strict_mono.mul_monotone (hf : strict_mono f) (hg : monotone g) (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 < g x) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul (hf h) (hg $ le_of_lt h) (hg0 x) (hf0 y)

lemma monotone.mul_strict_mono (hf : monotone f) (hg : strict_mono g) (hf0 : ∀ x, 0 < f x)
  (hg0 : ∀ x, 0 ≤ g x) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul' (hf $ le_of_lt h) (hg h) (hg0 x) (hf0 y)

lemma strict_mono.mul (hf : strict_mono f) (hg : strict_mono g) (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul'' (hf h) (hg h) (hf0 x) (hg0 x)

end mono

end linear_ordered_semiring

section decidable_linear_ordered_semiring
variable [decidable_linear_ordered_semiring α]

@[simp] lemma decidable.mul_le_mul_left {a b c : α} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
decidable.le_iff_le_iff_lt_iff_lt.2 $ mul_lt_mul_left h

@[simp] lemma decidable.mul_le_mul_right {a b c : α} (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
decidable.le_iff_le_iff_lt_iff_lt.2 $ mul_lt_mul_right h

end decidable_linear_ordered_semiring

-- The proof doesn't need commutativity but we have no `decidable_linear_ordered_ring`
@[simp] lemma abs_two [decidable_linear_ordered_comm_ring α] : abs (2:α) = 2 :=
abs_of_pos $ by refine zero_lt_two

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_no_top_order {α : Type*} [linear_ordered_semiring α] :
  no_top_order α :=
⟨assume a, ⟨a + 1, lt_add_of_pos_right _ zero_lt_one⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_no_bot_order {α : Type*} [linear_ordered_ring α] :
  no_bot_order α :=
⟨assume a, ⟨a - 1, sub_lt_iff_lt_add.mpr $ lt_add_of_pos_right _ zero_lt_one⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_domain [s : linear_ordered_ring α] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := @linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero α s,
  ..s }

section linear_ordered_ring
variable [linear_ordered_ring α]

@[simp] lemma mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_left h' h,
  λ h', mul_le_mul_of_nonpos_left h' (le_of_lt h)⟩

@[simp] lemma mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_right h' h,
  λ h', mul_le_mul_of_nonpos_right h' (le_of_lt h)⟩

@[simp] lemma mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
lt_iff_lt_of_le_iff_le (mul_le_mul_left_of_neg h)

@[simp] lemma mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
lt_iff_lt_of_le_iff_le (mul_le_mul_right_of_neg h)

lemma sub_one_lt (a : α) : a - 1 < a :=
sub_lt_iff_lt_add.2 (lt_add_one a)

lemma mul_self_pos {a : α} (ha : a ≠ 0) : 0 < a * a :=
by rcases lt_trichotomy a 0 with h|h|h;
   [exact mul_pos_of_neg_of_neg h h, exact (ha h).elim, exact mul_pos h h]

lemma mul_self_le_mul_self_of_le_of_neg_le {x y : α} (h₁ : x ≤ y) (h₂ : -x ≤ y) : x * x ≤ y * y :=
begin
  cases le_total 0 x,
  { exact mul_self_le_mul_self h h₁ },
  { rw ← neg_mul_neg, exact mul_self_le_mul_self (neg_nonneg_of_nonpos h) h₂ }
end

lemma nonneg_of_mul_nonpos_left {a b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
le_of_not_gt (λ ha, absurd h (not_le_of_gt (mul_pos_of_neg_of_neg ha hb)))

lemma nonneg_of_mul_nonpos_right {a b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
le_of_not_gt (λ hb, absurd h (not_le_of_gt (mul_pos_of_neg_of_neg ha hb)))

lemma pos_of_mul_neg_left {a b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
lt_of_not_ge (λ ha, absurd h (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos ha hb)))

lemma pos_of_mul_neg_right {a b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
lt_of_not_ge (λ hb, absurd h (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos ha hb)))

/- The sum of two squares is zero iff both elements are zero. -/
lemma mul_self_add_mul_self_eq_zero {x y : α} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split; intro h, swap, { rcases h with ⟨rfl, rfl⟩, simp },
  have : y * y ≤ 0, { rw [← h], apply le_add_of_nonneg_left (mul_self_nonneg x) },
  have : y * y = 0 := le_antisymm this (mul_self_nonneg y),
  have hx : x = 0, { rwa [this, add_zero, mul_self_eq_zero] at h },
  rw mul_self_eq_zero at this, split; assumption
end

end linear_ordered_ring

set_option old_structure_cmd true
section prio
set_option default_priority 100 -- see Note [default priority]
/-- Extend `nonneg_add_comm_group` to support ordered rings
  specified by their nonnegative elements -/
class nonneg_ring (α : Type*)
  extends ring α, zero_ne_one_class α, nonneg_add_comm_group α :=
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(mul_pos : ∀ {a b}, pos a → pos b → pos (a * b))

/-- Extend `nonneg_add_comm_group` to support linearly ordered rings
  specified by their nonnegative elements -/
class linear_nonneg_ring (α : Type*) extends domain α, nonneg_add_comm_group α :=
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(nonneg_total : ∀ a, nonneg a ∨ nonneg (-a))
end prio

namespace nonneg_ring
open nonneg_add_comm_group
variable [s : nonneg_ring α]

@[priority 100] -- see Note [lower instance priority]
instance to_ordered_ring : ordered_ring α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  add_le_add_left := @add_le_add_left _ _,
  mul_pos := λ a b, by simp [pos_def.symm]; exact mul_pos,
  ..s }

def to_linear_nonneg_ring
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : linear_nonneg_ring α :=
{ nonneg_total := nonneg_total,
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    suffices ∀ {a} b : α, nonneg a → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b, (nonneg_total a).elim (this b)
      (λ na, by simpa using this b na),
    suffices ∀ {a b : α}, nonneg a → nonneg b → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b na, (nonneg_total b).elim (this na)
      (λ nb, by simpa using this na nb),
    λ a b na nb z, classical.by_cases
      (λ nna : nonneg (-a), or.inl (nonneg_antisymm na nna))
      (λ pa, classical.by_cases
        (λ nnb : nonneg (-b), or.inr (nonneg_antisymm nb nnb))
        (λ pb, absurd z $ ne_of_gt $ pos_def.1 $ mul_pos
          ((pos_iff _).2 ⟨na, pa⟩)
          ((pos_iff _).2 ⟨nb, pb⟩))),
  ..s }

end nonneg_ring

namespace linear_nonneg_ring
open nonneg_add_comm_group
variable [s : linear_nonneg_ring α]

@[priority 100] -- see Note [lower instance priority]
instance to_nonneg_ring : nonneg_ring α :=
{ mul_pos := λ a b pa pb,
  let ⟨a1, a2⟩ := (pos_iff a).1 pa,
      ⟨b1, b2⟩ := (pos_iff b).1 pb in
  have ab : nonneg (a * b), from mul_nonneg a1 b1,
  (pos_iff _).2 ⟨ab, λ hn,
    have a * b = 0, from nonneg_antisymm ab hn,
    (eq_zero_or_eq_zero_of_mul_eq_zero _ _ this).elim
      (ne_of_gt (pos_def.1 pa))
      (ne_of_gt (pos_def.1 pb))⟩,
  ..s }

@[priority 100] -- see Note [lower instance priority]
instance to_linear_order : linear_order α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := nonneg_total_iff.1 nonneg_total,
  ..s }

@[priority 100] -- see Note [lower instance priority]
instance to_linear_ordered_ring : linear_ordered_ring α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := @le_total _ _,
  add_le_add_left := @add_le_add_left _ _,
  mul_pos := by simp [pos_def.symm]; exact @nonneg_ring.mul_pos _ _,
  zero_lt_one := lt_of_not_ge $ λ (h : nonneg (0 - 1)), begin
    rw [zero_sub] at h,
    have := mul_nonneg h h, simp at this,
    exact zero_ne_one (nonneg_antisymm this h).symm
  end, ..s }

/-- Convert a `linear_nonneg_ring` with a commutative multiplication and
decidable non-negativity into a `decidable_linear_ordered_comm_ring` -/
def to_decidable_linear_ordered_comm_ring
  [decidable_pred (@nonneg α _)]
  [comm : @is_commutative α (*)]
  : decidable_linear_ordered_comm_ring α :=
{ decidable_le := by apply_instance,
  decidable_lt := by apply_instance,
  mul_comm := is_commutative.comm,
  ..@linear_nonneg_ring.to_linear_ordered_ring _ s }

end linear_nonneg_ring

section prio
set_option default_priority 100 -- see Note [default priority]
class canonically_ordered_comm_semiring (α : Type*) extends
  canonically_ordered_add_monoid α, comm_semiring α, zero_ne_one_class α :=
(mul_eq_zero_iff (a b : α) : a * b = 0 ↔ a = 0 ∨ b = 0)
end prio

namespace canonically_ordered_semiring
open canonically_ordered_add_monoid

variable [canonically_ordered_comm_semiring α]

lemma mul_le_mul {a b c d : α} (hab : a ≤ b) (hcd : c ≤ d) :
  a * c ≤ b * d :=
begin
  rcases (le_iff_exists_add _ _).1 hab with ⟨b, rfl⟩,
  rcases (le_iff_exists_add _ _).1 hcd with ⟨d, rfl⟩,
  suffices : a * c ≤ a * c + (a * d + b * c + b * d), by simpa [mul_add, add_mul],
  exact (le_iff_exists_add _ _).2 ⟨_, rfl⟩
end

/-- A version of `zero_lt_one : 0 < 1` for a `canonically_ordered_comm_semiring`. -/
lemma zero_lt_one : (0:α) < 1 := lt_of_le_of_ne (zero_le 1) zero_ne_one

lemma mul_pos {a b : α} : 0 < a * b ↔ (0 < a) ∧ (0 < b) :=
by simp only [zero_lt_iff_ne_zero, ne.def, canonically_ordered_comm_semiring.mul_eq_zero_iff,
  not_or_distrib]

end canonically_ordered_semiring

instance : canonically_ordered_comm_semiring ℕ :=
{ le_iff_exists_add := assume a b,
  ⟨assume h, let ⟨c, hc⟩ := nat.le.dest h in ⟨c, hc.symm⟩,
    assume ⟨c, hc⟩, hc.symm ▸ nat.le_add_right _ _⟩,
  zero_ne_one       := ne_of_lt zero_lt_one,
  mul_eq_zero_iff   := assume a b,
    iff.intro nat.eq_zero_of_mul_eq_zero (by simp [or_imp_distrib] {contextual := tt}),
  bot               := 0,
  bot_le            := nat.zero_le,
  .. (infer_instance : ordered_add_comm_monoid ℕ),
  .. (infer_instance : linear_ordered_semiring ℕ),
  .. (infer_instance : comm_semiring ℕ) }

namespace with_top
variables [canonically_ordered_comm_semiring α] [decidable_eq α]

instance : mul_zero_class (with_top α) :=
{ zero := 0,
  mul := λm n, if m = 0 ∨ n = 0 then 0 else m.bind (λa, n.bind $ λb, ↑(a * b)),
  zero_mul := assume a, if_pos $ or.inl rfl,
  mul_zero := assume a, if_pos $ or.inr rfl }

instance : has_one (with_top α) := ⟨↑(1:α)⟩

lemma mul_def {a b : with_top α} :
  a * b = if a = 0 ∨ b = 0 then 0 else a.bind (λa, b.bind $ λb, ↑(a * b)) := rfl

@[simp] theorem top_ne_zero [partial_order α] : ⊤ ≠ (0 : with_top α) .
@[simp] theorem zero_ne_top [partial_order α] : (0 : with_top α) ≠ ⊤ .

@[simp] theorem coe_eq_zero [partial_order α] {a : α} : (a : with_top α) = 0 ↔ a = 0 :=
iff.intro
  (assume h, match a, h with _, rfl := rfl end)
  (assume h, h.symm ▸ rfl)

@[simp] theorem zero_eq_coe [partial_order α] {a : α} : 0 = (a : with_top α) ↔ a = 0 :=
by rw [eq_comm, coe_eq_zero]

@[simp] theorem coe_zero [partial_order α] : ↑(0 : α) = (0 : with_top α) := rfl

@[simp] lemma mul_top {a : with_top α} (h : a ≠ 0) : a * ⊤ = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul {a : with_top α} (h : a ≠ 0) : ⊤ * a = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul_top : (⊤ * ⊤ : with_top α) = ⊤ :=
top_mul top_ne_zero

lemma coe_mul {a b : α} : (↑(a * b) : with_top α) = a * b :=
decidable.by_cases (assume : a = 0, by simp [this]) $ assume ha,
decidable.by_cases (assume : b = 0, by simp [this]) $ assume hb,
by simp [*, mul_def]; refl

lemma mul_coe {b : α} (hb : b ≠ 0) : ∀{a : with_top α}, a * b = a.bind (λa:α, ↑(a * b))
| none     := show (if (⊤:with_top α) = 0 ∨ (b:with_top α) = 0 then 0 else ⊤ : with_top α) = ⊤,
    by simp [hb]
| (some a) := show ↑a * ↑b = ↑(a * b), from coe_mul.symm

private lemma comm (a b : with_top α) : a * b = b * a :=
begin
  by_cases ha : a = 0, { simp [ha] },
  by_cases hb : b = 0, { simp [hb] },
  simp [ha, hb, mul_def, option.bind_comm a b, mul_comm]
end

@[simp] lemma mul_eq_top_iff {a b : with_top α} : a * b = ⊤ ↔ (a ≠ 0 ∧ b = ⊤) ∨ (a = ⊤ ∧ b ≠ 0) :=
begin
  have H : ∀x:α, (¬x = 0) ↔ (⊤ : with_top α) * ↑x = ⊤ :=
    λx, ⟨λhx, by simp [top_mul, hx], λhx f, by simpa [f] using hx⟩,
  cases a; cases b; simp [none_eq_top, top_mul, coe_ne_top, some_eq_coe, coe_mul.symm],
  { rw [H b] },
  { rw [H a, comm] }
end

private lemma distrib' (a b c : with_top α) : (a + b) * c = a * c + b * c :=
begin
  cases c,
  { show (a + b) * ⊤ = a * ⊤ + b * ⊤,
    by_cases ha : a = 0; simp [ha] },
  { show (a + b) * c = a * c + b * c,
    by_cases hc : c = 0, { simp [hc] },
    simp [mul_coe hc], cases a; cases b,
    repeat { refl <|> exact congr_arg some (add_mul _ _ _) } }
end

private lemma mul_eq_zero (a b : with_top α) : a * b = 0 ↔ a = 0 ∨ b = 0 :=
by cases a; cases b; dsimp [mul_def]; split_ifs;
  simp [*, none_eq_top, some_eq_coe, canonically_ordered_comm_semiring.mul_eq_zero_iff] at *

private lemma assoc (a b c : with_top α) : (a * b) * c = a * (b * c) :=
begin
  cases a,
  { by_cases hb : b = 0; by_cases hc : c = 0;
      simp [*, none_eq_top, mul_eq_zero b c] },
  cases b,
  { by_cases ha : a = 0; by_cases hc : c = 0;
      simp [*, none_eq_top, some_eq_coe, mul_eq_zero ↑a c] },
  cases c,
  { by_cases ha : a = 0; by_cases hb : b = 0;
      simp [*, none_eq_top, some_eq_coe, mul_eq_zero ↑a ↑b] },
  simp [some_eq_coe, coe_mul.symm, mul_assoc]
end

private lemma one_mul' : ∀a : with_top α, 1 * a = a
| none     := show ((1:α) : with_top α) * ⊤ = ⊤, by simp [-with_bot.coe_one]
| (some a) := show ((1:α) : with_top α) * a = a, by simp [coe_mul.symm, -with_bot.coe_one]

instance [canonically_ordered_comm_semiring α] [decidable_eq α] :
  canonically_ordered_comm_semiring (with_top α) :=
{ one             := (1 : α),
  right_distrib   := distrib',
  left_distrib    := assume a b c, by rw [comm, distrib', comm b, comm c]; refl,
  mul_assoc       := assoc,
  mul_comm        := comm,
  mul_eq_zero_iff := mul_eq_zero,
  one_mul         := one_mul',
  mul_one         := assume a, by rw [comm, one_mul'],
  zero_ne_one     := assume h, @zero_ne_one α _ $ option.some.inj h,
  .. with_top.add_comm_monoid, .. with_top.mul_zero_class, .. with_top.canonically_ordered_add_monoid }

@[simp] lemma coe_nat : ∀(n : nat), ((n : α) : with_top α) = n
| 0     := rfl
| (n+1) := have (((1 : nat) : α) : with_top α) = ((1 : nat) : with_top α) := rfl,
           by rw [nat.cast_add, coe_add, nat.cast_add, coe_nat n, this]

@[simp] lemma nat_ne_top (n : nat) : (n : with_top α ) ≠ ⊤ :=
by rw [←coe_nat n]; apply coe_ne_top

@[simp] lemma top_ne_nat (n : nat) : (⊤ : with_top α) ≠ n :=
by rw [←coe_nat n]; apply top_ne_coe

lemma add_one_le_of_lt {i n : with_top ℕ} (h : i < n) : i + 1 ≤ n :=
begin
  cases n, { exact le_top },
  cases i, { exact (not_le_of_lt h le_top).elim },
  exact with_top.coe_le_coe.2 (with_top.coe_lt_coe.1 h)
end

@[elab_as_eliminator]
lemma nat_induction {P : with_top ℕ → Prop} (a : with_top ℕ)
  (h0 : P 0) (hsuc : ∀n:ℕ, P n → P n.succ) (htop : (∀n : ℕ, P n) → P ⊤) : P a :=
begin
  have A : ∀n:ℕ, P n,
  { assume n,
    induction n with n IH,
    { exact h0 },
    { exact hsuc n IH } },
  cases a,
  { exact htop A },
  { exact A a }
end

end with_top
