/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.ordered_ring

/-!
# strictly monotone functions, max, min and abs

This file proves basic properties about strictly monotone functions,
maxima and minima on a `decidable_linear_order`, and the absolute value
function on linearly ordered add_comm_groups, semirings and rings.

## Tags

min, max, abs
-/

universes u v
variables {α : Type u} {β : Type v}

attribute [simp] max_eq_left max_eq_right min_eq_left min_eq_right

section
variables [decidable_linear_order α] [decidable_linear_order β] {f : α → β} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[simp] lemma le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b := le_inf_iff
@[simp] lemma max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := sup_le_iff
lemma max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d := sup_le_sup
lemma min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d := inf_le_inf
lemma le_max_left_of_le : a ≤ b → a ≤ max b c := le_sup_left_of_le
lemma le_max_right_of_le : a ≤ c → a ≤ max b c := le_sup_right_of_le
lemma min_le_left_of_le : a ≤ c → min a b ≤ c := inf_le_left_of_le
lemma min_le_right_of_le : b ≤ c → min a b ≤ c := inf_le_right_of_le
lemma max_min_distrib_left : max a (min b c) = min (max a b) (max a c) := sup_inf_left
lemma max_min_distrib_right : max (min a b) c = min (max a c) (max b c) := sup_inf_right
lemma min_max_distrib_left : min a (max b c) = max (min a b) (min a c) := inf_sup_left
lemma min_max_distrib_right : min (max a b) c = max (min a c) (min b c) := inf_sup_right
lemma min_le_max : min a b ≤ max a b := le_trans (min_le_left a b) (le_max_left a b)

/-- An instance asserting that `max a a = a` -/
instance max_idem : is_idempotent α max := by apply_instance -- short-circuit type class inference

/-- An instance asserting that `min a a = a` -/
instance min_idem : is_idempotent α min := by apply_instance -- short-circuit type class inference

@[simp] lemma min_le_iff : min a b ≤ c ↔ a ≤ c ∨ b ≤ c :=
have a ≤ b → (a ≤ c ∨ b ≤ c ↔ a ≤ c),
  from assume h, or_iff_left_of_imp $ le_trans h,
have b ≤ a → (a ≤ c ∨ b ≤ c ↔ b ≤ c),
  from assume h, or_iff_right_of_imp $ le_trans h,
by cases le_total a b; simp *

@[simp] lemma le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
have b ≤ c → (a ≤ b ∨ a ≤ c ↔ a ≤ c),
  from assume h, or_iff_right_of_imp $ assume h', le_trans h' h,
have c ≤ b → (a ≤ b ∨ a ≤ c ↔ a ≤ b),
  from assume h, or_iff_left_of_imp $ assume h', le_trans h' h,
by cases le_total b c; simp *

@[simp] lemma max_lt_iff : max a b < c ↔ (a < c ∧ b < c) :=
by rw [lt_iff_not_ge]; simp [(≥), le_max_iff, not_or_distrib]

@[simp] lemma lt_min_iff : a < min b c ↔ (a < b ∧ a < c) :=
by rw [lt_iff_not_ge]; simp [(≥), min_le_iff, not_or_distrib]

@[simp] lemma lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
by rw [lt_iff_not_ge]; simp [(≥), max_le_iff, not_and_distrib]

@[simp] lemma min_lt_iff : min a b < c ↔ a < c ∨ b < c :=
by rw [lt_iff_not_ge]; simp [(≥), le_min_iff, not_and_distrib]

lemma max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
by apply max_lt; simp [lt_max_iff, h₁, h₂]

lemma min_lt_min (h₁ : a < c) (h₂ : b < d) : min a b < min c d :=
by apply lt_min; simp [min_lt_iff, h₁, h₂]

theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
right_comm min min_comm min_assoc a b c

theorem max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
left_comm max max_comm max_assoc a b c

theorem max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
right_comm max max_comm max_assoc a b c

lemma monotone.map_max (hf : monotone f) : f (max a b) = max (f a) (f b) :=
by cases le_total a b; simp [h, hf h]

lemma monotone.map_min (hf : monotone f) : f (min a b) = min (f a) (f b) :=
by cases le_total a b; simp [h, hf h]

theorem min_choice (a b : α) : min a b = a ∨ min a b = b :=
by by_cases h : a ≤ b; simp [min, h]

theorem max_choice (a b : α) : max a b = a ∨ max a b = b :=
by by_cases h : a ≤ b; simp [max, h]

lemma le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
le_trans (le_max_left _ _) h

lemma le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
le_trans (le_max_right _ _) h

end

lemma min_add {α : Type u} [decidable_linear_ordered_add_comm_group α] (a b c : α) :
      min a b + c = min (a + c) (b + c) :=
if hle : a ≤ b then
  have a - c ≤ b - c, from sub_le_sub hle (le_refl _),
  by simp * at *
else
  have b - c ≤ a - c, from sub_le_sub (le_of_lt (lt_of_not_ge hle)) (le_refl _),
  by simp * at *

lemma min_sub {α : Type u} [decidable_linear_ordered_add_comm_group α] (a b c : α) :
      min a b - c = min (a - c) (b - c) :=
by simp [min_add, sub_eq_add_neg]


/- Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/
lemma fn_min_add_fn_max [decidable_linear_order α] [add_comm_semigroup β] (f : α → β) (n m : α) :
  f (min n m) + f (max n m) = f n + f m :=
by { cases le_total n m with h h; simp [h, add_comm] }

lemma min_add_max [decidable_linear_order α] [add_comm_semigroup α] (n m : α) :
  min n m + max n m = n + m :=
fn_min_add_fn_max id n m

lemma fn_min_mul_fn_max [decidable_linear_order α] [comm_semigroup β] (f : α → β) (n m : α) :
  f (min n m) * f (max n m) = f n * f m :=
by { cases le_total n m with h h; simp [h, mul_comm] }

lemma min_mul_max [decidable_linear_order α] [comm_semigroup α] (n m : α) :
  min n m * max n m = n * m :=
fn_min_mul_fn_max id n m

section decidable_linear_ordered_add_comm_group
variables [decidable_linear_ordered_add_comm_group α] {a b c : α}

attribute [simp] abs_zero abs_neg

lemma abs_add (a b : α) : abs (a + b) ≤ abs a + abs b := abs_add_le_abs_add_abs a b

theorem abs_le : abs a ≤ b ↔ - b ≤ a ∧ a ≤ b :=
⟨assume h, ⟨neg_le_of_neg_le $ le_trans (neg_le_abs_self _) h, le_trans (le_abs_self _) h⟩,
  assume ⟨h₁, h₂⟩, abs_le_of_le_of_neg_le h₂ $ neg_le_of_neg_le h₁⟩

lemma abs_lt : abs a < b ↔ - b < a ∧ a < b :=
⟨assume h, ⟨neg_lt_of_neg_lt $ lt_of_le_of_lt (neg_le_abs_self _) h, lt_of_le_of_lt (le_abs_self _) h⟩,
  assume ⟨h₁, h₂⟩, abs_lt_of_lt_of_neg_lt h₂ $ neg_lt_of_neg_lt h₁⟩

lemma lt_abs : a < abs b ↔ a < b ∨ a < -b := lt_max_iff

lemma abs_sub_le_iff : abs (a - b) ≤ c ↔ a - b ≤ c ∧ b - a ≤ c :=
by rw [abs_le, neg_le_sub_iff_le_add, @sub_le_iff_le_add' _ _ b, and_comm]

lemma abs_sub_lt_iff : abs (a - b) < c ↔ a - b < c ∧ b - a < c :=
by rw [abs_lt, neg_lt_sub_iff_lt_add, @sub_lt_iff_lt_add' _ _ b, and_comm]

lemma sub_abs_le_abs_sub (a b : α) : abs a - abs b ≤ abs (a - b) := abs_sub_abs_le_abs_sub a b

lemma abs_abs_sub_le_abs_sub (a b : α) : abs (abs a - abs b) ≤ abs (a - b) :=
abs_sub_le_iff.2 ⟨sub_abs_le_abs_sub _ _, by rw abs_sub; apply sub_abs_le_abs_sub⟩

lemma abs_eq (hb : 0 ≤ b) : abs a = b ↔ a = b ∨ a = -b :=
iff.intro
  begin
    cases le_total a 0 with a_nonpos a_nonneg,
    { rw [abs_of_nonpos a_nonpos, neg_eq_iff_neg_eq, eq_comm], exact or.inr },
    { rw [abs_of_nonneg a_nonneg, eq_comm], exact or.inl }
  end
  (by intro h; cases h; subst h; try { rw abs_neg }; exact abs_of_nonneg hb)

@[simp] lemma abs_eq_zero : abs a = 0 ↔ a = 0 :=
⟨eq_zero_of_abs_eq_zero, λ e, e.symm ▸ abs_zero⟩

lemma abs_pos_iff {a : α} : 0 < abs a ↔ a ≠ 0 :=
⟨λ h, mt abs_eq_zero.2 (ne_of_gt h), abs_pos_of_ne_zero⟩

@[simp] lemma abs_nonpos_iff {a : α} : abs a ≤ 0 ↔ a = 0 :=
by rw [← not_lt, abs_pos_iff, not_not]

lemma abs_le_max_abs_abs (hab : a ≤ b)  (hbc : b ≤ c) : abs b ≤ max (abs a) (abs c) :=
abs_le_of_le_of_neg_le
  (by simp [le_max_iff, le_trans hbc (le_abs_self c)])
  (by simp [le_max_iff, le_trans (neg_le_neg hab) (neg_le_abs_self a)])

theorem abs_le_abs {α : Type*} [decidable_linear_ordered_add_comm_group α] {a b : α}
  (h₀ : a ≤ b) (h₁ : -a ≤ b) :
  abs a ≤ abs b :=
calc  abs a
    ≤ b : by { apply abs_le_of_le_of_neg_le; assumption }
... ≤ abs b : le_abs_self _

lemma min_le_add_of_nonneg_right {a b : α} (hb : b ≥ 0) : min a b ≤ a + b :=
calc
  min a b ≤ a     : by apply min_le_left
      ... ≤ a + b : le_add_of_nonneg_right hb

lemma min_le_add_of_nonneg_left {a b : α} (ha : a ≥ 0) : min a b ≤ a + b :=
calc
  min a b ≤ b     : by apply min_le_right
      ... ≤ a + b : le_add_of_nonneg_left ha

lemma max_le_add_of_nonneg {a b : α} (ha : a ≥ 0) (hb : b ≥ 0) : max a b ≤ a + b :=
max_le_iff.2 (by split; simpa)

lemma max_zero_sub_eq_self (a : α) : max a 0 - max (-a) 0 = a :=
begin
  rcases le_total a 0,
  { rw [max_eq_right h, max_eq_left, zero_sub, neg_neg], { rwa [le_neg, neg_zero] } },
  { rw [max_eq_left, max_eq_right, sub_zero], { rwa [neg_le, neg_zero] }, exact h }
end

lemma abs_max_sub_max_le_abs (a b c : α) : abs (max a c - max b c) ≤ abs (a - b) :=
begin
  simp only [max],
  split_ifs,
  { rw [sub_self, abs_zero], exact abs_nonneg _ },
  { calc abs (c - b) = - (c - b) : abs_of_neg (sub_neg_of_lt (lt_of_not_ge h_1))
      ... = b - c : neg_sub _ _
      ... ≤ b - a : by { rw sub_le_sub_iff_left, exact h }
      ... = - (a - b) : by rw neg_sub
      ... ≤ abs (a - b) : neg_le_abs_self _ },
  { calc abs (a - c) = a - c : abs_of_pos (sub_pos_of_lt (lt_of_not_ge h))
      ... ≤ a - b : by { rw sub_le_sub_iff_left, exact h_1 }
      ... ≤ abs (a - b) : le_abs_self _ },
  { refl }
end

lemma max_sub_min_eq_abs' (a b : α) : max a b - min a b = abs (a - b) :=
begin
  cases le_total a b with ab ba,
  { rw [max_eq_right ab, min_eq_left ab, abs_of_nonpos, neg_sub], rwa sub_nonpos },
  { rw [max_eq_left ba, min_eq_right ba, abs_of_nonneg], exact sub_nonneg_of_le ba }
end

lemma max_sub_min_eq_abs (a b : α) : max a b - min a b = abs (b - a) :=
by { rw [abs_sub], exact max_sub_min_eq_abs' _ _ }

end decidable_linear_ordered_add_comm_group

section decidable_linear_ordered_semiring
variables [decidable_linear_ordered_semiring α] {a b c d : α}

lemma mul_max_of_nonneg (b c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_max

lemma mul_min_of_nonneg (b c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_min

lemma max_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_max

lemma min_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_min

end decidable_linear_ordered_semiring

section decidable_linear_ordered_comm_ring
variables [decidable_linear_ordered_comm_ring α] {a b c d : α}

@[simp] lemma abs_one : abs (1 : α) = 1 := abs_of_pos zero_lt_one

lemma max_mul_mul_le_max_mul_max (b c : α) (ha : 0 ≤ a) (hd: 0 ≤ d) :
  max (a * b) (d * c) ≤ max a c * max d b :=
have ba : b * a ≤ max d b * max c a,
  from mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b)),
have cd : c * d ≤ max a c * max b d,
  from mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c)),
max_le
  (by simpa [mul_comm, max_comm] using ba)
  (by simpa [mul_comm, max_comm] using cd)

end decidable_linear_ordered_comm_ring
