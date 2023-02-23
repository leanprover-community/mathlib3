/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import algebra.order.ring.defs

/-!
# Lemmas for `linarith`

This file contains auxiliary lemmas that `linarith` uses to construct proofs.
If you find yourself looking for a theorem here, you might be in the wrong place.
-/

namespace linarith

lemma zero_lt_one {α} [ordered_semiring α] [nontrivial α] : (0 : α) < 1 := zero_lt_one

lemma eq_of_eq_of_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 :=
by simp *

lemma le_of_eq_of_le {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_eq_of_lt {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 :=
by simp *

lemma le_of_le_of_eq {α} [ordered_semiring α] {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_lt_of_eq {α} [ordered_semiring α] {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 :=
by simp *

lemma mul_neg {α} [strict_ordered_ring α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * a < 0 :=
have (-b)*a > 0, from mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha,
neg_of_neg_pos (by simpa)

lemma mul_nonpos {α} [ordered_ring α] {a b : α} (ha : a ≤ 0) (hb : 0 < b) : b * a ≤ 0 :=
have (-b)*a ≥ 0, from mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha,
by simpa

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity
@[nolint unused_arguments]
lemma mul_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : 0 < b) : b * a = 0 :=
by simp *

lemma eq_of_not_lt_of_not_gt {α} [linear_order α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
lemma mul_zero_eq {α} {R : α → α → Prop} [semiring α] {a b : α} (_ : R a 0) (h : b = 0) :
  a * b = 0 :=
by simp [h]

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
lemma zero_mul_eq {α} {R : α → α → Prop} [semiring α] {a b : α} (h : a = 0) (_ : R b 0) :
  a * b = 0 :=
by simp [h]

end linarith
