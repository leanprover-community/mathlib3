/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao
-/
import algebra.covariant_and_contravariant
import order.min_max

/-!
# Ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

Almost no monoid is actually present in this file: most assumptions have been generalized to
`has_mul` or `mul_one_class`.

-/

-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.

open function

variables {α β : Type*}

section has_mul
variables [has_mul α]

section has_le
variables [has_le α]

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_left]
lemma mul_le_mul_left' [covariant_class α α (*) (≤)]
  {b c : α} (bc : b ≤ c) (a : α) :
  a * b ≤ a * c :=
covariant_class.elim _ bc

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' [contravariant_class α α (*) (≤)]
  {a b c : α} (bc : a * b ≤ a * c) :
  b ≤ c :=
contravariant_class.elim _ bc

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_right]
lemma mul_le_mul_right' [covariant_class α α (swap (*)) (≤)]
  {b c : α} (bc : b ≤ c) (a : α) :
  b * a ≤ c * a :=
covariant_class.elim a bc

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' [contravariant_class α α (swap (*)) (≤)]
  {a b c : α} (bc : b * a ≤ c * a) :
  b ≤ c :=
contravariant_class.elim a bc

@[simp, to_additive]
lemma mul_le_mul_iff_left [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b c : α} :
  a * b ≤ a * c ↔ b ≤ c :=
rel_iff_cov α α (*) (≤) a

@[simp, to_additive]
lemma mul_le_mul_iff_right
  [covariant_class α α (swap (*)) (≤)] [contravariant_class α α (swap (*)) (≤)]
  (a : α) {b c : α} :
  b * a ≤ c * a ↔ b ≤ c :=
rel_iff_cov α α (swap (*)) (≤) a

end has_le

section has_lt
variables [has_lt α]

@[simp, to_additive]
lemma mul_lt_mul_iff_left [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)]
  (a : α) {b c : α} :
  a * b < a * c ↔ b < c :=
rel_iff_cov α α (*) (<) a

@[simp, to_additive]
lemma mul_lt_mul_iff_right
  [covariant_class α α (swap (*)) (<)] [contravariant_class α α (swap (*)) (<)]
  (a : α) {b c : α} :
  b * a < c * a ↔ b < c :=
rel_iff_cov α α (swap (*)) (<) a

@[to_additive add_lt_add_left]
lemma mul_lt_mul_left' [covariant_class α α (*) (<)]
  {b c : α} (bc : b < c) (a : α) :
  a * b < a * c :=
covariant_class.elim _ bc

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' [contravariant_class α α (*) (<)]
  {a b c : α} (bc : a * b < a * c) :
  b < c :=
contravariant_class.elim _ bc

@[to_additive add_lt_add_right]
lemma mul_lt_mul_right' [covariant_class α α (swap (*)) (<)]
  {b c : α} (bc : b < c) (a : α) :
  b * a < c * a :=
covariant_class.elim a bc

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' [contravariant_class α α (swap (*)) (<)]
  {a b c : α} (bc : b * a < c * a) :
  b < c :=
contravariant_class.elim a bc

end has_lt

section preorder
variables [preorder α]

@[to_additive]
lemma mul_lt_mul_of_lt_of_lt [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
calc  a * c < a * d : mul_lt_mul_left' h₂ a
        ... < b * d : mul_lt_mul_right' h₁ d

alias add_lt_add_of_lt_of_lt ← add_lt_add

@[to_additive]
lemma mul_lt_mul_of_le_of_lt [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]
  {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_mul_of_lt_of_le [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (<)]
  {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)

/-- Only assumes left strict covariance. -/
@[to_additive "Only assumes left strict covariance"]
lemma left.mul_lt_mul [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]
  {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
mul_lt_mul_of_le_of_lt h₁.le h₂

/-- Only assumes right strict covariance. -/
@[to_additive "Only assumes right strict covariance"]
lemma right.mul_lt_mul [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (<)]
  {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
mul_lt_mul_of_lt_of_le h₁ h₂.le

@[to_additive add_le_add]
lemma mul_le_mul' [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)

@[to_additive]
lemma mul_le_mul_three [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
  a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]
lemma mul_lt_of_mul_lt_left [covariant_class α α (*) (≤)]
  {a b c d : α} (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
(mul_le_mul_left' hle a).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_left [covariant_class α α (*) (≤)]
  {a b c d : α} (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
@act_rel_of_rel_of_act_rel _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ a _ _ _ hle h

@[to_additive]
lemma mul_lt_of_mul_lt_right [covariant_class α α (swap (*)) (≤)]
  {a b c d : α} (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(mul_le_mul_right' hle b).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_right [covariant_class α α (swap (*)) (≤)]
  {a b c d : α} (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right' hle b).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_left [covariant_class α α (*) (≤)]
  {a b c d : α} (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
lemma le_mul_of_le_mul_left [covariant_class α α (*) (≤)]
  {a b c d : α} (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
@rel_act_of_rel_of_rel_act _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ b _ _ _ hle h

@[to_additive]
lemma lt_mul_of_lt_mul_right [covariant_class α α (swap (*)) (≤)]
  {a b c d : α} (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
lemma le_mul_of_le_mul_right [covariant_class α α (swap (*)) (≤)]
  {a b c d : α} (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right' hle c)

end preorder

section partial_order
variables [partial_order α]

@[to_additive]
lemma mul_left_cancel'' [contravariant_class α α (*) (≤)]
  {a b c : α} (h : a * b = a * c) :
  b = c :=
(le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)

@[to_additive]
lemma mul_right_cancel'' [contravariant_class α α (swap (*)) (≤)]
  {a b c : α} (h : a * b = c * b) :
  a = c :=
le_antisymm (le_of_mul_le_mul_right' h.le) (le_of_mul_le_mul_right' h.ge)

end partial_order

section linear_order
variables [linear_order α] {a b c d : α} [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (<)]

@[to_additive] lemma min_le_max_of_mul_le_mul (h : a * b ≤ c * d) : min a b ≤ max c d :=
by { simp_rw [min_le_iff, le_max_iff], contrapose! h, exact mul_lt_mul_of_lt_of_lt h.1.1 h.2.2 }

end linear_order
end has_mul

-- using one
section mul_one_class
variables [mul_one_class α]

section has_le
variables [has_le α]

@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' [covariant_class α α (*) (≤)]
  {a b : α} (h : 1 ≤ b) :
  a ≤ a * b :=
calc  a = a * 1  : (mul_one a).symm
    ... ≤ a * b  : mul_le_mul_left' h a

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' [covariant_class α α (*) (≤)]
  {a b : α} (h : b ≤ 1) :
  a * b ≤ a :=
calc  a * b ≤ a * 1 : mul_le_mul_left' h a
        ... = a     : mul_one a

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' [covariant_class α α (swap (*)) (≤)]
  {a b : α} (h : 1 ≤ b) :
  a ≤ b * a :=
calc  a = 1 * a  : (one_mul a).symm
    ... ≤ b * a  : mul_le_mul_right' h a

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' [covariant_class α α (swap (*)) (≤)]
  {a b : α} (h : b ≤ 1) :
  b * a ≤ a :=
calc  b * a ≤ 1 * a : mul_le_mul_right' h a
        ... = a     : one_mul a

@[to_additive]
lemma one_le_of_le_mul_right [contravariant_class α α (*) (≤)] {a b : α} (h : a ≤ a * b) : 1 ≤ b :=
le_of_mul_le_mul_left' $ by simpa only [mul_one]

@[to_additive]
lemma le_one_of_mul_le_right [contravariant_class α α (*) (≤)] {a b : α} (h : a * b ≤ a) : b ≤ 1 :=
le_of_mul_le_mul_left' $ by simpa only [mul_one]

@[to_additive]
lemma one_le_of_le_mul_left [contravariant_class α α (swap (*)) (≤)] {a b : α} (h : b ≤ a * b) :
  1 ≤ a :=
le_of_mul_le_mul_right' $ by simpa only [one_mul]

@[to_additive]
lemma le_one_of_mul_le_left [contravariant_class α α (swap (*)) (≤)] {a b : α} (h : a * b ≤ b) :
  a ≤ 1 :=
le_of_mul_le_mul_right' $ by simpa only [one_mul]

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right'
  [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b : α} :
  a ≤ a * b ↔ 1 ≤ b :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left'
  [covariant_class α α (swap (*)) (≤)] [contravariant_class α α (swap (*)) (≤)]
  (a : α) {b : α} :
  a ≤ b * a ↔ 1 ≤ b :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right a)

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right'
  [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b : α} :
  a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left'
  [covariant_class α α (swap (*)) (≤)] [contravariant_class α α (swap (*)) (≤)]
  {a b : α} :
  a * b ≤ b ↔ a ≤ 1 :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right b)

end has_le

section has_lt
variable [has_lt α]

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right' [covariant_class α α (*) (<)]
  (a : α) {b : α} (h : 1 < b) :
  a < a * b :=
calc  a = a * 1  : (mul_one a).symm
    ... < a * b  : mul_lt_mul_left' h a

@[to_additive add_lt_of_neg_right]
lemma mul_lt_of_lt_one_right' [covariant_class α α (*) (<)]
  (a : α) {b : α} (h : b < 1) :
  a * b < a :=
calc  a * b < a * 1 : mul_lt_mul_left' h a
        ... = a     : mul_one a

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' [covariant_class α α (swap (*)) (<)]
  (a : α) {b : α} (h : 1 < b) :
  a < b * a :=
calc  a = 1 * a  : (one_mul a).symm
    ... < b * a  : mul_lt_mul_right' h a

@[to_additive add_lt_of_neg_left]
lemma mul_lt_of_lt_one_left' [covariant_class α α (swap (*)) (<)]
  (a : α) {b : α} (h : b < 1) :
  b * a < a :=
calc  b * a < 1 * a : mul_lt_mul_right' h a
        ... = a     : one_mul a

@[to_additive]
lemma one_lt_of_lt_mul_right [contravariant_class α α (*) (<)] {a b : α} (h : a < a * b) : 1 < b :=
lt_of_mul_lt_mul_left' $ by simpa only [mul_one]

@[to_additive]
lemma lt_one_of_mul_lt_right [contravariant_class α α (*) (<)] {a b : α} (h : a * b < a) : b < 1 :=
lt_of_mul_lt_mul_left' $ by simpa only [mul_one]

@[to_additive]
lemma one_lt_of_lt_mul_left [contravariant_class α α (swap (*)) (<)] {a b : α} (h : b < a * b) :
  1 < a :=
lt_of_mul_lt_mul_right' $ by simpa only [one_mul]

@[to_additive]
lemma lt_one_of_mul_lt_left [contravariant_class α α (swap (*)) (<)] {a b : α} (h : a * b < b) :
  a < 1 :=
lt_of_mul_lt_mul_right' $ by simpa only [one_mul]

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right'
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)]
  (a : α) {b : α} :
  a < a * b ↔ 1 < b :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left'
  [covariant_class α α (swap (*)) (<)] [contravariant_class α α (swap (*)) (<)]
  (a : α) {b : α} :
  a < b * a ↔ 1 < b :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right a)

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left'
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)]
  {a b : α} :
  a * b < a ↔ b < 1 :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right'
  [covariant_class α α (swap (*)) (<)] [contravariant_class α α (swap (*)) (<)]
  {a : α} (b : α) :
  a * b < b ↔ a < 1 :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right b)

end has_lt

section preorder
variable [preorder α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance. -/

@[to_additive]
lemma mul_le_of_le_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... ≤ c     : hbc

@[to_additive]
lemma mul_lt_of_le_of_lt_one [covariant_class α α (*) (<)]
  {a b c : α} (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
calc  b * a < b * 1 : mul_lt_mul_left' ha b
        ... = b     : mul_one b
        ... ≤ c     : hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : a ≤ 1) : b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... < c     : hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one [covariant_class α α (*) (<)]
  {a b c : α} (hbc : b < c) (ha : a < 1) : b * a < c :=
calc  b * a < b * 1 : mul_lt_mul_left' ha b
        ... = b     : mul_one b
        ... < c     : hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one' [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_le_one`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `right.add_nonpos`."]
lemma left.mul_le_one [covariant_class α α (*) (≤)]
  {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
mul_le_of_le_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_le_of_lt`. -/
@[to_additive left.add_neg_of_nonpos_of_neg "Assumes left covariance.
The lemma assuming right covariance is `right.add_neg_of_nonpos_of_neg`."]
lemma left.mul_lt_one_of_le_of_lt [covariant_class α α (*) (<)]
  {a b : α} (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_le_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_lt_of_le`. -/
@[to_additive left.add_neg_of_neg_of_nonpos "Assumes left covariance.
The lemma assuming right covariance is `right.add_neg_of_neg_of_nonpos`."]
lemma left.mul_lt_one_of_lt_of_le [covariant_class α α (*) (≤)]
  {a b : α} (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
mul_lt_of_lt_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `right.add_neg`."]
lemma left.mul_lt_one [covariant_class α α (*) (<)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_lt_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one'`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `right.add_neg'`."]
lemma left.mul_lt_one' [covariant_class α α (*) (≤)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_lt_of_lt_one' ha hb

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/

@[to_additive]
lemma le_mul_of_le_of_one_le [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
calc  b ≤ c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive]
lemma lt_mul_of_le_of_one_lt [covariant_class α α (*) (<)]
  {a b c : α} (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
calc  b ≤ c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... < c * a : mul_lt_mul_left' ha c

@[to_additive]
lemma lt_mul_of_lt_of_one_le [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
calc  b < c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive]
lemma lt_mul_of_lt_of_one_lt [covariant_class α α (*) (<)]
  {a b c : α} (hbc : b < c) (ha : 1 < a) : b < c * a :=
calc  b < c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... < c * a : mul_lt_mul_left' ha c

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : 1 < a) : b < c * a :=
lt_mul_of_lt_of_one_le hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_le_mul`. -/
@[to_additive left.add_nonneg "Assumes left covariance.
The lemma assuming right covariance is `right.add_nonneg`."]
lemma left.one_le_mul [covariant_class α α (*) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_le_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_le_of_lt`. -/
@[to_additive left.add_pos_of_nonneg_of_pos "Assumes left covariance.
The lemma assuming right covariance is `right.add_pos_of_nonneg_of_pos`."]
lemma left.one_lt_mul_of_le_of_lt [covariant_class α α (*) (<)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_le_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_lt_of_le`. -/
@[to_additive left.add_pos_of_pos_of_nonneg "Assumes left covariance.
The lemma assuming right covariance is `right.add_pos_of_pos_of_nonneg`."]
lemma left.one_lt_mul_of_lt_of_le [covariant_class α α (*) (≤)]
  {a b : α} (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_mul_of_lt_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul`. -/
@[to_additive left.add_pos "Assumes left covariance.
The lemma assuming right covariance is `right.add_pos`."]
lemma left.one_lt_mul [covariant_class α α (*) (<)]
  {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_lt_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul'`. -/
@[to_additive left.add_pos' "Assumes left covariance.
The lemma assuming right covariance is `right.add_pos'`."]
lemma left.one_lt_mul' [covariant_class α α (*) (≤)]
  {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_lt_of_one_lt' ha hb

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/

@[to_additive]
lemma mul_le_of_le_one_of_le [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma mul_lt_of_lt_one_of_le [covariant_class α α (swap (*)) (<)]
  {a b c : α} (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma mul_lt_of_le_one_of_lt [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : a ≤ 1) (hb : b < c) : a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

@[to_additive]
lemma mul_lt_of_lt_one_of_lt [covariant_class α α (swap (*)) (<)]
  {a b c : α} (ha : a < 1) (hb : b < c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

@[to_additive]
lemma mul_lt_of_lt_one_of_lt' [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_le_one`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `left.add_nonpos`."]
lemma right.mul_le_one [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
mul_le_of_le_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_lt_of_le`. -/
@[to_additive right.add_neg_of_neg_of_nonpos "Assumes right covariance.
The lemma assuming left covariance is `left.add_neg_of_neg_of_nonpos`."]
lemma right.mul_lt_one_of_lt_of_le [covariant_class α α (swap (*)) (<)]
  {a b : α} (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
mul_lt_of_lt_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_le_of_lt`. -/
@[to_additive right.add_neg_of_nonpos_of_neg "Assumes right covariance.
The lemma assuming left covariance is `left.add_neg_of_nonpos_of_neg`."]
lemma right.mul_lt_one_of_le_of_lt [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_le_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `left.add_neg`."]
lemma right.mul_lt_one [covariant_class α α (swap (*)) (<)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_lt_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one'`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `left.add_neg'`."]
lemma right.mul_lt_one' [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_lt_one_of_lt' ha hb

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/

@[to_additive]
lemma le_mul_of_one_le_of_le [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' ha c

@[to_additive]
lemma lt_mul_of_one_lt_of_le [covariant_class α α (swap (*)) (<)]
  {a b c : α} (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right' ha c

@[to_additive]
lemma lt_mul_of_one_le_of_lt [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
calc  b < c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' ha c

@[to_additive]
lemma lt_mul_of_one_lt_of_lt [covariant_class α α (swap (*)) (<)]
  {a b c : α} (ha : 1 < a) (hbc : b < c) : b < a * c :=
calc  b < c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right' ha c

@[to_additive]
lemma lt_mul_of_one_lt_of_lt' [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_le_mul`. -/
@[to_additive right.add_nonneg "Assumes right covariance.
The lemma assuming left covariance is `left.add_nonneg`."]
lemma right.one_le_mul [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_lt_of_le`. -/
@[to_additive right.add_pos_of_pos_of_nonneg "Assumes right covariance.
The lemma assuming left covariance is `left.add_pos_of_pos_of_nonneg`."]
lemma right.one_lt_mul_of_lt_of_le [covariant_class α α (swap (*)) (<)]
  {a b : α} (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_mul_of_one_lt_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_le_of_lt`. -/
@[to_additive right.add_pos_of_nonneg_of_pos "Assumes right covariance.
The lemma assuming left covariance is `left.add_pos_of_nonneg_of_pos`."]
lemma right.one_lt_mul_of_le_of_lt [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_one_le_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul`. -/
@[to_additive right.add_pos "Assumes right covariance.
The lemma assuming left covariance is `left.add_pos`."]
lemma right.one_lt_mul [covariant_class α α (swap (*)) (<)]
  {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_one_lt_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul'`. -/
@[to_additive right.add_pos' "Assumes right covariance.
The lemma assuming left covariance is `left.add_pos'`."]
lemma right.one_lt_mul' [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_one_lt_of_lt' ha hb

alias left.mul_le_one             ← mul_le_one'
alias left.mul_lt_one_of_le_of_lt ← mul_lt_one_of_le_of_lt
alias left.mul_lt_one_of_lt_of_le ← mul_lt_one_of_lt_of_le
alias left.mul_lt_one             ← mul_lt_one
alias left.mul_lt_one'            ← mul_lt_one'
attribute [to_additive add_nonpos "**Alias** of `left.add_nonpos`."]
mul_le_one'
attribute [to_additive add_neg_of_nonpos_of_neg "**Alias** of `left.add_neg_of_nonpos_of_neg`."]
mul_lt_one_of_le_of_lt
attribute [to_additive add_neg_of_neg_of_nonpos "**Alias** of `left.add_neg_of_neg_of_nonpos`."]
mul_lt_one_of_lt_of_le
attribute [to_additive "**Alias** of `left.add_neg`."]
mul_lt_one
attribute [to_additive "**Alias** of `left.add_neg'`."]
mul_lt_one'

alias left.one_le_mul             ← one_le_mul
alias left.one_lt_mul_of_le_of_lt ← one_lt_mul_of_le_of_lt'
alias left.one_lt_mul_of_lt_of_le ← one_lt_mul_of_lt_of_le'
alias left.one_lt_mul             ← one_lt_mul'
alias left.one_lt_mul'            ← one_lt_mul''
attribute [to_additive add_nonneg "**Alias** of `left.add_nonneg`."]
one_le_mul
attribute [to_additive add_pos_of_nonneg_of_pos "**Alias** of `left.add_pos_of_nonneg_of_pos`."]
one_lt_mul_of_le_of_lt'
attribute [to_additive add_pos_of_pos_of_nonneg "**Alias** of `left.add_pos_of_pos_of_nonneg`."]
one_lt_mul_of_lt_of_le'
attribute [to_additive add_pos "**Alias** of `left.add_pos`."]
one_lt_mul'
attribute [to_additive add_pos' "**Alias** of `left.add_pos'`."]
one_lt_mul''

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left [covariant_class α α (*) (≤)]
  {a b c : α} (h : a * b < c) (hle : 1 ≤ b) : a < c :=
(le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_left [covariant_class α α (*) (≤)]
  {a b c : α} (h : a * b ≤ c) (hle : 1 ≤ b) : a ≤ c :=
(le_mul_of_one_le_right' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_left [covariant_class α α (*) (≤)]
  {a b c : α} (h : a < b * c) (hle : c ≤ 1) : a < b :=
h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_left [covariant_class α α (*) (≤)]
  {a b c : α} (h : a ≤ b * c) (hle : c ≤ 1) : a ≤ b :=
h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
lemma lt_of_mul_lt_of_one_le_right [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (h : a * b < c) (hle : 1 ≤ a) : b < c :=
(le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_right [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
(le_mul_of_one_le_left' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_right [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (h : a < b * c) (hle : b ≤ 1) : a < c :=
h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_right [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
h.trans (mul_le_of_le_one_left' hle)

end preorder

section partial_order
variables [partial_order α]

@[to_additive]
lemma mul_eq_one_iff' [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le le_rfl hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha le_rfl,
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

@[to_additive] lemma mul_le_mul_iff_of_ge [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (≤)] [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (<)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
  a₂ * b₂ ≤ a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
begin
  refine ⟨λ h, _, by { rintro ⟨rfl, rfl⟩, refl }⟩,
  simp only [eq_iff_le_not_lt, ha, hb, true_and],
  refine ⟨λ ha, h.not_lt _, λ hb, h.not_lt _⟩,
  { exact mul_lt_mul_of_lt_of_le ha hb },
  { exact mul_lt_mul_of_le_of_lt ha hb }
end

section left
variables [covariant_class α α (*) (≤)] {a b : α}

@[to_additive eq_zero_of_add_nonneg_left]
lemma eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
ha.eq_of_not_lt $ λ h, hab.not_lt $ mul_lt_one_of_lt_of_le h hb

@[to_additive]
lemma eq_one_of_mul_le_one_left (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : a = 1 :=
ha.eq_of_not_gt $ λ h, hab.not_lt $ one_lt_mul_of_lt_of_le' h hb

end left

section right
variables [covariant_class α α (swap (*)) (≤)] {a b : α}

@[to_additive eq_zero_of_add_nonneg_right]
lemma eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
hb.eq_of_not_lt $ λ h, hab.not_lt $ right.mul_lt_one_of_le_of_lt ha h

@[to_additive]
lemma eq_one_of_mul_le_one_right (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : b = 1 :=
hb.eq_of_not_gt $ λ h, hab.not_lt $ right.one_lt_mul_of_le_of_lt ha h

end right
end partial_order

section linear_order
variables [linear_order α]

lemma exists_square_le [covariant_class α α (*) (<)]
  (a : α) : ∃ (b : α), b * b ≤ a :=
begin
  by_cases h : a < 1,
  { use a,
    have : a*a < a*1,
    exact mul_lt_mul_left' h a,
    rw mul_one at this,
    exact le_of_lt this },
  { use 1,
    push_neg at h,
    rwa mul_one }
end

end linear_order

end mul_one_class

section semigroup
variables [semigroup α]

section partial_order
variables [partial_order α]

/- This is not instance, since we want to have an instance from `left_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `left_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `left_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `left_cancel_add_semigroup`
(i.e. `c + a < c + b → a < b`) is a `left_cancel add_semigroup`."]
def contravariant.to_left_cancel_semigroup
  [contravariant_class α α (*) (≤)] :
  left_cancel_semigroup α :=
{ mul_left_cancel := λ a b c, mul_left_cancel''
  ..‹semigroup α› }

/- This is not instance, since we want to have an instance from `right_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `right_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `right_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `right_cancel_add_semigroup`
(`a + c < b + c → a < b`) is a `right_cancel add_semigroup`."]
def contravariant.to_right_cancel_semigroup
  [contravariant_class α α (swap (*)) (≤)] :
  right_cancel_semigroup α :=
{ mul_right_cancel := λ a b c, mul_right_cancel''
  ..‹semigroup α› }

@[to_additive] lemma left.mul_eq_mul_iff_eq_and_eq
  [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]
  [contravariant_class α α (*) (≤)] [contravariant_class α α (swap (*)) (≤)]
  {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) : a * b = c * d ↔ a = c ∧ b = d :=
begin
  refine ⟨λ h, _, λ h, congr_arg2 (*) h.1 h.2⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, mul_left_cancel'' h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨mul_right_cancel'' h, rfl⟩ },
  exact ((left.mul_lt_mul hac hbd).ne h).elim,
end

@[to_additive] lemma right.mul_eq_mul_iff_eq_and_eq
  [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (<)] [contravariant_class α α (swap (*)) (≤)]
  {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) : a * b = c * d ↔ a = c ∧ b = d :=
begin
  refine ⟨λ h, _, λ h, congr_arg2 (*) h.1 h.2⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, mul_left_cancel'' h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨mul_right_cancel'' h, rfl⟩ },
  exact ((right.mul_lt_mul hac hbd).ne h).elim,
end

alias left.mul_eq_mul_iff_eq_and_eq ← mul_eq_mul_iff_eq_and_eq
attribute [to_additive] mul_eq_mul_iff_eq_and_eq

end partial_order

end semigroup

section mono
variables [has_mul α] [preorder α] [preorder β] {f g : β → α} {s : set β}

@[to_additive const_add]
lemma monotone.const_mul' [covariant_class α α (*) (≤)] (hf : monotone f) (a : α) :
  monotone (λ x, a * f x) :=
λ x y h, mul_le_mul_left' (hf h) a

@[to_additive const_add]
lemma monotone_on.const_mul' [covariant_class α α (*) (≤)] (hf : monotone_on f s) (a : α) :
  monotone_on (λ x, a * f x) s :=
λ x hx y hy h, mul_le_mul_left' (hf hx hy h) a

@[to_additive const_add]
lemma antitone.const_mul' [covariant_class α α (*) (≤)] (hf : antitone f) (a : α) :
  antitone (λ x, a * f x) :=
λ x y h, mul_le_mul_left' (hf h) a

@[to_additive const_add]
lemma antitone_on.const_mul' [covariant_class α α (*) (≤)] (hf : antitone_on f s) (a : α) :
  antitone_on (λ x, a * f x) s :=
λ x hx y hy h, mul_le_mul_left' (hf hx hy h) a

@[to_additive add_const]
lemma monotone.mul_const' [covariant_class α α (swap (*)) (≤)]
  (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
λ x y h, mul_le_mul_right' (hf h) a

@[to_additive add_const]
lemma monotone_on.mul_const' [covariant_class α α (swap (*)) (≤)]
  (hf : monotone_on f s) (a : α) : monotone_on (λ x, f x * a) s :=
λ x hx y hy h, mul_le_mul_right' (hf hx hy h) a

@[to_additive add_const]
lemma antitone.mul_const' [covariant_class α α (swap (*)) (≤)]
  (hf : antitone f) (a : α) : antitone (λ x, f x * a) :=
λ x y h, mul_le_mul_right' (hf h) a

@[to_additive add_const]
lemma antitone_on.mul_const' [covariant_class α α (swap (*)) (≤)]
  (hf : antitone_on f s) (a : α) : antitone_on (λ x, f x * a) s :=
λ x hx y hy h, mul_le_mul_right' (hf hx hy h) a

/--  The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
lemma monotone.mul' [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

/--  The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
lemma monotone_on.mul' [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  (hf : monotone_on f s) (hg : monotone_on g s) : monotone_on (λ x, f x * g x) s :=
λ x hx y hy h, mul_le_mul' (hf hx hy h) (hg hx hy h)

/--  The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
lemma antitone.mul' [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  (hf : antitone f) (hg : antitone g) : antitone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

/--  The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
lemma antitone_on.mul' [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  (hf : antitone_on f s) (hg : antitone_on g s) : antitone_on (λ x, f x * g x) s :=
λ x hx y hy h, mul_le_mul' (hf hx hy h) (hg hx hy h)

section left
variables [covariant_class α α (*) (<)]

@[to_additive const_add] lemma strict_mono.const_mul' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, c * f x) :=
λ a b ab, mul_lt_mul_left' (hf ab) c

@[to_additive const_add] lemma strict_mono_on.const_mul' (hf : strict_mono_on f s) (c : α) :
  strict_mono_on (λ x, c * f x) s :=
λ a ha b hb ab, mul_lt_mul_left' (hf ha hb ab) c

@[to_additive const_add] lemma strict_anti.const_mul' (hf : strict_anti f) (c : α) :
  strict_anti (λ x, c * f x) :=
λ a b ab, mul_lt_mul_left' (hf ab) c

@[to_additive const_add] lemma strict_anti_on.const_mul' (hf : strict_anti_on f s) (c : α) :
  strict_anti_on (λ x, c * f x) s :=
λ a ha b hb ab, mul_lt_mul_left' (hf ha hb ab) c

end left

section right
variables [covariant_class α α (swap (*)) (<)]

@[to_additive add_const] lemma strict_mono.mul_const' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, f x * c) :=
λ a b ab, mul_lt_mul_right' (hf ab) c

@[to_additive add_const] lemma strict_mono_on.mul_const' (hf : strict_mono_on f s) (c : α) :
  strict_mono_on (λ x, f x * c) s :=
λ a ha b hb ab, mul_lt_mul_right' (hf ha hb ab) c

@[to_additive add_const] lemma strict_anti.mul_const' (hf : strict_anti f) (c : α) :
  strict_anti (λ x, f x * c) :=
λ a b ab, mul_lt_mul_right' (hf ab) c

@[to_additive add_const] lemma strict_anti_on.mul_const' (hf : strict_anti_on f s) (c : α) :
  strict_anti_on (λ x, f x * c) s :=
λ a ha b hb ab, mul_lt_mul_right' (hf ha hb ab) c

end right

/--  The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
lemma strict_mono.mul' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  (hf : strict_mono f) (hg : strict_mono g) :
  strict_mono (λ x, f x * g x) :=
λ a b ab, mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/--  The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
lemma strict_mono_on.mul' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  (hf : strict_mono_on f s) (hg : strict_mono_on g s) :
  strict_mono_on (λ x, f x * g x) s :=
λ a ha b hb ab, mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/--  The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
lemma strict_anti.mul' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  (hf : strict_anti f) (hg : strict_anti g) :
  strict_anti (λ x, f x * g x) :=
λ a b ab, mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/--  The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
lemma strict_anti_on.mul' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  (hf : strict_anti_on f s) (hg : strict_anti_on g s) :
  strict_anti_on (λ x, f x * g x) s :=
λ a ha b hb ab, mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/--  The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono
"The sum of a monotone function and a strictly monotone function is strictly monotone."]
lemma monotone.mul_strict_mono' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]
  {f g : β → α} (hf : monotone f) (hg : strict_mono g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/--  The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono
"The sum of a monotone function and a strictly monotone function is strictly monotone."]
lemma monotone_on.mul_strict_mono' [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (≤)] {f g : β → α}
  (hf : monotone_on f s) (hg : strict_mono_on g s) :
  strict_mono_on (λ x, f x * g x) s :=
λ x hx y hy h, mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy  h)

/--  The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti
"The sum of a antitone function and a strictly antitone function is strictly antitone."]
lemma antitone.mul_strict_anti' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]
  {f g : β → α} (hf : antitone f) (hg : strict_anti g) :
  strict_anti (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/--  The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti
"The sum of a antitone function and a strictly antitone function is strictly antitone."]
lemma antitone_on.mul_strict_anti' [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (≤)] {f g : β → α}
  (hf : antitone_on f s) (hg : strict_anti_on g s) :
  strict_anti_on (λ x, f x * g x) s :=
λ x hx y hy h, mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy  h)

variables [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (<)]

/--  The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
"The sum of a strictly monotone function and a monotone function is strictly monotone."]
lemma strict_mono.mul_monotone' (hf : strict_mono f) (hg : monotone g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/--  The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
"The sum of a strictly monotone function and a monotone function is strictly monotone."]
lemma strict_mono_on.mul_monotone' (hf : strict_mono_on f s) (hg : monotone_on g s) :
  strict_mono_on (λ x, f x * g x) s :=
λ x hx y hy h, mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

/--  The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
"The sum of a strictly antitone function and a antitone function is strictly antitone."]
lemma strict_anti.mul_antitone' (hf : strict_anti f) (hg : antitone g) :
  strict_anti (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/--  The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
"The sum of a strictly antitone function and a antitone function is strictly antitone."]
lemma strict_anti_on.mul_antitone' (hf : strict_anti_on f s) (hg : antitone_on g s) :
  strict_anti_on (λ x, f x * g x) s :=
λ x hx y hy h, mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

@[simp, to_additive cmp_add_left]
lemma cmp_mul_left' {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (*) (<)]
  (a b c : α) : cmp (a * b) (a * c) = cmp b c :=
(strict_mono_id.const_mul' a).cmp_map_eq b c

@[simp, to_additive cmp_add_right]
lemma cmp_mul_right' {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (swap (*)) (<)]
  (a b c : α) : cmp (a * c) (b * c) = cmp a b :=
(strict_mono_id.mul_const' c).cmp_map_eq a b

end mono

/--
An element `a : α` is `mul_le_cancellable` if `x ↦ a * x` is order-reflecting.
We will make a separate version of many lemmas that require `[contravariant_class α α (*) (≤)]` with
`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`.
-/
@[to_additive /-" An element `a : α` is `add_le_cancellable` if `x ↦ a + x` is order-reflecting.
We will make a separate version of many lemmas that require `[contravariant_class α α (+) (≤)]` with
`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`. "-/
]
def mul_le_cancellable [has_mul α] [has_le α] (a : α) : Prop :=
∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c

@[to_additive]
lemma contravariant.mul_le_cancellable [has_mul α] [has_le α] [contravariant_class α α (*) (≤)]
  {a : α} : mul_le_cancellable a :=
λ b c, le_of_mul_le_mul_left'

@[to_additive] lemma mul_le_cancellable_one [monoid α] [has_le α] : mul_le_cancellable (1 : α) :=
λ a b, by simpa only [one_mul] using id

namespace mul_le_cancellable

@[to_additive]
protected lemma injective [has_mul α] [partial_order α] {a : α} (ha : mul_le_cancellable a) :
  injective ((*) a) :=
λ b c h, le_antisymm (ha h.le) (ha h.ge)

@[to_additive]
protected lemma inj [has_mul α] [partial_order α] {a b c : α} (ha : mul_le_cancellable a) :
  a * b = a * c ↔ b = c :=
ha.injective.eq_iff

@[to_additive]
protected lemma injective_left [comm_semigroup α] [partial_order α] {a : α}
  (ha : mul_le_cancellable a) : injective (* a) :=
λ b c h, ha.injective $ by rwa [mul_comm a, mul_comm a]

@[to_additive]
protected lemma inj_left [comm_semigroup α] [partial_order α] {a b c : α}
  (hc : mul_le_cancellable c) : a * c = b * c ↔ a = b :=
hc.injective_left.eq_iff

variable [has_le α]

@[to_additive]
protected lemma mul_le_mul_iff_left [has_mul α] [covariant_class α α (*) (≤)]
  {a b c : α} (ha : mul_le_cancellable a) : a * b ≤ a * c ↔ b ≤ c :=
⟨λ h, ha h, λ h, mul_le_mul_left' h a⟩

@[to_additive]
protected lemma mul_le_mul_iff_right [comm_semigroup α] [covariant_class α α (*) (≤)]
  {a b c : α} (ha : mul_le_cancellable a) : b * a ≤ c * a ↔ b ≤ c :=
by rw [mul_comm b, mul_comm c, ha.mul_le_mul_iff_left]

@[to_additive]
protected lemma le_mul_iff_one_le_right [mul_one_class α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : a ≤ a * b ↔ 1 ≤ b :=
iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
protected lemma mul_le_iff_le_one_right [mul_one_class α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
protected lemma le_mul_iff_one_le_left [comm_monoid α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : a ≤ b * a ↔ 1 ≤ b :=
by rw [mul_comm, ha.le_mul_iff_one_le_right]

@[to_additive]
protected lemma mul_le_iff_le_one_left [comm_monoid α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : b * a ≤ a ↔ b ≤ 1 :=
by rw [mul_comm, ha.mul_le_iff_le_one_right]

end mul_le_cancellable

section bit
variables [has_add α] [preorder α]

lemma bit0_mono [covariant_class α α (+) (≤)] [covariant_class α α (swap (+)) (≤)] :
  monotone (bit0 : α → α) := λ a b h, add_le_add h h

lemma bit0_strict_mono [covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (<)] :
  strict_mono (bit0 : α → α) := λ a b h, add_lt_add h h

end bit
