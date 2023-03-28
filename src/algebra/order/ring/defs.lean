/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/

import algebra.order.group.defs
import algebra.order.monoid.cancel.defs
import algebra.order.monoid.canonical.defs
import algebra.order.monoid.nat_cast
import algebra.order.monoid.with_zero.defs
import algebra.order.ring.lemmas
import algebra.ring.defs
import order.min_max
import tactic.nontriviality
import data.pi.algebra
import algebra.group.units

/-!
# Ordered rings and semirings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`semiring`, `comm_semiring`, `ring`, `comm_ring`)
* an order class (`partial_order`, `linear_order`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `ordered_semiring`: Semiring with a partial order such that `+` and `*` respect `≤`.
* `strict_ordered_semiring`: Nontrivial semiring with a partial order such that `+` and `*` respects
  `<`.
* `ordered_comm_semiring`: Commutative semiring with a partial order such that `+` and `*` respect
  `≤`.
* `strict_ordered_comm_semiring`: Nontrivial commutative semiring with a partial order such that `+`
  and `*` respect `<`.
* `ordered_ring`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `ordered_comm_ring`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_semiring`: Nontrivial semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_comm_semiring`: Nontrivial commutative semiring with a linear order such that `+`
  respects `≤` and `*` respects `<`.
* `linear_ordered_ring`: Nontrivial ring with a linear order such that `+` respects `≤` and `*`
  respects `<`.
* `linear_ordered_comm_ring`: Nontrivial commutative ring with a linear order such that `+` respects
  `≤` and `*` respects `<`.
* `canonically_ordered_comm_semiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `ordered_semiring`
  - `ordered_add_comm_monoid` & multiplication & `*` respects `≤`
  - `semiring` & partial order structure & `+` respects `≤` & `*` respects `≤`
* `strict_ordered_semiring`
  - `ordered_cancel_add_comm_monoid` & multiplication & `*` respects `<` & nontriviality
  - `ordered_semiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `ordered_comm_semiring`
  - `ordered_semiring` & commutativity of multiplication
  - `comm_semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `strict_ordered_comm_semiring`
  - `strict_ordered_semiring` & commutativity of multiplication
  - `ordered_comm_semiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `ordered_ring`
  - `ordered_semiring` & additive inverses
  - `ordered_add_comm_group` & multiplication & `*` respects `<`
  - `ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `strict_ordered_ring`
  - `strict_ordered_semiring` & additive inverses
  - `ordered_semiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `ordered_comm_ring`
  - `ordered_ring` & commutativity of multiplication
  - `ordered_comm_semiring` & additive inverses
  - `comm_ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `strict_ordered_comm_ring`
  - `strict_ordered_comm_semiring` & additive inverses
  - `strict_ordered_ring` & commutativity of multiplication
  - `ordered_comm_ring` & `+` respects `<` & `*` respects `<` & nontriviality
* `linear_ordered_semiring`
  - `strict_ordered_semiring` & totality of the order
  - `linear_ordered_add_comm_monoid` & multiplication & nontriviality & `*` respects `<`
* `linear_ordered_comm_semiring`
  - `strict_ordered_comm_semiring` & totality of the order
  - `linear_ordered_semiring` & commutativity of multiplication
* `linear_ordered_ring`
  - `strict_ordered_ring` & totality of the order
  - `linear_ordered_semiring` & additive inverses
  - `linear_ordered_add_comm_group` & multiplication & `*` respects `<`
  - `domain` & linear order structure
* `linear_ordered_comm_ring`
  - `strict_ordered_comm_ring` & totality of the order
  - `linear_ordered_ring` & commutativity of multiplication
  - `linear_ordered_comm_semiring` & additive inverses
  - `is_domain` & linear order structure

-/

open function

set_option old_structure_cmd true

universe u
variables {α : Type u} {β : Type*}

/-! Note that `order_dual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/

lemma add_one_le_two_mul [has_le α] [semiring α] [covariant_class α α (+) (≤)]
  {a : α} (a1 : 1 ≤ a) :
  a + 1 ≤ 2 * a :=
calc  a + 1 ≤ a + a : add_le_add_left a1 a
        ... = 2 * a : (two_mul _).symm

/-- An `ordered_semiring` is a semiring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
@[protect_proj, ancestor semiring ordered_add_comm_monoid]
class ordered_semiring (α : Type u) extends semiring α, ordered_add_comm_monoid α :=
(zero_le_one : (0 : α) ≤ 1)
(mul_le_mul_of_nonneg_left  : ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b)
(mul_le_mul_of_nonneg_right : ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c)

/-- An `ordered_comm_semiring` is a commutative semiring with a partial order such that addition is
monotone and multiplication by a nonnegative number is monotone. -/
@[protect_proj, ancestor ordered_semiring comm_semiring]
class ordered_comm_semiring (α : Type u) extends ordered_semiring α, comm_semiring α

/-- An `ordered_ring` is a ring with a partial order such that addition is monotone and
multiplication by a nonnegative number is monotone. -/
@[protect_proj, ancestor ring ordered_add_comm_group]
class ordered_ring (α : Type u) extends ring α, ordered_add_comm_group α :=
(zero_le_one : 0 ≤ (1 : α))
(mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

/-- An `ordered_comm_ring` is a commutative ring with a partial order such that addition is monotone
and multiplication by a nonnegative number is monotone. -/
@[protect_proj, ancestor ordered_ring comm_ring]
class ordered_comm_ring (α : Type u) extends ordered_ring α, comm_ring α

/-- A `strict_ordered_semiring` is a nontrivial semiring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj, ancestor semiring ordered_cancel_add_comm_monoid nontrivial]
class strict_ordered_semiring (α : Type u)
  extends semiring α, ordered_cancel_add_comm_monoid α, nontrivial α :=
(zero_le_one : (0 : α) ≤ 1)
(mul_lt_mul_of_pos_left  : ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c)

/-- A `strict_ordered_comm_semiring` is a commutative semiring with a partial order such that
addition is strictly monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj, ancestor strict_ordered_semiring comm_semiring]
class strict_ordered_comm_semiring (α : Type u) extends strict_ordered_semiring α, comm_semiring α

/-- A `strict_ordered_ring` is a ring with a partial order such that addition is strictly monotone
and multiplication by a positive number is strictly monotone. -/
@[protect_proj, ancestor ring ordered_add_comm_group nontrivial]
class strict_ordered_ring (α : Type u) extends ring α, ordered_add_comm_group α, nontrivial α :=
(zero_le_one : 0 ≤ (1 : α))
(mul_pos     : ∀ a b : α, 0 < a → 0 < b → 0 < a * b)

/-- A `strict_ordered_comm_ring` is a commutative ring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj, ancestor strict_ordered_ring comm_ring]
class strict_ordered_comm_ring (α : Type*) extends strict_ordered_ring α, comm_ring α

/-- A `linear_ordered_semiring` is a nontrivial semiring with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
/- It's not entirely clear we should assume `nontrivial` at this point; it would be reasonable to
explore changing this, but be warned that the instances involving `domain` may cause typeclass
search loops. -/
@[protect_proj, ancestor strict_ordered_semiring linear_ordered_add_comm_monoid nontrivial]
class linear_ordered_semiring (α : Type u)
  extends strict_ordered_semiring α, linear_ordered_add_comm_monoid α

/-- A `linear_ordered_comm_semiring` is a nontrivial commutative semiring with a linear order such
that addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj, ancestor ordered_comm_semiring linear_ordered_semiring]
class linear_ordered_comm_semiring (α : Type*)
  extends strict_ordered_comm_semiring α, linear_ordered_semiring α

/-- A `linear_ordered_ring` is a ring with a linear order such that addition is monotone and
multiplication by a positive number is strictly monotone. -/
@[protect_proj, ancestor strict_ordered_ring linear_order]
class linear_ordered_ring (α : Type u) extends strict_ordered_ring α, linear_order α

/-- A `linear_ordered_comm_ring` is a commutative ring with a linear order such that addition is
monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj, ancestor linear_ordered_ring comm_monoid]
class linear_ordered_comm_ring (α : Type u) extends linear_ordered_ring α, comm_monoid α


section ordered_semiring
variables [ordered_semiring α] {a b c d : α}

@[priority 100] -- see Note [lower instance priority]
instance ordered_semiring.zero_le_one_class : zero_le_one_class α :=
{ ..‹ordered_semiring α› }

@[priority 200] -- see Note [lower instance priority]
instance ordered_semiring.to_pos_mul_mono : pos_mul_mono α :=
⟨λ x a b h, ordered_semiring.mul_le_mul_of_nonneg_left _ _ _ h x.2⟩

@[priority 200] -- see Note [lower instance priority]
instance ordered_semiring.to_mul_pos_mono : mul_pos_mono α :=
⟨λ x a b h, ordered_semiring.mul_le_mul_of_nonneg_right _ _ _ h x.2⟩

lemma bit1_mono : monotone (bit1 : α → α) := λ a b h, add_le_add_right (bit0_mono h) _

@[simp] lemma pow_nonneg (H : 0 ≤ a) : ∀ (n : ℕ), 0 ≤ a ^ n
| 0     := by { rw pow_zero, exact zero_le_one}
| (n+1) := by { rw pow_succ, exact mul_nonneg H (pow_nonneg _) }

lemma add_le_mul_two_add (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
calc a + (2 + b) ≤ a + (a + a * b) :
      add_le_add_left (add_le_add a2 $ le_mul_of_one_le_left b0 $ one_le_two.trans a2) a
             ... ≤ a * (2 + b) : by rw [mul_add, mul_two, add_assoc]

lemma one_le_mul_of_one_le_of_one_le (ha : 1 ≤ a) (hb : 1 ≤ b) : (1 : α) ≤ a * b :=
left.one_le_mul_of_le_of_le ha hb $ zero_le_one.trans ha

section monotone
variables [preorder β] {f g : β → α}

lemma monotone_mul_left_of_nonneg (ha : 0 ≤ a) : monotone (λ x, a * x) :=
λ b c h, mul_le_mul_of_nonneg_left h ha

lemma monotone_mul_right_of_nonneg (ha : 0 ≤ a) : monotone (λ x, x * a) :=
λ b c h, mul_le_mul_of_nonneg_right h ha

lemma monotone.mul_const (hf : monotone f) (ha : 0 ≤ a) : monotone (λ x, f x * a) :=
(monotone_mul_right_of_nonneg ha).comp hf

lemma monotone.const_mul (hf : monotone f) (ha : 0 ≤ a) : monotone (λ x, a * f x) :=
(monotone_mul_left_of_nonneg ha).comp hf

lemma antitone.mul_const (hf : antitone f) (ha : 0 ≤ a) : antitone (λ x, f x * a) :=
(monotone_mul_right_of_nonneg ha).comp_antitone hf

lemma antitone.const_mul (hf : antitone f) (ha : 0 ≤ a) : antitone (λ x, a * f x) :=
(monotone_mul_left_of_nonneg ha).comp_antitone hf

lemma monotone.mul (hf : monotone f) (hg : monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
  monotone (f * g) :=
λ b c h, mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

end monotone

lemma bit1_pos [nontrivial α] (h : 0 ≤ a) : 0 < bit1 a :=
zero_lt_one.trans_le $ bit1_zero.symm.trans_le $ bit1_mono h

lemma bit1_pos' (h : 0 < a) : 0 < bit1 a := by { nontriviality, exact bit1_pos h.le }

lemma mul_le_one (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
one_mul (1 : α) ▸ mul_le_mul ha hb hb' zero_le_one

lemma one_lt_mul_of_le_of_lt (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
hb.trans_le $ le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

lemma one_lt_mul_of_lt_of_le (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
ha.trans_le $ le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul_of_le_of_lt ← one_lt_mul

lemma mul_lt_one_of_nonneg_of_lt_one_left (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
(mul_le_of_le_one_right ha₀ hb).trans_lt ha

lemma mul_lt_one_of_nonneg_of_lt_one_right (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
(mul_le_of_le_one_left hb₀ ha).trans_lt hb

end ordered_semiring

section ordered_ring
variables [ordered_ring α] {a b c d : α}

@[priority 100] -- see Note [lower instance priority]
instance ordered_ring.to_ordered_semiring : ordered_semiring α :=
{ mul_le_mul_of_nonneg_left := λ a b c h hc,
    by simpa only [mul_sub, sub_nonneg] using ordered_ring.mul_nonneg _ _ hc (sub_nonneg.2 h),
  mul_le_mul_of_nonneg_right := λ a b c h hc,
    by simpa only [sub_mul, sub_nonneg] using ordered_ring.mul_nonneg _ _ (sub_nonneg.2 h) hc,
  ..‹ordered_ring α›, ..ring.to_semiring }

lemma mul_le_mul_of_nonpos_left (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b :=
by simpa only [neg_mul, neg_le_neg_iff] using mul_le_mul_of_nonneg_left h (neg_nonneg.2 hc)

lemma mul_le_mul_of_nonpos_right (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
by simpa only [mul_neg, neg_le_neg_iff] using mul_le_mul_of_nonneg_right h (neg_nonneg.2 hc)

lemma mul_nonneg_of_nonpos_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
by simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

lemma mul_le_mul_of_nonneg_of_nonpos (hca : c ≤ a) (hbd : b ≤ d) (hc : 0 ≤ c) (hb : b ≤ 0) :
  a * b ≤ c * d :=
(mul_le_mul_of_nonpos_right hca hb).trans $ mul_le_mul_of_nonneg_left hbd hc

lemma mul_le_mul_of_nonneg_of_nonpos' (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) :
  a * b ≤ c * d :=
(mul_le_mul_of_nonneg_left hbd ha).trans $ mul_le_mul_of_nonpos_right hca hd

lemma mul_le_mul_of_nonpos_of_nonneg (hac : a ≤ c) (hdb : d ≤ b) (hc : c ≤ 0) (hb : 0 ≤ b) :
  a * b ≤ c * d :=
(mul_le_mul_of_nonneg_right hac hb).trans $ mul_le_mul_of_nonpos_left hdb hc

lemma mul_le_mul_of_nonpos_of_nonneg' (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) :
  a * b ≤ c * d :=
(mul_le_mul_of_nonneg_left hbd ha).trans $ mul_le_mul_of_nonpos_right hca hd

lemma mul_le_mul_of_nonpos_of_nonpos (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≤ 0) (hb : b ≤ 0) :
  a * b ≤ c * d :=
(mul_le_mul_of_nonpos_right hca hb).trans $ mul_le_mul_of_nonpos_left hdb hc

lemma mul_le_mul_of_nonpos_of_nonpos' (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≤ 0) (hd : d ≤ 0) :
  a * b ≤ c * d :=
(mul_le_mul_of_nonpos_left hdb ha).trans $ mul_le_mul_of_nonpos_right hca hd

section monotone
variables [preorder β] {f g : β → α}

lemma antitone_mul_left {a : α} (ha : a ≤ 0) : antitone ((*) a) :=
λ b c b_le_c, mul_le_mul_of_nonpos_left b_le_c ha

lemma antitone_mul_right {a : α} (ha : a ≤ 0) : antitone (λ x, x * a) :=
λ b c b_le_c, mul_le_mul_of_nonpos_right b_le_c ha

lemma monotone.const_mul_of_nonpos (hf : monotone f) (ha : a ≤ 0) : antitone (λ x, a * f x) :=
(antitone_mul_left ha).comp_monotone hf

lemma monotone.mul_const_of_nonpos (hf : monotone f) (ha : a ≤ 0) : antitone (λ x, f x * a) :=
(antitone_mul_right ha).comp_monotone hf

lemma antitone.const_mul_of_nonpos (hf : antitone f) (ha : a ≤ 0) : monotone (λ x, a * f x) :=
(antitone_mul_left ha).comp hf

lemma antitone.mul_const_of_nonpos (hf : antitone f) (ha : a ≤ 0) : monotone (λ x, f x * a) :=
(antitone_mul_right ha).comp hf

lemma antitone.mul_monotone (hf : antitone f) (hg : monotone g) (hf₀ : ∀ x, f x ≤ 0)
  (hg₀ : ∀ x, 0 ≤ g x) :
  antitone (f * g) :=
λ b c h, mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)

lemma monotone.mul_antitone (hf : monotone f) (hg : antitone g) (hf₀ : ∀ x, 0 ≤ f x)
  (hg₀ : ∀ x, g x ≤ 0) :
  antitone (f * g) :=
λ b c h, mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

lemma antitone.mul (hf : antitone f) (hg : antitone g) (hf₀ : ∀ x, f x ≤ 0) (hg₀ : ∀ x, g x ≤ 0) :
  monotone (f * g) :=
λ b c h, mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

end monotone

lemma le_iff_exists_nonneg_add (a b : α) : a ≤ b ↔ ∃ c ≥ 0, b = a + c :=
⟨λ h, ⟨b - a, sub_nonneg.mpr h, by simp⟩,
  λ ⟨c, hc, h⟩, by { rw [h, le_add_iff_nonneg_right], exact hc }⟩

end ordered_ring

section ordered_comm_ring
variables [ordered_comm_ring α]

@[priority 100] -- See note [lower instance priority]
instance ordered_comm_ring.to_ordered_comm_semiring : ordered_comm_semiring α :=
{ ..ordered_ring.to_ordered_semiring, ..‹ordered_comm_ring α› }

end ordered_comm_ring

section strict_ordered_semiring
variables [strict_ordered_semiring α] {a b c d : α}

@[priority 200] -- see Note [lower instance priority]
instance strict_ordered_semiring.to_pos_mul_strict_mono : pos_mul_strict_mono α :=
⟨λ x a b h, strict_ordered_semiring.mul_lt_mul_of_pos_left _ _ _ h x.prop⟩

@[priority 200] -- see Note [lower instance priority]
instance strict_ordered_semiring.to_mul_pos_strict_mono : mul_pos_strict_mono α :=
⟨λ x a b h, strict_ordered_semiring.mul_lt_mul_of_pos_right _ _ _ h x.prop⟩

/-- A choice-free version of `strict_ordered_semiring.to_ordered_semiring` to avoid using choice in
basic `nat` lemmas. -/
@[reducible] -- See note [reducible non-instances]
def strict_ordered_semiring.to_ordered_semiring' [@decidable_rel α (≤)] : ordered_semiring α :=
{ mul_le_mul_of_nonneg_left := λ a b c hab hc, begin
    obtain rfl | hab := decidable.eq_or_lt_of_le hab,
    { refl },
    obtain rfl | hc := decidable.eq_or_lt_of_le hc,
    { simp },
    { exact (mul_lt_mul_of_pos_left hab hc).le }
  end,
  mul_le_mul_of_nonneg_right := λ a b c hab hc, begin
    obtain rfl | hab := decidable.eq_or_lt_of_le hab,
    { refl },
    obtain rfl | hc := decidable.eq_or_lt_of_le hc,
    { simp },
    { exact (mul_lt_mul_of_pos_right hab hc).le }
  end,
  ..‹strict_ordered_semiring α› }

@[priority 100] -- see Note [lower instance priority]
instance strict_ordered_semiring.to_ordered_semiring : ordered_semiring α :=
{ mul_le_mul_of_nonneg_left := λ _ _ _, begin
    letI := @strict_ordered_semiring.to_ordered_semiring' α _ (classical.dec_rel _),
    exact mul_le_mul_of_nonneg_left,
  end,
  mul_le_mul_of_nonneg_right := λ _ _ _, begin
    letI := @strict_ordered_semiring.to_ordered_semiring' α _ (classical.dec_rel _),
    exact mul_le_mul_of_nonneg_right,
  end,
  ..‹strict_ordered_semiring α› }

lemma mul_lt_mul (hac : a < c) (hbd : b ≤ d) (hb : 0 < b) (hc : 0 ≤ c) : a * b < c * d :=
(mul_lt_mul_of_pos_right hac hb).trans_le $ mul_le_mul_of_nonneg_left hbd hc

lemma mul_lt_mul' (hac : a ≤ c) (hbd : b < d) (hb : 0 ≤ b) (hc : 0 < c) : a * b < c * d :=
(mul_le_mul_of_nonneg_right hac hb).trans_lt $ mul_lt_mul_of_pos_left hbd hc

@[simp] theorem pow_pos (H : 0 < a) : ∀ (n : ℕ), 0 < a ^ n
| 0     := by { nontriviality, rw pow_zero, exact zero_lt_one }
| (n+1) := by { rw pow_succ, exact mul_pos H (pow_pos _) }

lemma mul_self_lt_mul_self (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
mul_lt_mul' h2.le h2 h1 $ h1.trans_lt h2

-- In the next lemma, we used to write `set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
lemma strict_mono_on_mul_self : strict_mono_on (λ x : α, x * x) {x | 0 ≤ x} :=
λ x hx y hy hxy, mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected lemma decidable.mul_lt_mul'' [@decidable_rel α (≤)]
  (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
h4.lt_or_eq_dec.elim
  (λ b0, mul_lt_mul h1 h2.le b0 $ h3.trans h1.le)
  (λ b0, by rw [← b0, mul_zero]; exact
    mul_pos (h3.trans_lt h1) (h4.trans_lt h2))

lemma mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d :=
by classical; exact decidable.mul_lt_mul''

lemma lt_mul_left (hn : 0 < a) (hm : 1 < b) : a < b * a :=
by { convert mul_lt_mul_of_pos_right hm hn, rw one_mul }

lemma lt_mul_right (hn : 0 < a) (hm : 1 < b) : a < a * b :=
by { convert mul_lt_mul_of_pos_left hm hn, rw mul_one }

lemma lt_mul_self (hn : 1 < a) : a < a * a :=
lt_mul_left (hn.trans_le' zero_le_one) hn

section monotone
variables [preorder β] {f g : β → α}

lemma strict_mono_mul_left_of_pos (ha : 0 < a) : strict_mono (λ x, a * x) :=
assume b c b_lt_c, mul_lt_mul_of_pos_left b_lt_c ha

lemma strict_mono_mul_right_of_pos (ha : 0 < a) : strict_mono (λ x, x * a) :=
assume b c b_lt_c, mul_lt_mul_of_pos_right b_lt_c ha

lemma strict_mono.mul_const (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, (f x) * a) :=
(strict_mono_mul_right_of_pos ha).comp hf

lemma strict_mono.const_mul (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, a * (f x)) :=
(strict_mono_mul_left_of_pos ha).comp hf

lemma strict_anti.mul_const (hf : strict_anti f) (ha : 0 < a) : strict_anti (λ x, f x * a) :=
(strict_mono_mul_right_of_pos ha).comp_strict_anti hf

lemma strict_anti.const_mul (hf : strict_anti f) (ha : 0 < a) : strict_anti (λ x, a * f x) :=
(strict_mono_mul_left_of_pos ha).comp_strict_anti hf

lemma strict_mono.mul_monotone (hf : strict_mono f) (hg : monotone g) (hf₀ : ∀ x, 0 ≤ f x)
  (hg₀ : ∀ x, 0 < g x) :
  strict_mono (f * g) :=
λ b c h, mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

lemma monotone.mul_strict_mono (hf : monotone f) (hg : strict_mono g) (hf₀ : ∀ x, 0 < f x)
  (hg₀ : ∀ x, 0 ≤ g x) :
  strict_mono (f * g) :=
λ b c h, mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

lemma strict_mono.mul (hf : strict_mono f) (hg : strict_mono g) (hf₀ : ∀ x, 0 ≤ f x)
  (hg₀ : ∀ x, 0 ≤ g x) :
  strict_mono (f * g) :=
λ b c h, mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end monotone

lemma lt_two_mul_self (ha : 0 < a) : a < 2 * a := lt_mul_of_one_lt_left ha one_lt_two

@[priority 100] -- see Note [lower instance priority]
instance strict_ordered_semiring.to_no_max_order : no_max_order α :=
⟨λ a, ⟨a + 1, lt_add_of_pos_right _ one_pos⟩⟩

end strict_ordered_semiring

section strict_ordered_comm_semiring
variables [strict_ordered_comm_semiring α]

/-- A choice-free version of `strict_ordered_comm_semiring.to_ordered_comm_semiring` to avoid using
choice in basic `nat` lemmas. -/
@[reducible] -- See note [reducible non-instances]
def strict_ordered_comm_semiring.to_ordered_comm_semiring' [@decidable_rel α (≤)] :
  ordered_comm_semiring α :=
{ ..‹strict_ordered_comm_semiring α›, ..strict_ordered_semiring.to_ordered_semiring' }

@[priority 100] -- see Note [lower instance priority]
instance strict_ordered_comm_semiring.to_ordered_comm_semiring : ordered_comm_semiring α :=
{ ..‹strict_ordered_comm_semiring α›, ..strict_ordered_semiring.to_ordered_semiring }

end strict_ordered_comm_semiring

section strict_ordered_ring
variables [strict_ordered_ring α] {a b c : α}

@[priority 100] -- see Note [lower instance priority]
instance strict_ordered_ring.to_strict_ordered_semiring : strict_ordered_semiring α :=
{ le_of_add_le_add_left := @le_of_add_le_add_left α _ _ _,
  mul_lt_mul_of_pos_left := λ a b c h hc,
    by simpa only [mul_sub, sub_pos] using strict_ordered_ring.mul_pos _ _ hc (sub_pos.2 h),
  mul_lt_mul_of_pos_right := λ a b c h hc,
    by simpa only [sub_mul, sub_pos] using strict_ordered_ring.mul_pos _ _ (sub_pos.2 h) hc,
  ..‹strict_ordered_ring α›,  ..ring.to_semiring }

/-- A choice-free version of `strict_ordered_ring.to_ordered_ring` to avoid using choice in basic
`int` lemmas. -/
@[reducible] -- See note [reducible non-instances]
def strict_ordered_ring.to_ordered_ring' [@decidable_rel α (≤)] : ordered_ring α :=
{ mul_nonneg := λ a b ha hb, begin
    obtain ha | ha := decidable.eq_or_lt_of_le ha,
    { rw [←ha, zero_mul] },
    obtain hb | hb := decidable.eq_or_lt_of_le hb,
    { rw [←hb, mul_zero] },
    { exact (strict_ordered_ring.mul_pos _ _ ha hb).le }
  end,
  ..‹strict_ordered_ring α›,  ..ring.to_semiring }

@[priority 100] -- see Note [lower instance priority]
instance strict_ordered_ring.to_ordered_ring : ordered_ring α :=
{ mul_nonneg := λ a b, begin
    letI := @strict_ordered_ring.to_ordered_ring' α _ (classical.dec_rel _),
    exact mul_nonneg,
  end,
  ..‹strict_ordered_ring α› }

lemma mul_lt_mul_of_neg_left (h : b < a) (hc : c < 0) : c * a < c * b :=
by simpa only [neg_mul, neg_lt_neg_iff] using mul_lt_mul_of_pos_left h (neg_pos_of_neg hc)

lemma mul_lt_mul_of_neg_right (h : b < a) (hc : c < 0) : a * c < b * c :=
by simpa only [mul_neg, neg_lt_neg_iff] using mul_lt_mul_of_pos_right h (neg_pos_of_neg hc)

lemma mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
by simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

section monotone
variables [preorder β] {f g : β → α}

lemma strict_anti_mul_left {a : α} (ha : a < 0) : strict_anti ((*) a) :=
λ b c b_lt_c, mul_lt_mul_of_neg_left b_lt_c ha

lemma strict_anti_mul_right {a : α} (ha : a < 0) : strict_anti (λ x, x * a) :=
λ b c b_lt_c, mul_lt_mul_of_neg_right b_lt_c ha

lemma strict_mono.const_mul_of_neg (hf : strict_mono f) (ha : a < 0) : strict_anti (λ x, a * f x) :=
(strict_anti_mul_left ha).comp_strict_mono hf

lemma strict_mono.mul_const_of_neg (hf : strict_mono f) (ha : a < 0) : strict_anti (λ x, f x * a) :=
(strict_anti_mul_right ha).comp_strict_mono hf

lemma strict_anti.const_mul_of_neg (hf : strict_anti f) (ha : a < 0) : strict_mono (λ x, a * f x) :=
(strict_anti_mul_left ha).comp hf

lemma strict_anti.mul_const_of_neg (hf : strict_anti f) (ha : a < 0) : strict_mono (λ x, f x * a) :=
(strict_anti_mul_right ha).comp hf

end monotone
end strict_ordered_ring

section strict_ordered_comm_ring
variables [strict_ordered_comm_ring α]

/-- A choice-free version of `strict_ordered_comm_ring.to_ordered_comm_semiring'` to avoid using
choice in basic `int` lemmas. -/
@[reducible] -- See note [reducible non-instances]
def strict_ordered_comm_ring.to_ordered_comm_ring' [@decidable_rel α (≤)] : ordered_comm_ring α :=
{ ..‹strict_ordered_comm_ring α›, ..strict_ordered_ring.to_ordered_ring' }

@[priority 100] -- See note [lower instance priority]
instance strict_ordered_comm_ring.to_strict_ordered_comm_semiring :
  strict_ordered_comm_semiring α :=
{ ..‹strict_ordered_comm_ring α›, ..strict_ordered_ring.to_strict_ordered_semiring }

@[priority 100] -- See note [lower instance priority]
instance strict_ordered_comm_ring.to_ordered_comm_ring : ordered_comm_ring α :=
{ ..‹strict_ordered_comm_ring α›, ..strict_ordered_ring.to_ordered_ring }

end strict_ordered_comm_ring

section linear_ordered_semiring
variables [linear_ordered_semiring α] {a b c d : α}

@[priority 200] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_pos_mul_reflect_lt : pos_mul_reflect_lt α :=
⟨λ a b c, (monotone_mul_left_of_nonneg a.2).reflect_lt⟩

@[priority 200] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_mul_pos_reflect_lt : mul_pos_reflect_lt α :=
⟨λ a b c, (monotone_mul_right_of_nonneg a.2).reflect_lt⟩

local attribute [instance] linear_ordered_semiring.decidable_le linear_ordered_semiring.decidable_lt

lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg (hab : 0 ≤ a * b) :
    (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) :=
begin
  refine decidable.or_iff_not_and_not.2 _,
  simp only [not_and, not_le], intros ab nab, apply not_lt_of_le hab _,
  rcases lt_trichotomy 0 a with (ha|rfl|ha),
  exacts [mul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    mul_neg_of_neg_of_pos ha (nab ha.le)]
end

lemma nonneg_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
le_of_not_gt $ λ ha, (mul_neg_of_neg_of_pos ha hb).not_le h

lemma nonneg_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
le_of_not_gt $ λ hb, (mul_neg_of_pos_of_neg ha hb).not_le h

lemma neg_of_mul_neg_left (h : a * b < 0) (hb : 0 ≤ b) : a < 0 :=
lt_of_not_ge $ λ ha, (mul_nonneg ha hb).not_lt h

lemma neg_of_mul_neg_right (h : a * b < 0) (ha : 0 ≤ a) : b < 0 :=
lt_of_not_ge $ λ hb, (mul_nonneg ha hb).not_lt h

lemma nonpos_of_mul_nonpos_left (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
le_of_not_gt (assume ha : a > 0, (mul_pos ha hb).not_le h)

lemma nonpos_of_mul_nonpos_right (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
le_of_not_gt (assume hb : b > 0, (mul_pos ha hb).not_le h)

@[simp] lemma zero_le_mul_left (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b :=
by { convert mul_le_mul_left h, simp }

@[simp] lemma zero_le_mul_right (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b :=
by { convert mul_le_mul_right h, simp }

lemma add_le_mul_of_left_le_right (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b :=
have 0 < b, from
calc 0 < 2 : zero_lt_two
   ... ≤ a : a2
   ... ≤ b : ab,
calc a + b ≤ b + b : add_le_add_right ab b
       ... = 2 * b : (two_mul b).symm
       ... ≤ a * b : (mul_le_mul_right this).mpr a2

lemma add_le_mul_of_right_le_left (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b :=
have 0 < a, from
calc 0 < 2 : zero_lt_two
   ... ≤ b : b2
   ... ≤ a : ba,
calc a + b ≤ a + a : add_le_add_left ba a
       ... = a * 2 : (mul_two a).symm
       ... ≤ a * b : (mul_le_mul_left this).mpr b2

lemma add_le_mul (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab
               else add_le_mul_of_right_le_left b2 (le_of_not_le hab)

lemma add_le_mul' (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a :=
(le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

section

@[simp] lemma bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_lt_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b :=
(add_le_add_iff_right 1).trans bit0_le_bit0

@[simp] lemma bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b :=
(add_lt_add_iff_right 1).trans bit0_lt_bit0

@[simp] lemma one_le_bit1 : (1 : α) ≤ bit1 a ↔ 0 ≤ a :=
by rw [bit1, le_add_iff_nonneg_left, bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma one_lt_bit1 : (1 : α) < bit1 a ↔ 0 < a :=
by rw [bit1, lt_add_iff_pos_left, bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma zero_le_bit0 : (0 : α) ≤ bit0 a ↔ 0 ≤ a :=
by rw [bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma zero_lt_bit0 : (0 : α) < bit0 a ↔ 0 < a :=
by rw [bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2:α))]

end

theorem mul_nonneg_iff_right_nonneg_of_pos (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b :=
⟨λ h, nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩

theorem mul_nonneg_iff_left_nonneg_of_pos (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a :=
⟨λ h, nonneg_of_mul_nonneg_left h hb, λ h, mul_nonneg h hb.le⟩

lemma nonpos_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
le_of_not_gt (λ ha, absurd h (mul_neg_of_pos_of_neg ha hb).not_le)

lemma nonpos_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
le_of_not_gt (λ hb, absurd h (mul_neg_of_neg_of_pos ha hb).not_le)

@[simp] lemma units.inv_pos {u : αˣ} : (0 : α) < ↑u⁻¹ ↔ (0 : α) < u :=
have ∀ {u : αˣ}, (0 : α) < u → (0 : α) < ↑u⁻¹ := λ u h,
  (zero_lt_mul_left h).mp $ u.mul_inv.symm ▸ zero_lt_one,
⟨this, this⟩

@[simp] lemma units.inv_neg {u : αˣ} : ↑u⁻¹ < (0 : α) ↔ ↑u < (0 : α) :=
have ∀ {u : αˣ}, ↑u < (0 : α) → ↑u⁻¹ < (0 : α) := λ u h,
  neg_of_mul_pos_right (by exact (u.mul_inv.symm ▸ zero_lt_one)) h.le,
⟨this, this⟩

lemma cmp_mul_pos_left (ha : 0 < a) (b c : α) : cmp (a * b) (a * c) = cmp b c :=
(strict_mono_mul_left_of_pos ha).cmp_map_eq b c

lemma cmp_mul_pos_right (ha : 0 < a) (b c : α) : cmp (b * a) (c * a) = cmp b c :=
(strict_mono_mul_right_of_pos ha).cmp_map_eq b c

lemma mul_max_of_nonneg (b c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_max

lemma mul_min_of_nonneg (b c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_min

lemma max_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_max

lemma min_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_min

lemma le_of_mul_le_of_one_le {a b c : α} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
le_of_mul_le_mul_right (h.trans $ le_mul_of_one_le_right hb hc) $ zero_lt_one.trans_le hc

lemma nonneg_le_nonneg_of_sq_le_sq {a b : α} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
le_of_not_gt $ λ hab, (mul_self_lt_mul_self hb hab).not_le h

lemma mul_self_le_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

lemma mul_self_lt_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
((@strict_mono_on_mul_self α _).lt_iff_lt h1 h2).symm

lemma mul_self_inj {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
(@strict_mono_on_mul_self α _).eq_iff_eq h1 h2

end linear_ordered_semiring

@[priority 100] -- See note [lower instance priority]
instance linear_ordered_comm_semiring.to_linear_ordered_cancel_add_comm_monoid
  [linear_ordered_comm_semiring α] : linear_ordered_cancel_add_comm_monoid α :=
{ ..‹linear_ordered_comm_semiring α› }

section linear_ordered_ring
variables [linear_ordered_ring α] {a b c : α}

local attribute [instance] linear_ordered_ring.decidable_le linear_ordered_ring.decidable_lt

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_linear_ordered_semiring : linear_ordered_semiring α :=
{ ..‹linear_ordered_ring α›, ..strict_ordered_ring.to_strict_ordered_semiring }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_linear_ordered_add_comm_group : linear_ordered_add_comm_group α :=
{ ..‹linear_ordered_ring α› }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.no_zero_divisors : no_zero_divisors α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
      intros a b hab,
      refine decidable.or_iff_not_and_not.2 (λ h, _), revert hab,
      cases lt_or_gt_of_ne h.1 with ha ha; cases lt_or_gt_of_ne h.2 with hb hb,
      exacts [(mul_pos_of_neg_of_neg ha hb).ne.symm, (mul_neg_of_neg_of_pos ha hb).ne,
        (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne.symm]
    end,
  .. ‹linear_ordered_ring α› }

@[priority 100] -- see Note [lower instance priority]
--We don't want to import `algebra.ring.basic`, so we cannot use `no_zero_divisors.to_is_domain`.
instance linear_ordered_ring.is_domain : is_domain α :=
{ mul_left_cancel_of_ne_zero := λ a b c ha h,
  begin
    rw [← sub_eq_zero, ← mul_sub] at h,
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  end,
  mul_right_cancel_of_ne_zero := λ a b c hb h,
  begin
    rw [← sub_eq_zero, ← sub_mul] at h,
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb)
  end,
  .. (infer_instance : nontrivial α) }

lemma mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
⟨pos_and_pos_or_neg_and_neg_of_mul_pos,
  λ h, h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

lemma mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b :=
by rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff, neg_pos, neg_lt_zero]

lemma mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg,
  λ h, h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

/-- Out of three elements of a `linear_ordered_ring`, two must have the same sign. -/
lemma mul_nonneg_of_three (a b c : α) :
  0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a :=
by iterate 3 { rw mul_nonneg_iff };
  have := le_total 0 a; have := le_total 0 b; have := le_total 0 c; itauto

lemma mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b :=
by rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff, neg_nonneg, neg_nonpos]

lemma mul_self_nonneg (a : α) : 0 ≤ a * a :=
(le_total 0 a).elim (λ h, mul_nonneg h h) (λ h, mul_nonneg_of_nonpos_of_nonpos h h)

@[simp] lemma neg_le_self_iff : -a ≤ a ↔ 0 ≤ a :=
by simp [neg_le_iff_add_nonneg, ← two_mul, mul_nonneg_iff, zero_le_one, (zero_lt_two' α).not_le]

@[simp] lemma neg_lt_self_iff : -a < a ↔ 0 < a :=
by simp [neg_lt_iff_pos_add, ← two_mul, mul_pos_iff, zero_lt_one, (zero_lt_two' α).not_lt]

@[simp] lemma le_neg_self_iff : a ≤ -a ↔ a ≤ 0 :=
calc a ≤ -a ↔ -(-a) ≤ -a : by rw neg_neg
... ↔ 0 ≤ -a : neg_le_self_iff
... ↔ a ≤ 0 : neg_nonneg

@[simp] lemma lt_neg_self_iff : a < -a ↔ a < 0 :=
calc a < -a ↔ -(-a) < -a : by rw neg_neg
... ↔ 0 < -a : neg_lt_self_iff
... ↔ a < 0 : neg_pos

lemma neg_one_lt_zero : -1 < (0:α) := neg_lt_zero.2 zero_lt_one

@[simp] lemma mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
(strict_anti_mul_left h).le_iff_le

@[simp] lemma mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
(strict_anti_mul_right h).le_iff_le

@[simp] lemma mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
(strict_anti_mul_left h).lt_iff_lt

@[simp] lemma mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
(strict_anti_mul_right h).lt_iff_lt

lemma lt_of_mul_lt_mul_of_nonpos_left (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
lt_of_mul_lt_mul_left (by rwa [neg_mul, neg_mul, neg_lt_neg_iff]) $ neg_nonneg.2 hc

lemma lt_of_mul_lt_mul_of_nonpos_right (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
lt_of_mul_lt_mul_right (by rwa [mul_neg, mul_neg, neg_lt_neg_iff]) $ neg_nonneg.2 hc

lemma cmp_mul_neg_left {a : α} (ha : a < 0) (b c : α) : cmp (a * b) (a * c) = cmp c b :=
(strict_anti_mul_left ha).cmp_map_eq b c

lemma cmp_mul_neg_right {a : α} (ha : a < 0) (b c : α) : cmp (b * a) (c * a) = cmp c b :=
(strict_anti_mul_right ha).cmp_map_eq b c

lemma sub_one_lt (a : α) : a - 1 < a :=
sub_lt_iff_lt_add.2 (lt_add_one a)

@[simp] lemma mul_self_pos {a : α} : 0 < a * a ↔ a ≠ 0 :=
begin
  split,
  { rintro h rfl, rw mul_zero at h, exact h.false },
  { intro h,
    cases h.lt_or_lt with h h,
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h] }
end

lemma mul_self_le_mul_self_of_le_of_neg_le {x y : α} (h₁ : x ≤ y) (h₂ : -x ≤ y) : x * x ≤ y * y :=
(le_total 0 x).elim (λ h, mul_le_mul h₁ h₁ h (h.trans h₁))
  (λ h, le_of_eq_of_le (neg_mul_neg x x).symm
    (mul_le_mul h₂ h₂ (neg_nonneg.mpr h) ((neg_nonneg.mpr h).trans h₂)))

lemma nonneg_of_mul_nonpos_left {a b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
le_of_not_gt (λ ha, absurd h (mul_pos_of_neg_of_neg ha hb).not_le)

lemma nonneg_of_mul_nonpos_right {a b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
le_of_not_gt (λ hb, absurd h (mul_pos_of_neg_of_neg ha hb).not_le)

lemma pos_of_mul_neg_left {a b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
lt_of_not_ge (λ ha, absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt)

lemma pos_of_mul_neg_right {a b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
lt_of_not_ge (λ hb, absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt)

lemma neg_iff_pos_of_mul_neg (hab : a * b < 0) : a < 0 ↔ 0 < b :=
⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩

lemma pos_iff_neg_of_mul_neg (hab : a * b < 0) : 0 < a ↔ b < 0 :=
⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

/-- The sum of two squares is zero iff both elements are zero. -/
lemma mul_self_add_mul_self_eq_zero {x y : α} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
by rw [add_eq_zero_iff', mul_self_eq_zero, mul_self_eq_zero]; apply mul_self_nonneg

lemma eq_zero_of_mul_self_add_mul_self_eq_zero (h : a * a + b * b = 0) : a = 0 :=
(mul_self_add_mul_self_eq_zero.mp h).left

end linear_ordered_ring

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_ring.to_strict_ordered_comm_ring [d : linear_ordered_comm_ring α] :
  strict_ordered_comm_ring α :=
{ ..d }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_ring.to_linear_ordered_comm_semiring [d : linear_ordered_comm_ring α] :
   linear_ordered_comm_semiring α :=
{ .. d, ..linear_ordered_ring.to_linear_ordered_semiring }

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring α] {a b c d : α}

lemma max_mul_mul_le_max_mul_max (b c : α) (ha : 0 ≤ a) (hd: 0 ≤ d) :
  max (a * b) (d * c) ≤ max a c * max d b :=
have ba : b * a ≤ max d b * max c a, from
  mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b)),
have cd : c * d ≤ max a c * max b d, from
  mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c)),
max_le
  (by simpa [mul_comm, max_comm] using ba)
  (by simpa [mul_comm, max_comm] using cd)

end linear_ordered_comm_ring
