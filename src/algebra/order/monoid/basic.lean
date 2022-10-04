/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one
import algebra.group.prod
import algebra.hom.equiv
import algebra.order.monoid.lemmas
import order.min_max
import order.hom.basic

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

set_option old_structure_cmd true
open function

universe u
variables {α : Type u} {β : Type*}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
@[protect_proj, ancestor comm_monoid partial_order]
class ordered_comm_monoid (α : Type*) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
@[protect_proj, ancestor add_comm_monoid partial_order]
class ordered_add_comm_monoid (α : Type*) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

attribute [to_additive] ordered_comm_monoid

section ordered_instances

@[to_additive]
instance ordered_comm_monoid.to_covariant_class_left (M : Type*) [ordered_comm_monoid M] :
  covariant_class M M (*) (≤) :=
{ elim := λ a b c bc, ordered_comm_monoid.mul_le_mul_left _ _ bc a }

/- This instance can be proven with `by apply_instance`.  However, `with_bot ℕ` does not
pick up a `covariant_class M M (function.swap (*)) (≤)` instance without it (see PR #7940). -/
@[to_additive]
instance ordered_comm_monoid.to_covariant_class_right (M : Type*) [ordered_comm_monoid M] :
  covariant_class M M (swap (*)) (≤) :=
covariant_swap_mul_le_of_covariant_mul_le M

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`left_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (*) (≤)` implies
`covariant_class M M (*) (<)`, see `left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le`. -/
@[to_additive] lemma has_mul.to_covariant_class_left
  (M : Type*) [has_mul M] [partial_order M] [covariant_class M M (*) (<)] :
  covariant_class M M (*) (≤) :=
⟨covariant_le_of_covariant_lt _ _ _ covariant_class.elim⟩

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`right_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (swap (*)) (<)`
implies `covariant_class M M (swap (*)) (≤)`, see
`right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le`. -/
@[to_additive] lemma has_mul.to_covariant_class_right
  (M : Type*) [has_mul M] [partial_order M] [covariant_class M M (swap (*)) (<)] :
  covariant_class M M (swap (*)) (≤) :=
⟨covariant_le_of_covariant_lt _ _ _ covariant_class.elim⟩

end ordered_instances

/-- An `ordered_comm_monoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_monoid`. -/
class has_exists_mul_of_le (α : Type u) [has_mul α] [has_le α] : Prop :=
(exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ (c : α), b = a * c)

/-- An `ordered_add_comm_monoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_add_monoid`. -/
class has_exists_add_of_le (α : Type u) [has_add α] [has_le α] : Prop :=
(exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ (c : α), b = a + c)

attribute [to_additive] has_exists_mul_of_le

export has_exists_mul_of_le (exists_mul_of_le)

export has_exists_add_of_le (exists_add_of_le)

section has_exists_mul_of_le
variables [linear_order α] [densely_ordered α] [monoid α] [has_exists_mul_of_le α]
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)] {a b : α}

@[to_additive]
lemma le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
le_of_forall_le_of_dense $ λ x hxb, by { obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le,
  exact h _ ((lt_mul_iff_one_lt_right' b).1 hxb) }

@[to_additive]
lemma le_of_forall_one_lt_lt_mul' (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
le_of_forall_one_lt_le_mul $ λ ε hε, (h _ hε).le

@[to_additive]
lemma le_iff_forall_one_lt_lt_mul' : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
⟨λ h ε, lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩

end has_exists_mul_of_le

/-- A linearly ordered additive commutative monoid. -/
@[protect_proj, ancestor linear_order ordered_add_comm_monoid]
class linear_ordered_add_comm_monoid (α : Type*)
  extends linear_order α, ordered_add_comm_monoid α.

/-- A linearly ordered commutative monoid. -/
@[protect_proj, ancestor linear_order ordered_comm_monoid, to_additive]
class linear_ordered_comm_monoid (α : Type*)
  extends linear_order α, ordered_comm_monoid α.

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class zero_le_one_class (α : Type*) [has_zero α] [has_one α] [has_le α] :=
(zero_le_one : (0 : α) ≤ 1)

@[simp] lemma zero_le_one [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one_class.zero_le_one

/- `zero_le_one` with an explicit type argument. -/
lemma zero_le_one' (α) [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one

lemma zero_le_two [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 2 :=
add_nonneg zero_le_one zero_le_one

lemma zero_le_three [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 3 :=
add_nonneg zero_le_two zero_le_one

lemma zero_le_four [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 4 :=
add_nonneg zero_le_two zero_le_two

lemma one_le_two [has_le α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (1 : α) ≤ 2 :=
calc 1 = 1 + 0 : (add_zero 1).symm
   ... ≤ 1 + 1 : add_le_add_left zero_le_one _

lemma one_le_two' [has_le α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (swap (+)) (≤)] : (1 : α) ≤ 2 :=
calc 1 = 0 + 1 : (zero_add 1).symm
   ... ≤ 1 + 1 : add_le_add_right zero_le_one _

/-- A linearly ordered commutative monoid with a zero element. -/
class linear_ordered_comm_monoid_with_zero (α : Type*)
  extends linear_ordered_comm_monoid α, comm_monoid_with_zero α :=
(zero_le_one : (0 : α) ≤ 1)

@[priority 100]
instance linear_ordered_comm_monoid_with_zero.zero_le_one_class
  [h : linear_ordered_comm_monoid_with_zero α] : zero_le_one_class α :=
{ ..h }

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor linear_ordered_add_comm_monoid has_top]
class linear_ordered_add_comm_monoid_with_top (α : Type*)
  extends linear_ordered_add_comm_monoid α, has_top α :=
(le_top : ∀ x : α, x ≤ ⊤)
(top_add' : ∀ x : α, ⊤ + x = ⊤)

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_add_comm_monoid_with_top.to_order_top (α : Type u)
  [h : linear_ordered_add_comm_monoid_with_top α] : order_top α :=
{ ..h }

section linear_ordered_add_comm_monoid_with_top
variables [linear_ordered_add_comm_monoid_with_top α] {a b : α}

@[simp]
lemma top_add (a : α) : ⊤ + a = ⊤ := linear_ordered_add_comm_monoid_with_top.top_add' a

@[simp]
lemma add_top (a : α) : a + ⊤ = ⊤ :=
trans (add_comm _ _) (top_add _)

end linear_ordered_add_comm_monoid_with_top

/-- Pullback an `ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.ordered_comm_monoid [ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β] [has_pow β ℕ]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  ordered_comm_monoid β :=
{ mul_le_mul_left := λ a b ab c, show f (c * a) ≤ f (c * b), by
  { rw [mul, mul], apply mul_le_mul_left', exact ab },
  ..partial_order.lift f hf,
  ..hf.comm_monoid f one mul npow }

/-- Pullback a `linear_ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.linear_ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.linear_ordered_comm_monoid [linear_ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β] [has_pow β ℕ] [has_sup β] [has_inf β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_comm_monoid β :=
{ .. hf.ordered_comm_monoid f one mul npow,
  .. linear_order.lift f hf hsup hinf }

lemma bit0_pos [ordered_add_comm_monoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
add_pos' h h

namespace units

@[to_additive]
instance [monoid α] [preorder α] : preorder αˣ :=
preorder.lift (coe : αˣ → α)

@[simp, norm_cast, to_additive]
theorem coe_le_coe [monoid α] [preorder α] {a b : αˣ} :
  (a : α) ≤ b ↔ a ≤ b := iff.rfl

@[simp, norm_cast, to_additive]
theorem coe_lt_coe [monoid α] [preorder α] {a b : αˣ} :
  (a : α) < b ↔ a < b := iff.rfl

@[to_additive]
instance [monoid α] [partial_order α] : partial_order αˣ :=
partial_order.lift coe units.ext

@[to_additive]
instance [monoid α] [linear_order α] : linear_order αˣ :=
linear_order.lift' coe units.ext

/-- `coe : αˣ → α` as an order embedding. -/
@[to_additive "`coe : add_units α → α` as an order embedding.", simps { fully_applied := ff }]
def order_embedding_coe [monoid α] [linear_order α] : αˣ ↪o α := ⟨⟨coe, ext⟩, λ _ _, iff.rfl⟩

@[simp, norm_cast, to_additive]
theorem max_coe [monoid α] [linear_order α] {a b : αˣ} :
  (↑(max a b) : α) = max a b :=
monotone.map_max order_embedding_coe.monotone

@[simp, norm_cast, to_additive]
theorem min_coe [monoid α] [linear_order α] {a b : αˣ} :
  (↑(min a b) : α) = min a b :=
monotone.map_min order_embedding_coe.monotone

end units

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor add_comm_monoid partial_order]
class ordered_cancel_add_comm_monoid (α : Type u) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor comm_monoid partial_order, to_additive]
class ordered_cancel_comm_monoid (α : Type u) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c)

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c d : α}

@[priority 200, to_additive] -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_contravariant_class_le_left :
  contravariant_class α α (*) (≤) :=
⟨ordered_cancel_comm_monoid.le_of_mul_le_mul_left⟩

@[to_additive]
lemma ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c :=
λ a b c h, lt_of_le_not_le
  (ordered_cancel_comm_monoid.le_of_mul_le_mul_left a b c h.le) $
  mt (λ h, ordered_cancel_comm_monoid.mul_le_mul_left _ _ h _) (not_le_of_gt h)

@[to_additive]
instance ordered_cancel_comm_monoid.to_contravariant_class_left
  (M : Type*) [ordered_cancel_comm_monoid M] :
  contravariant_class M M (*) (<) :=
{ elim := λ a b c, ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left _ _ _ }

/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance ordered_cancel_comm_monoid.to_contravariant_class_right
  (M : Type*) [ordered_cancel_comm_monoid M] :
  contravariant_class M M (swap (*)) (<) :=
contravariant_swap_mul_lt_of_contravariant_mul_lt M

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_ordered_comm_monoid : ordered_comm_monoid α :=
{ ..‹ordered_cancel_comm_monoid α› }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_cancel_comm_monoid : cancel_comm_monoid α :=
{ mul_left_cancel := λ a b c h,
    (le_of_mul_le_mul_left' h.le).antisymm $ le_of_mul_le_mul_left' h.ge,
  ..‹ordered_cancel_comm_monoid α› }

/-- Pullback an `ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_cancel_add_comm_monoid
"Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.ordered_cancel_comm_monoid {β : Type*}
  [has_one β] [has_mul β] [has_pow β ℕ]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  ordered_cancel_comm_monoid β :=
{ le_of_mul_le_mul_left := λ a b c (bc : f (a * b) ≤ f (a * c)),
    (mul_le_mul_iff_left (f a)).mp (by rwa [← mul, ← mul]),
  ..hf.ordered_comm_monoid f one mul npow }

end ordered_cancel_comm_monoid

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/
@[to_additive]
lemma fn_min_mul_fn_max {β} [linear_order α] [comm_semigroup β] (f : α → β) (n m : α) :
  f (min n m) * f (max n m) = f n * f m :=
by { cases le_total n m with h h; simp [h, mul_comm] }

@[to_additive]
lemma min_mul_max [linear_order α] [comm_semigroup α] (n m : α) :
  min n m * max n m = n * m :=
fn_min_mul_fn_max id n m

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_add_comm_monoid linear_ordered_add_comm_monoid]
class linear_ordered_cancel_add_comm_monoid (α : Type u)
  extends ordered_cancel_add_comm_monoid α, linear_ordered_add_comm_monoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_comm_monoid linear_ordered_comm_monoid, to_additive]
class linear_ordered_cancel_comm_monoid (α : Type u)
  extends ordered_cancel_comm_monoid α, linear_ordered_comm_monoid α

section covariant_class_mul_le
variables [linear_order α]

section has_mul
variable [has_mul α]

section left
variable [covariant_class α α (*) (≤)]

@[to_additive] lemma min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
(monotone_id.const_mul' a).map_min.symm

@[to_additive]
lemma max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
(monotone_id.const_mul' a).map_max.symm

@[to_additive]
lemma lt_or_lt_of_mul_lt_mul [covariant_class α α (function.swap (*)) (≤)]
  {a b m n : α} (h : m * n < a * b) :
  m < a ∨ n < b :=
by { contrapose! h, exact mul_le_mul' h.1 h.2 }

@[to_additive]
lemma mul_lt_mul_iff_of_le_of_le
  [covariant_class α α (function.swap (*)) (<)]
  [covariant_class α α (*) (<)]
  [covariant_class α α (function.swap (*)) (≤)]
  {a b c d : α} (ac : a ≤ c) (bd : b ≤ d) :
  a * b < c * d ↔ (a < c) ∨ (b < d) :=
begin
  refine ⟨lt_or_lt_of_mul_lt_mul, λ h, _⟩,
  cases h with ha hb,
  { exact mul_lt_mul_of_lt_of_le ha bd },
  { exact mul_lt_mul_of_le_of_lt ac hb }
end

end left

section right
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
(monotone_id.mul_const' c).map_min.symm

@[to_additive]
lemma max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
(monotone_id.mul_const' c).map_max.symm

end right

end has_mul

variable [mul_one_class α]

@[to_additive]
lemma min_le_mul_of_one_le_right [covariant_class α α (*) (≤)] {a b : α} (hb : 1 ≤ b) :
  min a b ≤ a * b :=
min_le_iff.2 $ or.inl $ le_mul_of_one_le_right' hb

@[to_additive]
lemma min_le_mul_of_one_le_left [covariant_class α α (function.swap (*)) (≤)] {a b : α}
  (ha : 1 ≤ a) : min a b ≤ a * b :=
min_le_iff.2 $ or.inr $ le_mul_of_one_le_left' ha

@[to_additive]
lemma max_le_mul_of_one_le [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  max a b ≤ a * b :=
max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end covariant_class_mul_le

section linear_ordered_cancel_comm_monoid
variables [linear_ordered_cancel_comm_monoid α]

/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.linear_ordered_cancel_add_comm_monoid
"Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.linear_ordered_cancel_comm_monoid {β : Type*}
  [has_one β] [has_mul β] [has_pow β ℕ] [has_sup β] [has_inf β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_cancel_comm_monoid β :=
{ ..hf.linear_ordered_comm_monoid f one mul npow hsup hinf,
  ..hf.ordered_cancel_comm_monoid f one mul npow }

end linear_ordered_cancel_comm_monoid

/-! ### Order dual -/

namespace order_dual

@[to_additive]
instance contravariant_class_mul_le [has_le α] [has_mul α] [c : contravariant_class α α (*) (≤)] :
  contravariant_class αᵒᵈ αᵒᵈ (*) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_le [has_le α] [has_mul α] [c : covariant_class α α (*) (≤)] :
  covariant_class αᵒᵈ αᵒᵈ (*) (≤) :=
⟨c.1.flip⟩

@[to_additive] instance contravariant_class_swap_mul_le [has_le α] [has_mul α]
  [c : contravariant_class α α (swap (*)) (≤)] :
  contravariant_class αᵒᵈ αᵒᵈ (swap (*)) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_le [has_le α] [has_mul α]
  [c : covariant_class α α (swap (*)) (≤)] :
  covariant_class αᵒᵈ αᵒᵈ (swap (*)) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_mul_lt [has_lt α] [has_mul α] [c : contravariant_class α α (*) (<)] :
  contravariant_class αᵒᵈ αᵒᵈ (*) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_lt [has_lt α] [has_mul α] [c : covariant_class α α (*) (<)] :
  covariant_class αᵒᵈ αᵒᵈ (*) (<) :=
⟨c.1.flip⟩

@[to_additive] instance contravariant_class_swap_mul_lt [has_lt α] [has_mul α]
  [c : contravariant_class α α (swap (*)) (<)] :
  contravariant_class αᵒᵈ αᵒᵈ (swap (*)) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_lt [has_lt α] [has_mul α]
  [c : covariant_class α α (swap (*)) (<)] :
  covariant_class αᵒᵈ αᵒᵈ (swap (*)) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance [ordered_comm_monoid α] : ordered_comm_monoid αᵒᵈ :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_left' h c,
  .. order_dual.partial_order α,
  .. order_dual.comm_monoid }

@[to_additive ordered_cancel_add_comm_monoid.to_contravariant_class]
instance ordered_cancel_comm_monoid.to_contravariant_class [ordered_cancel_comm_monoid α] :
  contravariant_class αᵒᵈ αᵒᵈ has_mul.mul has_le.le :=
{ elim := λ a b c, ordered_cancel_comm_monoid.le_of_mul_le_mul_left a c b }

@[to_additive]
instance [ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid αᵒᵈ :=
{ le_of_mul_le_mul_left := λ a b c : α, le_of_mul_le_mul_left',
  .. order_dual.ordered_comm_monoid, .. order_dual.cancel_comm_monoid }

@[to_additive]
instance [linear_ordered_cancel_comm_monoid α] :
  linear_ordered_cancel_comm_monoid αᵒᵈ :=
{ .. order_dual.linear_order α,
  .. order_dual.ordered_cancel_comm_monoid }

@[to_additive]
instance [linear_ordered_comm_monoid α] :
  linear_ordered_comm_monoid αᵒᵈ :=
{ .. order_dual.linear_order α,
  .. order_dual.ordered_comm_monoid }

end order_dual

/-! ### Product -/

namespace prod

variables {M N : Type*}

@[to_additive]
instance [ordered_comm_monoid α] [ordered_comm_monoid β] : ordered_comm_monoid (α × β) :=
{ mul_le_mul_left := λ a b h c, ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩,
  .. prod.comm_monoid, .. prod.partial_order _ _ }

@[to_additive]
instance [ordered_cancel_comm_monoid M] [ordered_cancel_comm_monoid N] :
  ordered_cancel_comm_monoid (M × N) :=
{ le_of_mul_le_mul_left := λ a b c h, ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩,
  .. prod.ordered_comm_monoid }

@[to_additive] instance [has_le α] [has_le β] [has_mul α] [has_mul β] [has_exists_mul_of_le α]
  [has_exists_mul_of_le β] : has_exists_mul_of_le (α × β) :=
⟨λ a b h, let ⟨c, hc⟩ := exists_mul_of_le h.1, ⟨d, hd⟩ := exists_mul_of_le h.2 in
  ⟨(c, d), ext hc hd⟩⟩

end prod

/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `order_iso.mul_left` when working in an ordered group. -/
@[to_additive "The order embedding sending `b` to `a + b`, for some fixed `a`.
  See also `order_iso.add_left` when working in an additive ordered group.", simps]
def order_embedding.mul_left
  {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (*) (<)] (m : α) : α ↪o α :=
order_embedding.of_strict_mono (λ n, m * n) (λ a b w, mul_lt_mul_left' w m)

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `order_iso.mul_right` when working in an ordered group. -/
@[to_additive "The order embedding sending `b` to `b + a`, for some fixed `a`.
  See also `order_iso.add_right` when working in an additive ordered group.", simps]
def order_embedding.mul_right
  {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (swap (*)) (<)] (m : α) :
  α ↪o α :=
order_embedding.of_strict_mono (λ n, n * m) (λ a b w, mul_lt_mul_right' w m)
