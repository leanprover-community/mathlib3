/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.group.defs
/-!

# Typeclasses for modeling the interactions between an order relation and a binary operation

This file begins the splitting of the ordering assumptions from the algebraic assumptions on the
operations in the `ordered_[...]` hierarchy.

The strategy is to introduce separately the two most common interactions between order relations
and binary operations.  These model the implications

* `b ≤ c → a * b ≤ a * c`, (left-multiplication is monotone),
* `a * b < a * c → b < c`, (a kind of contrapositive version of monotonicity of multiplication).

Since we want to have the freedom to apply them independently to

* each relation `(≤)` and `(<)`,
* each binary operation `(+)` and `(*)`,
* left or right actions,

we generalize the setup as follows.

Start with two Types `M` and `N`, an "action" `μ : M → N → N` and a relation `r : N → N → Prop`.
We introduce the two separate definitions

* covariant:     `∀ (m : M) {n₁ n₂ : N}, r n₁ n₂ → r (μ m n₁) (μ m n₂)`,
* contravariant: `∀ (m : M) {n₁ n₂ : N}, r (μ m n₁) (μ m n₂) → r n₁ n₂`,

modeled on the monotonicity conditions above.

We then introduce the 16 typeclasses obtained by choosing `M = N` and assuming

* one of `covariant` and `contravariant`, with
* the relation `r` being one of `(≤)` or `(<)`,
* the operation `μ : M → M → M` being one of `(+)` or `(*)`, for left monotonicity,
* the operation `μ : M → M → M` being one of `(flip (+))` or `(flip(*))`,
  for right monotonicity.

There are two main reasons for introducing several typeclasses.  The first, is that it is much more
human-friendly to have a class called `has_add_le_add_right M` than one called
`covariant (flip (+)) (≤)`.  The second, is that this way, we bound better the space
for typeclass inference: e.g. we ask the typeclass search to look for `has_add` and `has_le`
instances, instead of extending the search to all possible functions among different Types.

The general approach is to formulate and prove a lemma, with the `ordered_[...]` typeclass of your
liking.  After that, you convert the single typeclass, say `[ordered_cancel_monoid M]`, with three
typeclasses, e.g. `[partial_order M] [left_cancel_semigroup M] [has_mul_le_mul_right M]` and see
if the proof still works: chances are that it might!

It is possible (and even expected) to combine several `co(ntra)variant` assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[has_mul_le_mul_left M] [has_lt_of_mul_le_mul_left M]` on top of order/algebraic assumptions.

A formal remark is that normally the relation that is an input to `covariant` is `(≤)`,
while the relation that is an input to `contravariant` is `(<)`. This need not be the case in
general, but seems to be the most common usage. In the opposite direction, the implication

```lean
[semigroup M] [partial_order M] [has_le_of_mul_le_mul M] → left_cancel_semigroup M
```
holds (note the `has_le_[...]` as opposed to the more common idioms `has_lt_[...]` and
`has_mul_le_[...]`.
-/
-- use ⇒, as per Eric's suggestion?
section covariants_and_contravariants

variables {M N : Type*} (μ : M → N → N) (r : N → N → Prop) (m : M) {a b c : N}

/--  Let `M` and `N` be Types, with an action `μ : M → N → N` and a relation `r N → N → Prop`
 on `N`.

Informally, `covariant μ r` says that "the action `μ` preserves the relation `r`".

More precisely, `covariant μ r` asserts that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the
relation `r` holds for the pair `(n₁, n₂)`, then the relation `r` also holds for the pair
`(μ m n₁, μ m n₂)`, obtained from `(n₁, n₂)` by "acting upon it by `m`". -/
def covariant     : Prop := ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/--  Let `M` and `N` be Types, with an action `μ : M → N → N` and a relation `r N → N → Prop`
 on `N`.

Informally, `contravariant μ r` says that "the action `μ` preserves the relation `r`".

More precisely, `contravariant μ r` asserts that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`,
if the relation `r` holds for the pair `(μ m n₁, μ m n₂)`, obtained from `(n₁, n₂)` by
"acting upon it by `m`", then the relation `r` also holds for the pair `(n₁, n₂)`. -/
def contravariant : Prop := ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

variables {M N}

@[simp]
lemma covariant_def :
  covariant μ r ↔ ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂) :=
iff.rfl

@[simp]
lemma contravariant_def :
  contravariant μ r ↔ ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂ :=
iff.rfl

lemma covariant_le_iff_contravariant_lt [linear_order N] :
  covariant μ (≤) ↔ contravariant μ (<) :=
⟨ λ h a b c bc, not_le.mp (λ k, not_le.mpr bc (h _ k)),
  λ h a b c bc, not_lt.mp (λ k, not_lt.mpr bc (h _ k))⟩

lemma covariant_lt_iff_contravariant_le [linear_order N] :
  covariant μ (<) ↔ contravariant μ (≤) :=
⟨ λ h a b c bc, not_lt.mp (λ k, not_lt.mpr bc (h _ k)),
  λ h a b c bc, not_le.mp (λ k, not_le.mpr bc (h _ k))⟩

lemma is_symm_op.swap_eq {α β} (op) [is_symm_op α β op] : flip op = op :=
funext $ λ a, funext $ λ b, (is_symm_op.symm_op a b).symm

@[to_additive]
lemma covariant_iff_covariant_mul [comm_semigroup N] :
  covariant ((*) : N → N → N) (r) ↔ covariant (flip (*) : N → N → N) (r) :=
by rw is_symm_op.swap_eq

@[to_additive]
lemma contravariant_iff_contravariant_mul [comm_semigroup N] :
  contravariant ((*) : N → N → N) (r) ↔ contravariant (flip (*) : N → N → N) (r) :=
by rw is_symm_op.swap_eq

end covariants_and_contravariants

section typeclasses_relating_orders_and_binary_operations
/-!
Typeclasses relating orders and binary operations

These typeclasses are of two kinds:

*  `has_mul_le_mul_left`, asserting `b ≤ c → a * b ≤ a * c`,
*  `has_lt_of_mul_lt_mul_left`, asserting `b < c → a * b < a * c`.

The binary operation (`(*)` or `(+)`), the side of multiplication (left or right), the partial
order (`(≤)` or `(<)`) are free to vary in all ways.
-/
variable (α : Type*)

/--  A typeclass assuming the implication `b ≤ c → a + b ≤ a + c`:
left-addition is monotone. -/
class has_add_le_add_left [has_add α] [has_le α] : Prop :=
(add_le_add_left : covariant ((+) : α → α → α) (≤))

/--  A typeclass assuming the implication `b ≤ c → a * b ≤ a * c`:
left-multiplication is monotone. -/
@[to_additive]
class has_mul_le_mul_left [has_mul α] [has_le α] : Prop :=
(mul_le_mul_left : covariant ((*) : α → α → α) (≤))

/--  A typeclass assuming the implication `b ≤ c → b + a ≤ c + a`:
right-addition is monotone. -/
class has_add_le_add_right [has_add α] [has_le α] : Prop :=
(add_le_add_right : covariant (flip (+) : α → α → α) (≤))

/--  A typeclass assuming the implication `b ≤ c → b * a ≤ c * a`:
right-multiplication is monotone. -/
@[to_additive]
class has_mul_le_mul_right [has_mul α] [has_le α] : Prop :=
(mul_le_mul_right : covariant (flip (*) : α → α → α) (≤))

/--  A typeclass assuming the implication `b < c → a + b < a + c`:
left-addition is strictly monotone. -/
class has_add_lt_add_left [has_add α] [has_lt α] : Prop :=
(add_lt_add_left : covariant ((+) : α → α → α) (<))

/--  A typeclass assuming the implication `b < c → a * b < a * c`:
left-multiplication is strictly monotone. -/
@[to_additive]
class has_mul_lt_mul_left [has_mul α] [has_lt α] : Prop :=
(mul_lt_mul_left : covariant ((*) : α → α → α) (<))

/--  A typeclass assuming the implication `b < c → b + a < c + a`:
right-addition is strictly monotone. -/
class has_add_lt_add_right [has_add α] [has_lt α] : Prop :=
(add_lt_add_right : covariant (flip (+) : α → α → α) (<))

/--  A typeclass assuming the implication `b < c → b * a < c * a`:
right-multiplication is strictly monotone. -/
@[to_additive]
class has_mul_lt_mul_right [has_mul α] [has_lt α] : Prop :=
(mul_lt_mul_right : covariant (flip (*) : α → α → α) (<))

/--  A typeclass assuming the implication `a + b ≤ a + c → b ≤ c`:
left-addition is "reverse" monotone. -/
class has_le_of_add_le_add_left [has_add α] [has_le α] : Prop :=
(le_of_add_le_add_left : contravariant ((+) : α → α → α) (≤))

/--  A typeclass assuming the implication `a * b ≤ a * c → b ≤ c`:
left-multiplication is "reverse" monotone. -/
@[to_additive]
class has_le_of_mul_le_mul_left [has_mul α] [has_le α] : Prop :=
(le_of_mul_le_mul_left : contravariant ((*) : α → α → α) (≤))

/--  A typeclass assuming the implication `b + a ≤ c + a → b ≤ c`:
right-addition is "reverse" monotone. -/
class has_le_of_add_le_add_right [has_add α] [has_le α] : Prop :=
(le_of_add_le_add_right : contravariant (flip (+) : α → α → α) (≤))

/--  A typeclass assuming the implication `b * a ≤ c * a → b ≤ c`:
right-multiplication is "reverse" monotone. -/
@[to_additive]
class has_le_of_mul_le_mul_right [has_mul α] [has_le α] : Prop :=
(le_of_mul_le_mul_right : contravariant (flip (*) : α → α → α) (≤))

/--  A typeclass assuming the implication `a + b < a + c → b < c`:
left-addition is "reverse" strictly monotone. -/
class has_lt_of_add_lt_add_left [has_add α] [has_lt α] : Prop :=
(lt_of_add_lt_add_left : contravariant ((+) : α → α → α) (<))

/--  A typeclass assuming the implication `a * b < a * c → b < c`:
left-multiplication is "reverse" strictly monotone. -/
@[to_additive]
class has_lt_of_mul_lt_mul_left [has_mul α] [has_lt α] : Prop :=
(lt_of_mul_lt_mul_left : contravariant ((*) : α → α → α) (<))

/--  A typeclass assuming the implication `b + a < c + a → b < c`:
right-addition is "reverse" strictly monotone. -/
class has_lt_of_add_lt_add_right [has_add α] [has_lt α] : Prop :=
(lt_of_add_lt_add_right : contravariant (flip (+) : α → α → α) (<))

/--  A typeclass assuming the implication `b * a < c * a → b < c`:
right-multiplication is "reverse" strictly monotone. -/
@[to_additive]
class has_lt_of_mul_lt_mul_right [has_mul α] [has_lt α] : Prop :=
(lt_of_mul_lt_mul_right : contravariant (flip (*) : α → α → α) (<))

section le_implies_lt
/-!  In this section, we show that, for a linear order, monotonicity of an operation implies
"reverse" strict monotonicity of the same operation. -/
variable [linear_order α]

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_mul_le_mul_left.to_has_lt_of_mul_lt_mul_left [has_mul α] [has_mul_le_mul_left α] :
  has_lt_of_mul_lt_mul_left α :=
{ lt_of_mul_lt_mul_left :=
    (covariant_le_iff_contravariant_lt _).mp has_mul_le_mul_left.mul_le_mul_left }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_mul_le_mul_right.to_has_lt_of_mul_lt_mul_right [has_mul α] [has_mul_le_mul_right α] :
  has_lt_of_mul_lt_mul_right α :=
{ lt_of_mul_lt_mul_right :=
    (covariant_le_iff_contravariant_lt _).mp has_mul_le_mul_right.mul_le_mul_right }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_le_of_mul_le_mul_left.to_has_mul_lt_mul_left [has_mul α]
  [has_le_of_mul_le_mul_left α] :
  has_mul_lt_mul_left α :=
{ mul_lt_mul_left :=
    (covariant_lt_iff_contravariant_le _).mpr has_le_of_mul_le_mul_left.le_of_mul_le_mul_left }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_le_of_mul_le_mul_right.to_has_mul_lt_mul_right [has_mul α]
  [has_le_of_mul_le_mul_right α] :
  has_mul_lt_mul_right α :=
{ mul_lt_mul_right :=
    (covariant_lt_iff_contravariant_le _).mpr has_le_of_mul_le_mul_right.le_of_mul_le_mul_right }

end le_implies_lt

section left_implies_right
/-!  In this section, we show that, for a commutative operation, left monotonicity assumptions
imply the corresponding right monotonicity. -/
variable [comm_semigroup α]

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_mul_le_mul_left.to_mul_le_mul_right [has_le α] [has_mul_le_mul_left α] :
  has_mul_le_mul_right α :=
{ mul_le_mul_right := (covariant_iff_covariant_mul (≤)).mp has_mul_le_mul_left.mul_le_mul_left }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_le_of_mul_le_mul_left.to_has_le_of_mul_le_mul_right [has_le α]
  [has_le_of_mul_le_mul_left α] :
  has_le_of_mul_le_mul_right α :=
{ le_of_mul_le_mul_right :=
    (contravariant_iff_contravariant_mul (≤)).mp has_le_of_mul_le_mul_left.le_of_mul_le_mul_left }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_mul_lt_mul_left.to_mul_lt_mul_right [has_lt α] [has_mul_lt_mul_left α] :
  has_mul_lt_mul_right α :=
{ mul_lt_mul_right := (covariant_iff_covariant_mul (<)).mp has_mul_lt_mul_left.mul_lt_mul_left }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance has_lt_of_mul_lt_mul_left.to_has_lt_of_mul_lt_mul_right [has_lt α]
  [has_lt_of_mul_lt_mul_left α] :
  has_lt_of_mul_lt_mul_right α :=
{ lt_of_mul_lt_mul_right :=
    (contravariant_iff_contravariant_mul (<)).mp has_lt_of_mul_lt_mul_left.lt_of_mul_lt_mul_left }

end left_implies_right

@[to_additive]
def contravariant.to_left_cancel_semigroup [semigroup α] [partial_order α]
  [has_le_of_mul_le_mul_left α] :
  left_cancel_semigroup α :=
{ mul_left_cancel := λ a b c bc, (has_le_of_mul_le_mul_left.le_of_mul_le_mul_left _ bc.le).antisymm
    (has_le_of_mul_le_mul_left.le_of_mul_le_mul_left _ bc.ge),
  ..(infer_instance : semigroup α) }

@[to_additive]
def contravariant.to_right_cancel_semigroup [semigroup α] [partial_order α]
  [has_le_of_mul_le_mul_right α] :
  right_cancel_semigroup α :=
{ mul_right_cancel := λ a b c bc,
le_antisymm (has_le_of_mul_le_mul_right.le_of_mul_le_mul_right b bc.le)
    (has_le_of_mul_le_mul_right.le_of_mul_le_mul_right b bc.ge)
  ..(infer_instance : semigroup α) }


end typeclasses_relating_orders_and_binary_operations
