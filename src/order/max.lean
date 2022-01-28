/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudriashov
-/
import order.order_dual

/-!
# Minimal/maximal and bottom/top elements

This file defines predicates for elements to be bottom/top and typeclasses saying that there are no
minimal/maximal elements.

## Predicates

* `is_bot`: An element is *bottom* if all elements are greater than it.
* `is_top`: An element is *top* if all elements are less than it.

## Typeclasses

* `no_min_order`: An order without minimal elements.
* `no_max_order`: An order without maximal elements.
-/

open order_dual

variables {α : Type*}

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class no_min_order (α : Type*) [has_lt α] : Prop :=
(exists_lt (a : α) : ∃ b, b < a)

/-- Order without maximal elements. Sometimes called cofinal. -/
class no_max_order (α : Type*) [has_lt α] : Prop :=
(exists_gt (a : α) : ∃ b, a < b)

export no_min_order (exists_lt)
export no_max_order (exists_gt)

instance nonempty_lt [has_lt α] [no_min_order α] (a : α) : nonempty {x // x < a} :=
nonempty_subtype.2 (exists_lt a)

instance nonempty_gt [has_lt α] [no_max_order α] (a : α) : nonempty {x // a < x} :=
nonempty_subtype.2 (exists_gt a)

instance order_dual.no_min_order (α : Type*) [has_lt α] [no_max_order α] :
  no_min_order (order_dual α) :=
⟨λ a, @exists_gt α _ _ a⟩

instance order_dual.no_max_order (α : Type*) [has_lt α] [no_min_order α] :
  no_max_order (order_dual α) :=
⟨λ a, @exists_lt α _ _ a⟩

section has_le
variables [has_le α] {a : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`no_min_order α` within a proof. -/
def is_bot (a : α) : Prop := ∀ b, a ≤ b

/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`no_max_order α` within a proof. -/
def is_top (a : α) : Prop := ∀ b, b ≤ a

lemma is_top.to_dual (h : is_top a) : is_bot (to_dual a) := h
lemma is_bot.to_dual (h : is_bot a) : is_top (to_dual a) := h

end has_le

section preorder
variables [preorder α] {a b : α}

@[simp] lemma not_is_bot [no_min_order α] (a : α) : ¬is_bot a :=
λ h, let ⟨b, hb⟩ := exists_lt a in hb.not_le $ h b

@[simp] lemma not_is_top [no_max_order α] (a : α) : ¬is_top a :=
λ h, let ⟨b, hb⟩ := exists_gt a in hb.not_le $ h b

end preorder

section partial_order
variables [partial_order α] {a b : α}

lemma is_bot.unique (ha : is_bot a) (hb : b ≤ a) : a = b := (ha b).antisymm hb
lemma is_top.unique (ha : is_top a) (hb : a ≤ b) : a = b := le_antisymm hb (ha b)

end partial_order

section linear_order
variables [linear_order α]

lemma is_top_or_exists_gt (a : α) : is_top a ∨ ∃ b, a < b :=
by simpa only [or_iff_not_imp_left, is_top, not_forall, not_le] using id

lemma is_bot_or_exists_lt (a : α) : is_bot a ∨ ∃ b, b < a := @is_top_or_exists_gt (order_dual α) _ a

end linear_order
