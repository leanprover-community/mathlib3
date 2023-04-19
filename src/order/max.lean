/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
import order.synonym

/-!
# Minimal/maximal and bottom/top elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `is_bot`: An element is *bottom* if all elements are greater than it.
* `is_top`: An element is *top* if all elements are less than it.
* `is_min`: An element is *minimal* if no element is strictly less than it.
* `is_max`: An element is *maximal* if no element is strictly greater than it.

See also `is_bot_iff_is_min` and `is_top_iff_is_max` for the equivalences in a (co)directed order.

## Typeclasses

* `no_bot_order`: An order without bottom elements.
* `no_top_order`: An order without top elements.
* `no_min_order`: An order without minimal elements.
* `no_max_order`: An order without maximal elements.
-/

open order_dual

variables {ι α β : Type*} {π : ι → Type*}

/-- Order without bottom elements. -/
class no_bot_order (α : Type*) [has_le α] : Prop :=
(exists_not_ge (a : α) : ∃ b, ¬ a ≤ b)

/-- Order without top elements. -/
class no_top_order (α : Type*) [has_le α] : Prop :=
(exists_not_le (a : α) : ∃ b, ¬ b ≤ a)

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class no_min_order (α : Type*) [has_lt α] : Prop :=
(exists_lt (a : α) : ∃ b, b < a)

/-- Order without maximal elements. Sometimes called cofinal. -/
class no_max_order (α : Type*) [has_lt α] : Prop :=
(exists_gt (a : α) : ∃ b, a < b)

export no_bot_order (exists_not_ge)
export no_top_order (exists_not_le)
export no_min_order (exists_lt)
export no_max_order (exists_gt)

instance nonempty_lt [has_lt α] [no_min_order α] (a : α) : nonempty {x // x < a} :=
nonempty_subtype.2 (exists_lt a)

instance nonempty_gt [has_lt α] [no_max_order α] (a : α) : nonempty {x // a < x} :=
nonempty_subtype.2 (exists_gt a)

instance order_dual.no_bot_order (α : Type*) [has_le α] [no_top_order α] : no_bot_order αᵒᵈ :=
⟨λ a, @exists_not_le α _ _ a⟩

instance order_dual.no_top_order (α : Type*) [has_le α] [no_bot_order α] : no_top_order αᵒᵈ :=
⟨λ a, @exists_not_ge α _ _ a⟩

instance order_dual.no_min_order (α : Type*) [has_lt α] [no_max_order α] : no_min_order αᵒᵈ :=
⟨λ a, @exists_gt α _ _ a⟩

instance order_dual.no_max_order (α : Type*) [has_lt α] [no_min_order α] : no_max_order αᵒᵈ :=
⟨λ a, @exists_lt α _ _ a⟩

instance no_max_order_of_left [preorder α] [preorder β] [no_max_order α] : no_max_order (α × β) :=
⟨λ ⟨a, b⟩, by { obtain ⟨c, h⟩ := exists_gt a, exact ⟨(c, b), prod.mk_lt_mk_iff_left.2 h⟩ }⟩

instance no_max_order_of_right [preorder α] [preorder β] [no_max_order β] : no_max_order (α × β) :=
⟨λ ⟨a, b⟩, by { obtain ⟨c, h⟩ := exists_gt b, exact ⟨(a, c), prod.mk_lt_mk_iff_right.2 h⟩ }⟩

instance no_min_order_of_left [preorder α] [preorder β] [no_min_order α] : no_min_order (α × β) :=
⟨λ ⟨a, b⟩, by { obtain ⟨c, h⟩ := exists_lt a, exact ⟨(c, b), prod.mk_lt_mk_iff_left.2 h⟩ }⟩

instance no_min_order_of_right [preorder α] [preorder β] [no_min_order β] : no_min_order (α × β) :=
⟨λ ⟨a, b⟩, by { obtain ⟨c, h⟩ := exists_lt b, exact ⟨(a, c), prod.mk_lt_mk_iff_right.2 h⟩ }⟩

instance [nonempty ι] [Π i, preorder (π i)] [Π i, no_max_order (π i)] : no_max_order (Π i, π i) :=
⟨λ a, begin
  classical,
  obtain ⟨b, hb⟩ := exists_gt (a $ classical.arbitrary _),
  exact ⟨_, lt_update_self_iff.2 hb⟩,
end⟩

instance [nonempty ι] [Π i, preorder (π i)] [Π i, no_min_order (π i)] : no_min_order (Π i, π i) :=
⟨λ a, begin
  classical,
  obtain ⟨b, hb⟩ := exists_lt (a $ classical.arbitrary _),
  exact ⟨_, update_lt_self_iff.2 hb⟩,
end⟩

@[priority 100] -- See note [lower instance priority]
instance no_min_order.to_no_bot_order (α : Type*) [preorder α] [no_min_order α] : no_bot_order α :=
⟨λ a, (exists_lt a).imp $ λ _, not_le_of_lt⟩

@[priority 100] -- See note [lower instance priority]
instance no_max_order.to_no_top_order (α : Type*) [preorder α] [no_max_order α] : no_top_order α :=
⟨λ a, (exists_gt a).imp $ λ _, not_le_of_lt⟩

lemma no_bot_order.to_no_min_order (α : Type*) [linear_order α] [no_bot_order α] : no_min_order α :=
{ exists_lt := by { convert λ a : α, exists_not_ge a, simp_rw not_le, } }

lemma no_top_order.to_no_max_order (α : Type*) [linear_order α] [no_top_order α] : no_max_order α :=
{ exists_gt := by { convert λ a : α, exists_not_le a, simp_rw not_le, } }

lemma no_bot_order_iff_no_min_order (α : Type*) [linear_order α] :
  no_bot_order α ↔ no_min_order α :=
⟨λ h, by { haveI := h, exact no_bot_order.to_no_min_order α },
  λ h, by { haveI := h, exact no_min_order.to_no_bot_order α }⟩

lemma no_top_order_iff_no_max_order (α : Type*) [linear_order α] :
  no_top_order α ↔ no_max_order α :=
⟨λ h, by { haveI := h, exact no_top_order.to_no_max_order α },
  λ h, by { haveI := h, exact no_max_order.to_no_top_order α }⟩

theorem no_min_order.not_acc [has_lt α] [no_min_order α] (a : α) : ¬ acc (<) a :=
λ h, acc.rec_on h $ λ x _, (exists_lt x).rec_on

theorem no_max_order.not_acc [has_lt α] [no_max_order α] (a : α) : ¬ acc (>) a :=
λ h, acc.rec_on h $ λ x _, (exists_gt x).rec_on

section has_le
variables [has_le α] {a b : α}

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

/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `is_min_iff_forall_not_lt` does the
conversion. -/
def is_min (a : α) : Prop := ∀ ⦃b⦄, b ≤ a → a ≤ b

/-- `a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `is_max_iff_forall_not_lt` does the
conversion. -/
def is_max (a : α) : Prop := ∀ ⦃b⦄, a ≤ b → b ≤ a

@[simp] lemma not_is_bot [no_bot_order α] (a : α) : ¬is_bot a :=
λ h, let ⟨b, hb⟩ := exists_not_ge a in hb $ h _

@[simp] lemma not_is_top [no_top_order α] (a : α) : ¬is_top a :=
λ h, let ⟨b, hb⟩ := exists_not_le a in hb $ h _

protected lemma is_bot.is_min (h : is_bot a) : is_min a := λ b _, h b
protected lemma is_top.is_max (h : is_top a) : is_max a := λ b _, h b

@[simp] lemma is_bot_to_dual_iff : is_bot (to_dual a) ↔ is_top a := iff.rfl
@[simp] lemma is_top_to_dual_iff : is_top (to_dual a) ↔ is_bot a := iff.rfl
@[simp] lemma is_min_to_dual_iff : is_min (to_dual a) ↔ is_max a := iff.rfl
@[simp] lemma is_max_to_dual_iff : is_max (to_dual a) ↔ is_min a := iff.rfl
@[simp] lemma is_bot_of_dual_iff {a : αᵒᵈ} : is_bot (of_dual a) ↔ is_top a := iff.rfl
@[simp] lemma is_top_of_dual_iff {a : αᵒᵈ} : is_top (of_dual a) ↔ is_bot a := iff.rfl
@[simp] lemma is_min_of_dual_iff {a : αᵒᵈ} : is_min (of_dual a) ↔ is_max a := iff.rfl
@[simp] lemma is_max_of_dual_iff {a : αᵒᵈ} : is_max (of_dual a) ↔ is_min a := iff.rfl

alias is_bot_to_dual_iff ↔ _ is_top.to_dual
alias is_top_to_dual_iff ↔ _ is_bot.to_dual
alias is_min_to_dual_iff ↔ _ is_max.to_dual
alias is_max_to_dual_iff ↔ _ is_min.to_dual
alias is_bot_of_dual_iff ↔ _ is_top.of_dual
alias is_top_of_dual_iff ↔ _ is_bot.of_dual
alias is_min_of_dual_iff ↔ _ is_max.of_dual
alias is_max_of_dual_iff ↔ _ is_min.of_dual

end has_le

section preorder
variables [preorder α] {a b : α}

lemma is_bot.mono (ha : is_bot a) (h : b ≤ a) : is_bot b := λ c, h.trans $ ha _
lemma is_top.mono (ha : is_top a) (h : a ≤ b) : is_top b := λ c, (ha _).trans h
lemma is_min.mono (ha : is_min a) (h : b ≤ a) : is_min b := λ c hc, h.trans $ ha $ hc.trans h
lemma is_max.mono (ha : is_max a) (h : a ≤ b) : is_max b := λ c hc, (ha $ h.trans hc).trans h

lemma is_min.not_lt (h : is_min a) : ¬ b < a := λ hb, hb.not_le $ h hb.le
lemma is_max.not_lt (h : is_max a) : ¬ a < b := λ hb, hb.not_le $ h hb.le
@[simp] lemma not_is_min_of_lt (h : b < a) : ¬ is_min a := λ ha, ha.not_lt h
@[simp] lemma not_is_max_of_lt (h : a < b) : ¬ is_max a := λ ha, ha.not_lt h

alias not_is_min_of_lt ← has_lt.lt.not_is_min
alias not_is_max_of_lt ← has_lt.lt.not_is_max

lemma is_min_iff_forall_not_lt : is_min a ↔ ∀ b, ¬ b < a :=
⟨λ h _, h.not_lt, λ h b hba, of_not_not $ λ hab, h _ $ hba.lt_of_not_le hab⟩

lemma is_max_iff_forall_not_lt : is_max a ↔ ∀ b, ¬ a < b :=
⟨λ h _, h.not_lt, λ h b hba, of_not_not $ λ hab, h _ $ hba.lt_of_not_le hab⟩

@[simp] lemma not_is_min_iff : ¬ is_min a ↔ ∃ b, b < a :=
by simp_rw [lt_iff_le_not_le, is_min, not_forall, exists_prop]

@[simp] lemma not_is_max_iff : ¬ is_max a ↔ ∃ b, a < b :=
by simp_rw [lt_iff_le_not_le, is_max, not_forall, exists_prop]

@[simp] lemma not_is_min [no_min_order α] (a : α) : ¬ is_min a := not_is_min_iff.2 $ exists_lt a
@[simp] lemma not_is_max [no_max_order α] (a : α) : ¬ is_max a := not_is_max_iff.2 $ exists_gt a

namespace subsingleton
variable [subsingleton α]

protected lemma is_bot (a : α) : is_bot a := λ _, (subsingleton.elim _ _).le
protected lemma is_top (a : α) : is_top a := λ _, (subsingleton.elim _ _).le
protected lemma is_min (a : α) : is_min a := (subsingleton.is_bot _).is_min
protected lemma is_max (a : α) : is_max a := (subsingleton.is_top _).is_max

end subsingleton
end preorder

section partial_order
variables [partial_order α] {a b : α}

protected lemma is_min.eq_of_le (ha : is_min a) (h : b ≤ a) : b = a := h.antisymm $ ha h
protected lemma is_min.eq_of_ge (ha : is_min a) (h : b ≤ a) : a = b := h.antisymm' $ ha h
protected lemma is_max.eq_of_le (ha : is_max a) (h : a ≤ b) : a = b := h.antisymm $ ha h
protected lemma is_max.eq_of_ge (ha : is_max a) (h : a ≤ b) : b = a := h.antisymm' $ ha h

end partial_order

section prod
variables [preorder α] [preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

lemma is_bot.prod_mk (ha : is_bot a) (hb : is_bot b) : is_bot (a, b) := λ c, ⟨ha _, hb _⟩
lemma is_top.prod_mk (ha : is_top a) (hb : is_top b) : is_top (a, b) := λ c, ⟨ha _, hb _⟩
lemma is_min.prod_mk (ha : is_min a) (hb : is_min b) : is_min (a, b) := λ c hc, ⟨ha hc.1, hb hc.2⟩
lemma is_max.prod_mk (ha : is_max a) (hb : is_max b) : is_max (a, b) := λ c hc, ⟨ha hc.1, hb hc.2⟩

lemma is_bot.fst (hx : is_bot x) : is_bot x.1 := λ c, (hx (c, x.2)).1
lemma is_bot.snd (hx : is_bot x) : is_bot x.2 := λ c, (hx (x.1, c)).2
lemma is_top.fst (hx : is_top x) : is_top x.1 := λ c, (hx (c, x.2)).1
lemma is_top.snd (hx : is_top x) : is_top x.2 := λ c, (hx (x.1, c)).2

lemma is_min.fst (hx : is_min x) : is_min x.1 :=
λ c hc, (hx $ show (c, x.2) ≤ x, from (and_iff_left le_rfl).2 hc).1

lemma is_min.snd (hx : is_min x) : is_min x.2 :=
λ c hc, (hx $ show (x.1, c) ≤ x, from (and_iff_right le_rfl).2 hc).2

lemma is_max.fst (hx : is_max x) : is_max x.1 :=
λ c hc, (hx $ show x ≤ (c, x.2), from (and_iff_left le_rfl).2 hc).1

lemma is_max.snd (hx : is_max x) : is_max x.2 :=
λ c hc, (hx $ show x ≤ (x.1, c), from (and_iff_right le_rfl).2 hc).2

lemma prod.is_bot_iff : is_bot x ↔ is_bot x.1 ∧ is_bot x.2 :=
⟨λ hx, ⟨hx.fst, hx.snd⟩, λ h, h.1.prod_mk h.2⟩

lemma prod.is_top_iff : is_top x ↔ is_top x.1 ∧ is_top x.2 :=
⟨λ hx, ⟨hx.fst, hx.snd⟩, λ h, h.1.prod_mk h.2⟩

lemma prod.is_min_iff : is_min x ↔ is_min x.1 ∧ is_min x.2 :=
⟨λ hx, ⟨hx.fst, hx.snd⟩, λ h, h.1.prod_mk h.2⟩

lemma prod.is_max_iff : is_max x ↔ is_max x.1 ∧ is_max x.2 :=
⟨λ hx, ⟨hx.fst, hx.snd⟩, λ h, h.1.prod_mk h.2⟩

end prod
