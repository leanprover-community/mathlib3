/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sum.basic
import order.bounded_order

/-!
# Orders on a sum type

This file defines the disjoint sum and the linear (aka lexicographic) sum of two orders.

It also provides relation instances for `sum.lift_rel` and `sum.lex`.

## Implementation notes

We declare the disjoint sum of orders as the default instances. The linear order can override it
locally by opening locale `lex`.

## TODO

Define the order embedding from the disjoint sum to the linear sum.
-/

namespace sum
variables {α β γ δ : Type*}

/-! ### Unbundled relation classes -/

section lift_rel
variables (r : α → α → Prop) (s : β → β → Prop)

instance [is_refl α r] [is_refl β s] : is_refl (α ⊕ β) (lift_rel r s) :=
⟨by { rintro (a | a), exacts [lift_rel.inl (refl _), lift_rel.inr (refl _)] }⟩

instance [is_irrefl α r] [is_irrefl β s] : is_irrefl (α ⊕ β) (lift_rel r s) :=
⟨by { rintro _ (⟨a, _, h⟩ | ⟨a, _, h⟩); exact irrefl _ h }⟩

instance [is_trans α r] [is_trans β s] : is_trans (α ⊕ β) (lift_rel r s) :=
⟨by { rintro _ _ _ (⟨a, b, hab⟩ | ⟨a, b, hab⟩) (⟨_, c, hbc⟩ | ⟨_, c, hbc⟩),
  exacts [lift_rel.inl (trans hab hbc), lift_rel.inr (trans hab hbc)] }⟩

instance [is_antisymm α r] [is_antisymm β s] : is_antisymm (α ⊕ β) (lift_rel r s) :=
⟨by { rintro _ _ (⟨a, b, hab⟩ | ⟨a, b, hab⟩) (⟨_, _, hba⟩ | ⟨_, _, hba⟩); rw antisymm hab hba }⟩

end lift_rel

section lex
variables (r : α → α → Prop) (s : β → β → Prop)

instance [is_refl α r] [is_refl β s] : is_refl (α ⊕ β) (lex r s) :=
⟨by { rintro (a | a), exacts [lex.inl (refl _), lex.inr (refl _)] }⟩

instance [is_irrefl α r] [is_irrefl β s] : is_irrefl (α ⊕ β) (lex r s) :=
⟨by { rintro _ (⟨a, _, h⟩ | ⟨a, _, h⟩); exact irrefl _ h }⟩

instance [is_trans α r] [is_trans β s] : is_trans (α ⊕ β) (lex r s) :=
⟨by { rintro _ _ _ (⟨a, b, hab⟩ | ⟨a, b, hab⟩) (⟨_, c, hbc⟩ | ⟨_, c, hbc⟩),
  exacts [lex.inl (trans hab hbc), lex.sep _ _, lex.inr (trans hab hbc), lex.sep _ _] }⟩

instance [is_antisymm α r] [is_antisymm β s] : is_antisymm (α ⊕ β) (lex r s) :=
⟨by { rintro _ _ (⟨a, b, hab⟩ | ⟨a, b, hab⟩) (⟨_, _, hba⟩ | ⟨_, _, hba⟩); rw antisymm hab hba }⟩

instance [is_total α r] [is_total β s] : is_total (α ⊕ β) (lex r s) :=
⟨begin
  rintro (a | a) (b | b),
  { exact (total_of r a b).imp lex.inl lex.inl },
  { exact or.inl (lex.sep _ _) },
  { exact or.inr (lex.sep _ _) },
  { exact (total_of s a b).imp lex.inr lex.inr }
end⟩

instance [is_trichotomous α r] [is_trichotomous β s] : is_trichotomous (α ⊕ β) (lex r s) :=
⟨begin
  rintro (a | a) (b | b),
  { exact (trichotomous_of r a b).imp3 lex.inl (congr_arg _) lex.inl },
  { exact or.inl (lex.sep _ _) },
  { exact or.inr (or.inr $ lex.sep _ _) },
  { exact (trichotomous_of s a b).imp3 lex.inr (congr_arg _) lex.inr }
end⟩

instance [is_well_order α r] [is_well_order β s] : is_well_order (α ⊕ β) (sum.lex r s) :=
{ wf := sum.lex_wf is_well_order.wf is_well_order.wf }

end lex

/-! # Disjoint sum of two orders -/

section disjoint

instance [has_le α] [has_le β] : has_le (α ⊕ β) := ⟨lift_rel (≤) (≤)⟩

instance [preorder α] [preorder β] : preorder (α ⊕ β) :=
{ le_refl := λ _, refl _,
  le_trans := λ _ _ _, trans,
  .. sum.has_le }

instance [partial_order α] [partial_order β] : partial_order (α ⊕ β) :=
{ le_antisymm := λ _ _, antisymm,
  .. sum.preorder }

end disjoint

/-! # Linear sum of two orders -/

namespace lex

localized "attribute [-instance] sum.has_le" in lex
localized "attribute [-instance] sum.preorder" in lex
localized "attribute [-instance] sum.partial_order" in le

/-- The linear/lexicographical `≤` on a sum. Turn this on by opening locale `lex`. -/
protected def has_le [has_le α] [has_le β] : has_le (α ⊕ β) := ⟨lex (≤) (≤)⟩

/-- The linear/lexicographical `<` on a sum. Turn this on by opening locale `lex`. -/
protected def has_lt [has_lt α] [has_lt β] : has_lt (α ⊕ β) := ⟨lex (<) (<)⟩

localized "attribute [instance] sum.lex.has_le" in lex
localized "attribute [instance] sum.lex.has_lt" in lex

lemma le_def [has_le α] [has_le β] {a b : α ⊕ β} : a ≤ b ↔ lex (≤) (≤) a b := iff.rfl
lemma lt_def [has_lt α] [has_lt β] {a b : α ⊕ β} : a < b ↔ lex (<) (<) a b := iff.rfl

lemma inl_le_inl_iff [has_le α] [has_le β] {a b : α} : (inl a : α ⊕ β) ≤ inl b ↔ a ≤ b :=
lex_inl_inl

lemma inr_le_inr_iff [has_le α] [has_le β] {a b : β} : (inr a : α ⊕ β) ≤ inr b ↔ a ≤ b :=
lex_inr_inr

lemma inl_lt_inl_iff [has_lt α] [has_lt β] {a b : α} : (inl a : α ⊕ β) < inl b ↔ a < b :=
lex_inl_inl

lemma inr_lt_inr_iff [has_lt α] [has_lt β] {a b : β} : (inr a : α ⊕ β) < inr b ↔ a < b :=
lex_inr_inr

lemma not_inr_le_inl [has_le α] [has_le β] {a : α} {b : β} : ¬ inr b ≤ inl a := lex_inr_inl
lemma not_inr_lt_inl [has_lt α] [has_lt β] {a : α} {b : β} : ¬ inr b < inl a := lex_inr_inl

/-- The linear/lexicographical preorder on a sum. Turn this on by opening locale `lex`. -/
protected def preorder [preorder α] [preorder β] : preorder (α ⊕ β) :=
{ le_refl := λ _, refl _,
  le_trans := λ _ _ _, trans,
  lt_iff_le_not_le := λ a b, begin
    refine ⟨λ hab, ⟨hab.mono (λ _ _, le_of_lt) (λ _ _, le_of_lt), _⟩, _⟩,
    { rintro (⟨b, a, hba⟩ | ⟨b, a, hba⟩ | ⟨b, a⟩),
      { exact hba.not_lt (inl_lt_inl_iff.1 hab) },
      { exact hba.not_lt (inr_lt_inr_iff.1 hab) },
      { exact not_inr_lt_inl hab } },
    { rintro ⟨⟨a, b, hab⟩ | ⟨a, b, hab⟩ | ⟨a, b⟩, hba⟩,
      { exact lex.inl (hab.lt_of_not_le $ λ h, hba $ lex.inl h) },
      { exact lex.inr (hab.lt_of_not_le $ λ h, hba $ lex.inr h) },
      { exact lex.sep _ _} }
  end,
  .. lex.has_le, .. lex.has_lt }

localized "attribute [instance] sum.lex.preorder" in lex

/-- The linear/lexicographical partial order on a sum. Turn this on by opening locale `lex`. -/
protected def partial_order [partial_order α] [partial_order β] : partial_order (α ⊕ β) :=
{ le_antisymm := λ _ _, antisymm,
  .. lex.preorder }

localized "attribute [instance] sum.lex.partial_order" in lex

/-- The linear order on a sum. Turn this on by opening locale `lex`. -/
protected def linear_order [linear_order α] [linear_order β] : linear_order (α ⊕ β) :=
{ le_total := total_of _,
  decidable_le := lex.decidable_rel,
  decidable_eq := sum.decidable_eq _ _,
  .. lex.partial_order }

localized "attribute [instance] sum.lex.linear_order" in lex

/-- The lexicographical bottom of a sum. Turn this on by opening locale `lex`. -/
protected def order_bot [has_le α] [order_bot α] [has_le β] : order_bot (α ⊕ β) :=
{ bot := inl ⊥,
  bot_le := begin
    rintro (a | b),
    { exact lex.inl bot_le },
    { exact lex.sep _ _ }
  end }

localized "attribute [instance] sum.lex.order_bot" in lex

@[simp] lemma inl_bot [has_le α] [order_bot α] [has_le β]: (inl ⊥ : α ⊕ β) = ⊥ := rfl

/-- The lexicographical top of a sum. Turn this on by opening locale `lex`. -/
protected def order_top [has_le α] [has_le β] [order_top β] : order_top (α ⊕ β) :=
{ top := inr ⊤,
  le_top := begin
    rintro (a | b),
    { exact lex.sep _ _ },
    { exact lex.inr le_top }
  end }

localized "attribute [instance] sum.lex.order_top" in lex

@[simp] lemma inr_top [has_le α] [has_le β] [order_top β] : (inr ⊤ : α ⊕ β) = ⊤ := rfl

/-- The lexicographical bounded order on a sum. Turn this on by opening locale `lex`. -/
protected def bounded_order [has_le α] [has_le β] [order_bot α] [order_top β] :
  bounded_order (α ⊕ β) :=
{ .. lex.order_bot, .. lex.order_top }

localized "attribute [instance] sum.lex.bounded_order" in lex

end lex
end sum
