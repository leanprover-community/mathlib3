/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.basic

/-!
# Orders on a sum type

This file defines the disjoint sum and the linear (aka lexicographic) sum of two orders and provides
relation instances for `sum.lift_rel` and `sum.lex`.

We declare the disjoint sum of orders as the default set of instances. The linear order goes on a
type synonym.

## Main declarations

* `sum.has_le`, `sum.has_lt`: Disjoint sum of orders.
* `sum.lex.has_le`, `sum.lex.has_lt`: Lexicographic/linear sum of orders.

## Notation

* `α ⊕ₗ β`:  The linear sum of `α` and `β`.
-/

namespace sum
variables {α β γ δ : Type*}

/-! ### Unbundled relation classes -/

section lift_rel
variables (r : α → α → Prop) (s : β → β → Prop)

@[refl] lemma lift_rel.refl [is_refl α r] [is_refl β s] : ∀ x, lift_rel r s x x
| (inl a) := lift_rel.inl (refl _)
| (inr a) := lift_rel.inr (refl _)

instance [is_refl α r] [is_refl β s] : is_refl (α ⊕ β) (lift_rel r s) := ⟨lift_rel.refl _ _⟩

instance [is_irrefl α r] [is_irrefl β s] : is_irrefl (α ⊕ β) (lift_rel r s) :=
⟨by { rintro _ (⟨a, _, h⟩ | ⟨a, _, h⟩); exact irrefl _ h }⟩

@[trans] lemma lift_rel.trans [is_trans α r] [is_trans β s] :
  ∀ {a b c}, lift_rel r s a b → lift_rel r s b c → lift_rel r s a c
| _ _ _ (lift_rel.inl hab) (lift_rel.inl hbc) := lift_rel.inl $ trans hab hbc
| _ _ _ (lift_rel.inr hab) (lift_rel.inr hbc) := lift_rel.inr $ trans hab hbc

instance [is_trans α r] [is_trans β s] : is_trans (α ⊕ β) (lift_rel r s) :=
⟨λ _ _ _, lift_rel.trans _ _⟩

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
⟨λ a b, match a, b with
  | inl a, inl b := (total_of r a b).imp lex.inl lex.inl
  | inl a, inr b := or.inl (lex.sep _ _)
  | inr a, inl b := or.inr (lex.sep _ _)
  | inr a, inr b := (total_of s a b).imp lex.inr lex.inr
end⟩

instance [is_trichotomous α r] [is_trichotomous β s] : is_trichotomous (α ⊕ β) (lex r s) :=
⟨λ a b, match a, b with
  | inl a, inl b := (trichotomous_of r a b).imp3 lex.inl (congr_arg _) lex.inl
  | inl a, inr b := or.inl (lex.sep _ _)
  | inr a, inl b := or.inr (or.inr $ lex.sep _ _)
  | inr a, inr b := (trichotomous_of s a b).imp3 lex.inr (congr_arg _) lex.inr
end⟩

instance [is_well_order α r] [is_well_order β s] : is_well_order (α ⊕ β) (sum.lex r s) :=
{ wf := sum.lex_wf is_well_order.wf is_well_order.wf }

end lex

/-! ### Disjoint sum of two orders -/

section disjoint

instance [has_le α] [has_le β] : has_le (α ⊕ β) := ⟨lift_rel (≤) (≤)⟩
instance [has_lt α] [has_lt β] : has_lt (α ⊕ β) := ⟨lift_rel (<) (<)⟩

lemma le_def [has_le α] [has_le β] {a b : α ⊕ β} : a ≤ b ↔ lift_rel (≤) (≤) a b := iff.rfl
lemma lt_def [has_lt α] [has_lt β] {a b : α ⊕ β} : a < b ↔ lift_rel (<) (<) a b := iff.rfl

@[simp] lemma inl_le_inl_iff [has_le α] [has_le β] {a b : α} : (inl a : α ⊕ β) ≤ inl b ↔ a ≤ b :=
lift_rel_inl_inl

@[simp] lemma inr_le_inr_iff [has_le α] [has_le β] {a b : β} : (inr a : α ⊕ β) ≤ inr b ↔ a ≤ b :=
lift_rel_inr_inr

@[simp] lemma inl_lt_inl_iff [has_lt α] [has_lt β] {a b : α} : (inl a : α ⊕ β) < inl b ↔ a < b :=
lift_rel_inl_inl

@[simp] lemma inr_lt_inr_iff [has_lt α] [has_lt β] {a b : β} : (inr a : α ⊕ β) < inr b ↔ a < b :=
lift_rel_inr_inr

@[simp] lemma not_inl_le_inr [has_le α] [has_le β] {a : α} {b : β} : ¬ inl b ≤ inr a :=
not_lift_rel_inl_inr

@[simp] lemma not_inl_lt_inr [has_lt α] [has_lt β] {a : α} {b : β} : ¬ inl b < inr a :=
not_lift_rel_inl_inr

@[simp] lemma not_inr_le_inl [has_le α] [has_le β] {a : α} {b : β} : ¬ inr b ≤ inl a :=
not_lift_rel_inr_inl

@[simp] lemma not_inr_lt_inl [has_lt α] [has_lt β] {a : α} {b : β} : ¬ inr b < inl a :=
not_lift_rel_inr_inl

section preorder
variables [preorder α] [preorder β]

instance : preorder (α ⊕ β) :=
{ le_refl := λ _, refl _,
  le_trans := λ _ _ _, trans,
  lt_iff_le_not_le := λ a b, begin
    refine ⟨λ hab, ⟨hab.mono (λ _ _, le_of_lt) (λ _ _, le_of_lt), _⟩, _⟩,
    { rintro (⟨b, a, hba⟩ | ⟨b, a, hba⟩),
      { exact hba.not_lt (inl_lt_inl_iff.1 hab) },
      { exact hba.not_lt (inr_lt_inr_iff.1 hab) } },
    { rintro ⟨⟨a, b, hab⟩ | ⟨a, b, hab⟩, hba⟩,
      { exact lift_rel.inl (hab.lt_of_not_le $ λ h, hba $ lift_rel.inl h) },
      { exact lift_rel.inr (hab.lt_of_not_le $ λ h, hba $ lift_rel.inr h) } }
  end,
  .. sum.has_le, .. sum.has_lt }

lemma inl_mono : monotone (inl : α → α ⊕ β) := λ a b, lift_rel.inl
lemma inr_mono : monotone (inr : β → α ⊕ β) := λ a b, lift_rel.inr
lemma inl_strict_mono : strict_mono (inl : α → α ⊕ β) := λ a b, lift_rel.inl
lemma inr_strict_mono : strict_mono (inr : β → α ⊕ β) := λ a b, lift_rel.inr

end preorder

instance [partial_order α] [partial_order β] : partial_order (α ⊕ β) :=
{ le_antisymm := λ _ _, antisymm,
  .. sum.preorder }

instance no_min_order [has_lt α] [has_lt β] [no_min_order α] [no_min_order β] :
  no_min_order (α ⊕ β) :=
⟨λ a, match a with
| inl a := let ⟨b, h⟩ := exists_lt a in ⟨inl b, inl_lt_inl_iff.2 h⟩
| inr a := let ⟨b, h⟩ := exists_lt a in ⟨inr b, inr_lt_inr_iff.2 h⟩
end⟩

instance no_max_order [has_lt α] [has_lt β] [no_max_order α] [no_max_order β] :
  no_max_order (α ⊕ β) :=
⟨λ a, match a with
| inl a := let ⟨b, h⟩ := exists_gt a in ⟨inl b, inl_lt_inl_iff.2 h⟩
| inr a := let ⟨b, h⟩ := exists_gt a in ⟨inr b, inr_lt_inr_iff.2 h⟩
end⟩

@[simp] lemma no_min_order_iff [has_lt α] [has_lt β] :
  no_min_order (α ⊕ β) ↔ no_min_order α ∧ no_min_order β :=
⟨λ _, by exactI ⟨⟨λ a, begin
  obtain ⟨b | b, h⟩ := exists_lt (inl a : α ⊕ β),
  { exact ⟨b, inl_lt_inl_iff.1 h⟩ },
  { exact (not_inr_lt_inl h).elim }
end⟩, ⟨λ a, begin
  obtain ⟨b | b, h⟩ := exists_lt (inr a : α ⊕ β),
  { exact (not_inl_lt_inr h).elim },
  { exact ⟨b, inr_lt_inr_iff.1 h⟩ }
end⟩⟩, λ h, @sum.no_min_order _ _ _ _ h.1 h.2⟩

@[simp] lemma no_max_order_iff [has_lt α] [has_lt β] :
  no_max_order (α ⊕ β) ↔ no_max_order α ∧ no_max_order β :=
⟨λ _, by exactI ⟨⟨λ a, begin
  obtain ⟨b | b, h⟩ := exists_gt (inl a : α ⊕ β),
  { exact ⟨b, inl_lt_inl_iff.1 h⟩ },
  { exact (not_inl_lt_inr h).elim }
end⟩, ⟨λ a, begin
  obtain ⟨b | b, h⟩ := exists_gt (inr a : α ⊕ β),
  { exact (not_inr_lt_inl h).elim },
  { exact ⟨b, inr_lt_inr_iff.1 h⟩ }
end⟩⟩, λ h, @sum.no_max_order _ _ _ _ h.1 h.2⟩

instance densely_ordered [has_lt α] [has_lt β] [densely_ordered α] [densely_ordered β] :
  densely_ordered (α ⊕ β) :=
⟨λ a b h, match a, b, h with
| inl a, inl b, lift_rel.inl h := let ⟨c, ha, hb⟩ := exists_between h in
                    ⟨to_lex (inl c), lift_rel.inl ha, lift_rel.inl hb⟩
| inr a, inr b, lift_rel.inr h := let ⟨c, ha, hb⟩ := exists_between h in
                    ⟨to_lex (inr c), lift_rel.inr ha, lift_rel.inr hb⟩
end⟩

@[simp] lemma densely_ordered_iff [has_lt α] [has_lt β] :
  densely_ordered (α ⊕ β) ↔ densely_ordered α ∧ densely_ordered β :=
⟨λ _, by exactI ⟨⟨λ a b h, begin
  obtain ⟨c | c, ha, hb⟩ := @exists_between (α ⊕ β) _ _ _ _ (inl_lt_inl_iff.2 h),
  { exact ⟨c, inl_lt_inl_iff.1 ha, inl_lt_inl_iff.1 hb⟩ },
  { exact (not_inl_lt_inr ha).elim }
end⟩, ⟨λ a b h, begin
  obtain ⟨c | c, ha, hb⟩ := @exists_between (α ⊕ β) _ _ _ _ (inr_lt_inr_iff.2 h),
  { exact (not_inl_lt_inr hb).elim },
  { exact ⟨c, inr_lt_inr_iff.1 ha, inr_lt_inr_iff.1 hb⟩ }
end⟩⟩, λ h, @sum.densely_ordered _ _ _ _ h.1 h.2⟩

@[simp] lemma swap_le_swap_iff [has_le α] [has_le β] {a b : α ⊕ β} : a.swap ≤ b.swap ↔ a ≤ b :=
by cases a; cases b;
  simp only [swap, inr_le_inr_iff, inl_le_inl_iff, not_inl_le_inr, not_inr_le_inl]

@[simp] lemma swap_lt_swap_iff [has_lt α] [has_lt β] {a b : α ⊕ β} : a.swap < b.swap ↔ a < b :=
by cases a; cases b;
  simp only [swap, inr_lt_inr_iff, inl_lt_inl_iff, not_inl_lt_inr, not_inr_lt_inl]

end disjoint

/-! ### Linear sum of two orders -/

namespace lex

notation α ` ⊕ₗ `:30 β:29 := _root_.lex (α ⊕ β)

--TODO: Can we make `inlₗ`, `inrₗ` `local notation`?

/-- Lexicographical `sum.inl`. Only used for pattern matching. -/
@[pattern] abbreviation _root_.sum.inlₗ (x : α) : α ⊕ₗ β := to_lex (sum.inl x)

/-- Lexicographical `sum.inr`. Only used for pattern matching. -/
@[pattern] abbreviation _root_.sum.inrₗ (x : β) : α ⊕ₗ β := to_lex (sum.inr x)

/-- The linear/lexicographical `≤` on a sum. -/
instance has_le [has_le α] [has_le β] : has_le (α ⊕ₗ β) := ⟨lex (≤) (≤)⟩

/-- The linear/lexicographical `<` on a sum. -/
instance has_lt [has_lt α] [has_lt β] : has_lt (α ⊕ₗ β) := ⟨lex (<) (<)⟩

@[simp] lemma to_lex_le_to_lex [has_le α] [has_le β] {a b : α ⊕ β} :
  to_lex a ≤ to_lex b ↔ lex (≤) (≤) a b := iff.rfl

@[simp] lemma to_lex_lt_to_lex [has_lt α] [has_lt β] {a b : α ⊕ β} :
  to_lex a < to_lex b ↔ lex (<) (<) a b := iff.rfl

lemma le_def [has_le α] [has_le β] {a b : α ⊕ₗ β} : a ≤ b ↔ lex (≤) (≤) (of_lex a) (of_lex b) :=
iff.rfl

lemma lt_def [has_lt α] [has_lt β] {a b : α ⊕ₗ β} : a < b ↔ lex (<) (<) (of_lex a) (of_lex b) :=
iff.rfl

@[simp] lemma inl_le_inl_iff [has_le α] [has_le β] {a b : α} :
  to_lex (inl a : α ⊕ β) ≤ to_lex (inl b) ↔ a ≤ b :=
lex_inl_inl

@[simp] lemma inr_le_inr_iff [has_le α] [has_le β] {a b : β} :
  to_lex (inr a : α ⊕ β) ≤ to_lex (inr b) ↔ a ≤ b :=
lex_inr_inr

@[simp] lemma inl_lt_inl_iff [has_lt α] [has_lt β] {a b : α} :
  to_lex (inl a : α ⊕ β) < to_lex (inl b) ↔ a < b :=
lex_inl_inl

@[simp] lemma inr_lt_inr_iff [has_lt α] [has_lt β] {a b : β} :
  to_lex (inr a : α ⊕ₗ β) < to_lex (inr b) ↔ a < b :=
lex_inr_inr

@[simp] lemma inl_le_inr [has_le α] [has_le β] (a : α) (b : β) : to_lex (inl a) ≤ to_lex (inr b) :=
lex.sep _ _

@[simp] lemma inl_lt_inr [has_lt α] [has_lt β] (a : α) (b : β) : to_lex (inl a) < to_lex (inr b) :=
lex.sep _ _

@[simp] lemma not_inr_le_inl [has_le α] [has_le β] {a : α} {b : β} :
  ¬ to_lex (inr b) ≤ to_lex (inl a) :=
lex_inr_inl

@[simp] lemma not_inr_lt_inl [has_lt α] [has_lt β] {a : α} {b : β} :
  ¬ to_lex (inr b) < to_lex (inl a) :=
lex_inr_inl

section preorder
variables [preorder α] [preorder β]

instance preorder : preorder (α ⊕ₗ β) :=
{ le_refl := refl_of (lex (≤) (≤)),
  le_trans := λ _ _ _, trans_of (lex (≤) (≤)),
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

lemma to_lex_mono : monotone (@to_lex (α ⊕ β)) := λ a b h, h.lex
lemma to_lex_strict_mono : strict_mono (@to_lex (α ⊕ β)) := λ a b h, h.lex

lemma inl_mono : monotone (to_lex ∘ inl : α → α ⊕ₗ β) := to_lex_mono.comp inl_mono
lemma inr_mono : monotone (to_lex ∘ inr : β → α ⊕ₗ β) := to_lex_mono.comp inr_mono

lemma inl_strict_mono : strict_mono (to_lex ∘ inl : α → α ⊕ₗ β) :=
to_lex_strict_mono.comp inl_strict_mono

lemma inr_strict_mono : strict_mono (to_lex ∘ inr : β → α ⊕ₗ β) :=
to_lex_strict_mono.comp inr_strict_mono

end preorder

instance partial_order [partial_order α] [partial_order β] : partial_order (α ⊕ₗ β) :=
{ le_antisymm := λ _ _, antisymm_of (lex (≤) (≤)),
  .. lex.preorder }

instance linear_order [linear_order α] [linear_order β] : linear_order (α ⊕ₗ β) :=
{ le_total := total_of (lex (≤) (≤)),
  decidable_le := lex.decidable_rel,
  decidable_eq := sum.decidable_eq _ _,
  .. lex.partial_order }

/-- The lexicographical bottom of a sum is the bottom of the left component. -/
instance order_bot [has_le α] [order_bot α] [has_le β] : order_bot (α ⊕ₗ β) :=
{ bot := inl ⊥,
  bot_le := begin
    rintro (a | b),
    { exact lex.inl bot_le },
    { exact lex.sep _ _ }
  end }

@[simp] lemma inl_bot [has_le α] [order_bot α] [has_le β]: to_lex (inl ⊥ : α ⊕ β) = ⊥ := rfl

/-- The lexicographical top of a sum is the top of the right component. -/
instance order_top [has_le α] [has_le β] [order_top β] : order_top (α ⊕ₗ β) :=
{ top := inr ⊤,
  le_top := begin
    rintro (a | b),
    { exact lex.sep _ _ },
    { exact lex.inr le_top }
  end }

@[simp] lemma inr_top [has_le α] [has_le β] [order_top β] : to_lex (inr ⊤ : α ⊕ β) = ⊤ := rfl

instance bounded_order [has_le α] [has_le β] [order_bot α] [order_top β] :
  bounded_order (α ⊕ₗ β) :=
{ .. lex.order_bot, .. lex.order_top }

instance no_min_order [has_lt α] [has_lt β] [no_min_order α] [no_min_order β] :
  no_min_order (α ⊕ₗ β) :=
⟨λ a, match a with
| inl a := let ⟨b, h⟩ := exists_lt a in ⟨to_lex (inl b), inl_lt_inl_iff.2 h⟩
| inr a := let ⟨b, h⟩ := exists_lt a in ⟨to_lex (inr b), inr_lt_inr_iff.2 h⟩
end⟩

instance no_max_order [has_lt α] [has_lt β] [no_max_order α] [no_max_order β] :
  no_max_order (α ⊕ₗ β) :=
⟨λ a, match a with
| inl a := let ⟨b, h⟩ := exists_gt a in ⟨to_lex (inl b), inl_lt_inl_iff.2 h⟩
| inr a := let ⟨b, h⟩ := exists_gt a in ⟨to_lex (inr b), inr_lt_inr_iff.2 h⟩
end⟩

instance no_min_order_of_nonempty [has_lt α] [has_lt β] [no_min_order α] [nonempty α] :
  no_min_order (α ⊕ₗ β) :=
⟨λ a, match a with
| inl a := let ⟨b, h⟩ := exists_lt a in ⟨to_lex (inl b), inl_lt_inl_iff.2 h⟩
| inr a := ⟨to_lex (inl $ classical.arbitrary α), inl_lt_inr _ _⟩
end⟩

instance no_max_order_of_nonempty [has_lt α] [has_lt β] [no_max_order β] [nonempty β] :
  no_max_order (α ⊕ₗ β) :=
⟨λ a, match a with
| inl a := ⟨to_lex (inr $ classical.arbitrary β), inl_lt_inr _ _⟩
| inr a := let ⟨b, h⟩ := exists_gt a in ⟨to_lex (inr b), inr_lt_inr_iff.2 h⟩
end⟩

instance densely_ordered_of_no_max_order [has_lt α] [has_lt β] [densely_ordered α]
  [densely_ordered β] [no_max_order α] :
  densely_ordered (α ⊕ₗ β) :=
⟨λ a b h, match a, b, h with
| inl a, inl b, lex.inl h := let ⟨c, ha, hb⟩ := exists_between h in
                    ⟨to_lex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
| inl a, inr b, lex.sep _ _ := let ⟨c, h⟩ := exists_gt a in
                    ⟨to_lex (inl c), inl_lt_inl_iff.2 h, inl_lt_inr _ _⟩
| inr a, inr b, lex.inr h := let ⟨c, ha, hb⟩ := exists_between h in
                    ⟨to_lex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩
end⟩

instance densely_ordered_of_no_min_order [has_lt α] [has_lt β] [densely_ordered α]
  [densely_ordered β] [no_min_order β] :
  densely_ordered (α ⊕ₗ β) :=
⟨λ a b h, match a, b, h with
| inl a, inl b, lex.inl h := let ⟨c, ha, hb⟩ := exists_between h in
                    ⟨to_lex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
| inl a, inr b, lex.sep _ _ := let ⟨c, h⟩ := exists_lt b in
                    ⟨to_lex (inr c), inl_lt_inr _ _, inr_lt_inr_iff.2 h⟩
| inr a, inr b, lex.inr h := let ⟨c, ha, hb⟩ := exists_between h in
                    ⟨to_lex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩
end⟩

end lex
end sum

/-! ### Order isomorphisms -/

open order_dual sum

namespace order_iso
variables {α β γ : Type*} [has_le α] [has_le β] [has_le γ] (a : α) (b : β) (c : γ)

/-- `equiv.sum_comm` promoted to an order isomorphism. -/
@[simps apply] def sum_comm (α β : Type*) [has_le α] [has_le β] : α ⊕ β ≃o β ⊕ α :=
{ map_rel_iff' := λ a b, swap_le_swap_iff,
  ..equiv.sum_comm α β }

@[simp] lemma sum_comm_symm (α β : Type*) [has_le α] [has_le β] :
  (order_iso.sum_comm α β).symm = order_iso.sum_comm β α := rfl

/-- `equiv.sum_assoc` promoted to an order isomorphism. -/
def sum_assoc (α β γ : Type*) [has_le α] [has_le β] [has_le γ] : (α ⊕ β) ⊕ γ ≃o α ⊕ β ⊕ γ :=
{ map_rel_iff' := by { rintro ((a | a) | a) ((b | b) | b); simp },
  ..equiv.sum_assoc α β γ }

@[simp] lemma sum_assoc_apply_inl_inl : sum_assoc α β γ (inl (inl a)) = inl a := rfl
@[simp] lemma sum_assoc_apply_inl_inr : sum_assoc α β γ (inl (inr b)) = inr (inl b) := rfl
@[simp] lemma sum_assoc_apply_inr : sum_assoc α β γ (inr c) = inr (inr c) := rfl
@[simp] lemma sum_assoc_symm_apply_inl : (sum_assoc α β γ).symm (inl a) = inl (inl a) := rfl
@[simp] lemma sum_assoc_symm_apply_inr_inl : (sum_assoc α β γ).symm (inr (inl b)) = inl (inr b) :=
rfl
@[simp] lemma sum_assoc_symm_apply_inr_inr : (sum_assoc α β γ).symm (inr (inr c)) = inr c := rfl

/-- `order_dual` is distributive over `⊕` up to an order isomorphism. -/
def sum_dual_distrib (α β : Type*) [has_le α] [has_le β] : (α ⊕ β)ᵒᵈ ≃o αᵒᵈ ⊕ βᵒᵈ :=
{ map_rel_iff' := begin
  rintro (a | a) (b | b),
  { change inl (to_dual a) ≤ inl (to_dual b) ↔ to_dual (inl a) ≤ to_dual (inl b),
    simp only [to_dual_le_to_dual, inl_le_inl_iff] },
  { exact iff_of_false not_inl_le_inr not_inr_le_inl },
  { exact iff_of_false not_inr_le_inl not_inl_le_inr },
  { change inr (to_dual a) ≤ inr (to_dual b) ↔ to_dual (inr a) ≤ to_dual (inr b),
    simp only [to_dual_le_to_dual, inr_le_inr_iff] }
end,
  ..equiv.refl _ }

@[simp] lemma sum_dual_distrib_inl :
  sum_dual_distrib α β (to_dual (inl a)) = inl (to_dual a) := rfl

@[simp] lemma sum_dual_distrib_inr :
  sum_dual_distrib α β (to_dual (inr b)) = inr (to_dual b) := rfl

@[simp] lemma sum_dual_distrib_symm_inl :
  (sum_dual_distrib α β).symm (inl (to_dual a)) = to_dual (inl a) := rfl

@[simp] lemma sum_dual_distrib_symm_inr  :
  (sum_dual_distrib α β).symm (inr (to_dual b)) = to_dual (inr b) := rfl

/-- `equiv.sum_assoc` promoted to an order isomorphism. -/
def sum_lex_assoc (α β γ : Type*) [has_le α] [has_le β] [has_le γ] : (α ⊕ₗ β) ⊕ₗ γ ≃o α ⊕ₗ β ⊕ₗ γ :=
{ map_rel_iff' := λ a b, ⟨λ h, match a, b, h with
    | inlₗ (inlₗ a), inlₗ (inlₗ b), lex.inl h := lex.inl $ lex.inl h
    | inlₗ (inlₗ a), inlₗ (inrₗ b), lex.sep _ _ := lex.inl $ lex.sep _ _
    | inlₗ (inlₗ a),        inrₗ b, lex.sep _ _ := lex.sep _ _
    | inlₗ (inrₗ a), inlₗ (inrₗ b), lex.inr (lex.inl h) := lex.inl $ lex.inr h
    | inlₗ (inrₗ a),        inrₗ b, lex.inr (lex.sep _ _) := lex.sep _ _
    |       inrₗ a,        inrₗ b, lex.inr (lex.inr h) := lex.inr h
    end, λ h, match a, b, h with
    | inlₗ (inlₗ a), inlₗ (inlₗ b), lex.inl (lex.inl h) := lex.inl h
    | inlₗ (inlₗ a), inlₗ (inrₗ b), lex.inl (lex.sep _ _) := lex.sep _ _
    | inlₗ (inlₗ a),        inrₗ b, lex.sep _ _ := lex.sep _ _
    | inlₗ (inrₗ a), inlₗ (inrₗ b), lex.inl (lex.inr h) := lex.inr $ lex.inl h
    | inlₗ (inrₗ a),        inrₗ b, lex.sep _ _ := lex.inr $ lex.sep _ _
    |       inrₗ a,        inrₗ b, lex.inr h  := lex.inr $ lex.inr h
    end⟩,
  ..equiv.sum_assoc α β γ }

@[simp] lemma sum_lex_assoc_apply_inl_inl :
  sum_lex_assoc α β γ (to_lex $ inl $ to_lex $ inl a) = to_lex (inl a) := rfl

@[simp] lemma sum_lex_assoc_apply_inl_inr :
  sum_lex_assoc α β γ (to_lex $ inl $ to_lex $ inr b) = to_lex (inr $ to_lex $ inl b) := rfl

@[simp] lemma sum_lex_assoc_apply_inr :
  sum_lex_assoc α β γ (to_lex $ inr c) = to_lex (inr $ to_lex $ inr c) := rfl

@[simp] lemma sum_lex_assoc_symm_apply_inl :
  (sum_lex_assoc α β γ).symm (inl a) = inl (inl a) := rfl

@[simp] lemma sum_lex_assoc_symm_apply_inr_inl :
  (sum_lex_assoc α β γ).symm (inr (inl b)) = inl (inr b) := rfl

@[simp] lemma sum_lex_assoc_symm_apply_inr_inr :
  (sum_lex_assoc α β γ).symm (inr (inr c)) = inr c := rfl

/-- `order_dual` is antidistributive over `⊕ₗ` up to an order isomorphism. -/
def sum_lex_dual_antidistrib (α β : Type*) [has_le α] [has_le β] : (α ⊕ₗ β)ᵒᵈ ≃o βᵒᵈ ⊕ₗ αᵒᵈ :=
{ map_rel_iff' := begin
  rintro (a | a) (b | b), simp,
  { change to_lex (inr $ to_dual a) ≤ to_lex (inr $ to_dual b) ↔
      to_dual (to_lex $ inl a) ≤ to_dual (to_lex $ inl b),
    simp only [to_dual_le_to_dual, lex.inl_le_inl_iff, lex.inr_le_inr_iff] },
  { exact iff_of_false lex.not_inr_le_inl lex.not_inr_le_inl },
  { exact iff_of_true (lex.inl_le_inr _ _) (lex.inl_le_inr _ _) },
  { change to_lex (inl $ to_dual a) ≤ to_lex (inl $ to_dual b) ↔
      to_dual (to_lex $ inr a) ≤ to_dual (to_lex $ inr b),
    simp only [to_dual_le_to_dual, lex.inl_le_inl_iff, lex.inr_le_inr_iff] }
end,
  ..equiv.sum_comm α β }

@[simp] lemma sum_lex_dual_antidistrib_inl :
  sum_lex_dual_antidistrib α β (to_dual (inl a)) = inr (to_dual a) := rfl

@[simp] lemma sum_lex_dual_antidistrib_inr :
  sum_lex_dual_antidistrib α β (to_dual (inr b)) = inl (to_dual b) := rfl

@[simp] lemma sum_lex_dual_antidistrib_symm_inl :
  (sum_lex_dual_antidistrib α β).symm (inl (to_dual b)) = to_dual (inr b) := rfl

@[simp] lemma sum_lex_dual_antidistrib_symm_inr :
  (sum_lex_dual_antidistrib α β).symm (inr (to_dual a)) = to_dual (inl a) := rfl

end order_iso
