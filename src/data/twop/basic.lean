/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.concrete_category.bundled
import data.fintype.basic
import data.sum.basic
import order.bounded_order

/-!
# Pointed sum and two-pointed types

## TODO

`card (two_pointed α) = card α * (card α - 1)`
-/

open function sum

variables {α β : Type*}

/-- Type-valued `nontrivial`. -/
class two_pointed (α : Type*) :=
(fst snd : α)
(fst_ne_snd : fst ≠ snd)

section two_pointed
variables (α) [two_pointed α] [two_pointed β]

/-- The first pointed element of 𝒶 pointed type. -/
def pointed_fst : α := two_pointed.fst

/-- The first pointed element of 𝒶 pointed type. -/
def pointed_snd : α := two_pointed.snd

lemma pointed_fst_ne_snd : pointed_fst α ≠ pointed_snd α := two_pointed.fst_ne_snd
lemma pointed_snd_ne_fst : pointed_snd α ≠ pointed_fst α := (pointed_fst_ne_snd _).symm

@[priority 100] -- See note [lower instance priority]
instance two_pointed.to_nontrivial : nontrivial α :=
⟨⟨pointed_fst α, pointed_snd α, pointed_fst_ne_snd α⟩⟩

/-- Swaps the two pointed elements. -/
def two_pointed_swap : two_pointed α := ⟨pointed_snd α, pointed_fst α, pointed_snd_ne_fst α⟩

end two_pointed

namespace pointed_sum
variables {𝒶 a : α} {𝒷 b : β} {x y z : α ⊕ β}

/-- Glues `sum.inl 𝒶` and `sum.inr 𝒷` and nothing else. -/
inductive rel (𝒶 : α) (𝒷 : β) : α ⊕ β → α ⊕ β → Prop
| refl (x : α ⊕ β) : rel x x
| glue_left : rel (inl 𝒶) (inr 𝒷)
| glue_right : rel (inr 𝒷) (inl 𝒶)

attribute [refl] rel.refl

@[symm] lemma rel.symm : rel 𝒶 𝒷 x y → rel 𝒶 𝒷 y x := by rintro (_ | _ | _); constructor

@[trans] lemma rel.trans : ∀ {x y z}, rel 𝒶 𝒷 x y → rel 𝒶 𝒷 y z → rel 𝒶 𝒷 x z
| _ _ _ (rel.refl _)   (rel.refl _)   := rel.refl _
| _ _ _ (rel.refl _)   rel.glue_left  := rel.glue_left
| _ _ _ (rel.refl _)   rel.glue_right := rel.glue_right
| _ _ _ rel.glue_left  (rel.refl _) := rel.glue_left
| _ _ _ rel.glue_right (rel.refl _) := rel.glue_right
| _ _ _ rel.glue_left  rel.glue_right := rel.refl _
| _ _ _ rel.glue_right rel.glue_left  := rel.refl _

lemma rel.equivalence : equivalence (rel 𝒶 𝒷) := by tidy; apply rel.trans; assumption

variables (𝒶 𝒷)

/-- The quotient of `α ⊕ β` by `sum.inl 𝒶 = sum.inr 𝒷`. -/
def rel.setoid : setoid (α ⊕ β) := ⟨rel 𝒶 𝒷, rel.equivalence⟩

/-- The sum of `α` and `β` pointed at `𝒶` and `𝒷`. -/
def _root_.pointed_sum : Type* := quotient (pointed_sum.rel.setoid 𝒶 𝒷)

notation 𝒶 ` ⊕ₚ `:30 𝒷:29 := pointed_sum 𝒶 𝒷

def inl (a : α) : 𝒶 ⊕ₚ 𝒷 := @quotient.mk _ (rel.setoid _ _) (inl a)

def inr (b : β) : 𝒶 ⊕ₚ 𝒷 := @quotient.mk _ (rel.setoid _ _) (inr b)

lemma inl_injective : injective (inl 𝒶 𝒷) := sorry

lemma inr_injective : injective (inr 𝒶 𝒷) := sorry

lemma inl_eq_inr : inl 𝒶 𝒷 𝒶 = inr 𝒶 𝒷 𝒷 := sorry

variables {𝒶 𝒷 a b}

lemma inl_eq_inr_iff : inl 𝒶 𝒷 a = inr 𝒶 𝒷 b ↔ a = 𝒶 ∧ b = 𝒷 :=
begin
  split,
  sorry,
  rintro ⟨rfl, rfl⟩,
  exact inl_eq_inr _ _,
end

lemma inl_ne_inr_left (h : a ≠ 𝒶) : inl 𝒶 𝒷 a ≠ inr 𝒶 𝒷 b := sorry
lemma inl_ne_inr_right (h : b ≠ 𝒷) : inl 𝒶 𝒷 a ≠ inr 𝒶 𝒷 b := sorry

notation α ` ⊕ₚₚ `:30 β:29 := pointed_snd α ⊕ₚ pointed_fst β

section two_pointed
variables (α 𝒷) [two_pointed α] [two_pointed β]

instance two_pointed_left : two_pointed (pointed_snd α ⊕ₚ 𝒷) :=
{ fst := inl _ _ (pointed_fst α),
  snd := inr _ _ (pointed_snd β),
  fst_ne_snd := inl_ne_inr_left $ pointed_fst_ne_snd _ }

variables {α} (β 𝒶)

instance two_pointed_right : two_pointed (𝒶 ⊕ₚ pointed_fst β) :=
{ fst := inl _ _ (pointed_fst α),
  snd := inr _ _ (pointed_snd β),
  fst_ne_snd := inl_ne_inr_right $ pointed_snd_ne_fst _ }

end two_pointed

section lift_rel
variables (𝒶 𝒷) (r : α → α → Prop) (s : β → β → Prop)

inductive lift_rel : 𝒶 ⊕ₚ 𝒷 → 𝒶 ⊕ₚ 𝒷 → Prop
| inl {a b} : r a b → lift_rel (inl _ _ a) (inl _ _ b)
| inr {a b} : s a b → lift_rel (inr _ _ a) (inr _ _ b)

end lift_rel

section lift_trans_rel
variables (𝒶 𝒷) (r : α → α → Prop) (s : β → β → Prop)

inductive lift_trans_rel : 𝒶 ⊕ₚ 𝒷 → 𝒶 ⊕ₚ 𝒷 → Prop
| inl {a b} : r a b → lift_trans_rel (inl _ _ a) (inl _ _ b)
| inr {a b} : s a b → lift_trans_rel (inr _ _ a) (inr _ _ b)
| inl_inr {a b} : r a 𝒶 → s 𝒷 b → lift_trans_rel (inl _ _ a) (inr _ _ b)
| inr_inl {a b} : s b 𝒷 → r 𝒶 a → lift_trans_rel (inr _ _ b) (inl _ _ a)

variables {𝒶 𝒷 r s}

instance [is_refl α r] [is_refl β s] : is_refl (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
⟨λ x, begin
  sorry
end⟩

instance [is_irrefl α r] [is_irrefl β s] : is_irrefl (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
⟨λ a h, match a, h with
  | _, lift_trans_rel.inl h := sorry
  | _, lift_trans_rel.inr h := sorry
end⟩

@[trans] lemma lift_trans_rel.trans [is_trans α r] [is_trans β s] :
  ∀ {a b c}, lift_trans_rel 𝒶 𝒷 r s a b → lift_trans_rel 𝒶 𝒷 r s b c → lift_trans_rel 𝒶 𝒷 r s a c
-- | _ _ _ (lift_trans_rel.inl hab) (lift_trans_rel.inl hbc) := lift_trans_rel.inl $ trans hab hbc
-- | _ _ _ (lift_trans_rel.inr hab) (lift_trans_rel.inr hbc) := lift_trans_rel.inr $ trans hab hbc
:= sorry

instance [is_trans α r] [is_trans β s] : is_trans (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
⟨λ _ _ _, lift_trans_rel.trans _ _⟩

instance [is_antisymm α r] [is_antisymm β s] : is_antisymm (𝒶 ⊕ₚ 𝒷) (lift_trans_rel 𝒶 𝒷 r s) :=
⟨sorry⟩

end lift_trans_rel
end pointed_sum

open pointed_sum

/-- Two-points a bounded order at its bottom and top elements. -/
@[reducible] -- See note [reducible non instances]
def bounded_order.to_two_pointed [partial_order α] [bounded_order α] [nontrivial α] :
  two_pointed α :=
{ fst := ⊥,
  snd := ⊤,
  fst_ne_snd := bot_ne_top }

section order
variables (𝒶 : α) (𝒷 : β)

instance [has_le α] [has_le β] : has_le (𝒶 ⊕ₚ 𝒷) := ⟨lift_trans_rel _ _ (≤) (≤)⟩
instance [has_lt α] [has_lt β] : has_lt (𝒶 ⊕ₚ 𝒷) := ⟨lift_trans_rel _ _ (<) (<)⟩

instance [preorder α] [preorder β] : preorder (𝒶 ⊕ₚ 𝒷) :=
{ le := (≤),
  lt := (<),
  le_refl := refl_of (lift_trans_rel _ _ (≤) (≤)),
  le_trans := λ _ _ _, trans_of (lift_trans_rel _ _ (≤) (≤)),
  lt_iff_le_not_le := λ a b, begin
    sorry
  end }

instance [partial_order α] [partial_order β] : partial_order (𝒶 ⊕ₚ 𝒷) :=
{ le := (≤),
  lt := (<),
  le_antisymm := λ _ _, antisymm_of (lift_trans_rel _ _ (≤) (≤)) }

end order

/-! ### Twop -/

namespace category_theory

/-- The category of two-pointed types. -/
def Twop : Type* := bundled two_pointed

/-- A sq-coalgebra on a two-pointed type `α` is a map `α → α ⊕ₚₚ α`. -/
class sq_coalgebra (α : Type*) :=
[two_pointed : two_pointed α]
(double_map : α → α ⊕ₚₚ α)

/-- The category of sq-coalgebras. -/
def SqCoalgebra : Type* := bundled sq_coalgebra

end category_theory
