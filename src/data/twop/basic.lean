/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.field
import category_theory.concrete_category.bundled
import category_theory.functor
import category_theory.limits.shapes.terminal
import data.fintype.basic
import data.real.basic
import data.sum.basic
import order.bounded_order

/-!
# Pointed sum and two-pointed types

## TODO

`card (two_pointed α) = card α * (card α - 1)`
-/

open function set sum

variables {α β : Type*}

/-- Type-valued `nontrivial`. -/
class two_pointed (α : Type*) :=
(fst snd : α)
(fst_ne_snd : fst ≠ snd)

section two_pointed
variables (α) [two_pointed α] [two_pointed β]

/-- The first pointed element of a pointed type. -/
def pointed_fst : α := two_pointed.fst

/-- The second pointed element of a pointed type. -/
def pointed_snd : α := two_pointed.snd

lemma pointed_fst_ne_snd : pointed_fst α ≠ pointed_snd α := two_pointed.fst_ne_snd
lemma pointed_snd_ne_fst : pointed_snd α ≠ pointed_fst α := (pointed_fst_ne_snd _).symm

@[priority 100] -- See note [lower instance priority]
instance two_pointed.to_nontrivial : nontrivial α :=
⟨⟨pointed_fst α, pointed_snd α, pointed_fst_ne_snd α⟩⟩

/-- Swaps the two pointed elements. -/
def two_pointed_swap : two_pointed α := ⟨pointed_snd α, pointed_fst α, pointed_snd_ne_fst α⟩

instance : two_pointed bool := ⟨ff, tt, bool.ff_ne_tt⟩

end two_pointed

/-! ### Pointed sum -/

namespace pointed_sum
variables {𝒶 a : α} {𝒷 b : β} {x y z : α ⊕ β}

/-- Glues `sum.inl 𝒶` and `sum.inr 𝒷` and nothing else. -/
inductive rel (𝒶 : α) (𝒷 : β) : α ⊕ β → α ⊕ β → Prop
| refl (x : α ⊕ β) : rel x x
| inl_inr : rel (inl 𝒶) (inr 𝒷)
| inr_inl : rel (inr 𝒷) (inl 𝒶)

attribute [refl] rel.refl

@[symm] lemma rel.symm : rel 𝒶 𝒷 x y → rel 𝒶 𝒷 y x := by rintro (_ | _ | _); constructor

lemma rel_comm : rel 𝒶 𝒷 x y ↔ rel 𝒶 𝒷 y x := ⟨rel.symm, rel.symm⟩

@[trans] lemma rel.trans : ∀ {x y z}, rel 𝒶 𝒷 x y → rel 𝒶 𝒷 y z → rel 𝒶 𝒷 x z
| _ _ _ (rel.refl _) (rel.refl _)   := rel.refl _
| _ _ _ (rel.refl _) rel.inl_inr  := rel.inl_inr
| _ _ _ (rel.refl _) rel.inr_inl  := rel.inr_inl
| _ _ _ rel.inl_inr  (rel.refl _) := rel.inl_inr
| _ _ _ rel.inr_inl  (rel.refl _) := rel.inr_inl
| _ _ _ rel.inl_inr  rel.inr_inl  := rel.refl _
| _ _ _ rel.inr_inl  rel.inl_inr  := rel.refl _

lemma rel.equivalence : equivalence (rel 𝒶 𝒷) := by tidy; apply rel.trans; assumption

@[simp] lemma rel_inl_inl_iff {a b : α} : rel 𝒶 𝒷 (inl a) (inl b) ↔ a = b :=
⟨λ h, by { cases h, refl }, by { rintro rfl, exact rel.refl _ }⟩

@[simp] lemma rel_inl_inr_iff {a : α} {b : β} : rel 𝒶 𝒷 (inl a) (inr b) ↔ a = 𝒶 ∧ b = 𝒷 :=
⟨λ h, by { cases h, exact ⟨rfl, rfl⟩ }, by { rintro ⟨rfl, rfl⟩, exact rel.inl_inr }⟩

@[simp] lemma rel_inr_inl_iff {a : α} {b : β} : rel 𝒶 𝒷 (inr b) (inl a) ↔ a = 𝒶 ∧ b = 𝒷 :=
⟨λ h, by { cases h, exact ⟨rfl, rfl⟩ }, by { rintro ⟨rfl, rfl⟩, exact rel.inr_inl }⟩

@[simp] lemma rel_inr_inr_iff {a b : β} : rel 𝒶 𝒷 (inr a) (inr b) ↔ a = b :=
⟨λ h, by { cases h, refl }, by { rintro rfl, exact rel.refl _ }⟩

variables (𝒶 𝒷)

instance [decidable_eq α] [decidable_eq β] : decidable_rel (rel 𝒶 𝒷)
| (sum.inl a) (sum.inl b) := decidable_of_iff' _ rel_inl_inl_iff
| (sum.inl a) (sum.inr b) := decidable_of_iff' _ rel_inl_inr_iff
| (sum.inr a) (sum.inl b) := decidable_of_iff' _ rel_inr_inl_iff
| (sum.inr a) (sum.inr b) := decidable_of_iff' _ rel_inr_inr_iff

/-- The quotient of `α ⊕ β` by `sum.inl 𝒶 = sum.inr 𝒷`. -/
def rel.setoid : setoid (α ⊕ β) := ⟨rel 𝒶 𝒷, rel.equivalence⟩

/-- The sum of `α` and `β` pointed at `𝒶` and `𝒷`. -/
def _root_.pointed_sum : Type* := quotient (pointed_sum.rel.setoid 𝒶 𝒷)

notation 𝒶 ` ⊕ₚ `:30 𝒷:29 := pointed_sum 𝒶 𝒷

/-- The map to the left component of `𝒶 ⊕ₚ 𝒷`. -/
def inl (a : α) : 𝒶 ⊕ₚ 𝒷 := @quotient.mk _ (rel.setoid _ _) (inl a)

/-- The map to the right component of `𝒶 ⊕ₚ 𝒷`. -/
def inr (b : β) : 𝒶 ⊕ₚ 𝒷 := @quotient.mk _ (rel.setoid _ _) (inr b)

instance : inhabited (𝒶 ⊕ₚ 𝒷) := ⟨inl 𝒶 𝒷 𝒶⟩

instance [decidable_eq α] [decidable_eq β] : decidable_eq (𝒶 ⊕ₚ 𝒷) :=
@quotient.decidable_eq _ (pointed_sum.rel.setoid 𝒶 𝒷) $ rel.decidable_rel _ _

variables {𝒶 𝒷 a b}

@[simp] lemma inl_inj {b : α} : inl 𝒶 𝒷 a = inl 𝒶 𝒷 b ↔ a = b :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inl_inl_iff

@[simp] lemma inl_eq_inr_iff : inl 𝒶 𝒷 a = inr 𝒶 𝒷 b ↔ a = 𝒶 ∧ b = 𝒷 :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inl_inr_iff

@[simp] lemma inr_inj {a b : β} : inr 𝒶 𝒷 a = inr 𝒶 𝒷 b ↔ a = b :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inr_inr_iff

@[simp] lemma inr_eq_inl_iff : inr 𝒶 𝒷 b = inl 𝒶 𝒷 a ↔ a = 𝒶 ∧ b = 𝒷 :=
(@quotient.eq _ (rel.setoid 𝒶 𝒷) _ _).trans rel_inr_inl_iff

lemma inl_injective : injective (inl 𝒶 𝒷) := λ _ _, inl_inj.1
lemma inr_injective : injective (inr 𝒶 𝒷) := λ _ _, inr_inj.1

lemma inl_eq_inr : inl 𝒶 𝒷 𝒶 = inr 𝒶 𝒷 𝒷 := @quotient.sound _ (rel.setoid 𝒶 𝒷) _ _ rel.inl_inr
lemma inr_eq_inl : inr 𝒶 𝒷 𝒷 = inl 𝒶 𝒷 𝒶 := @quotient.sound _ (rel.setoid 𝒶 𝒷) _ _ rel.inr_inl

lemma inl_ne_inr_left (h : a ≠ 𝒶) : inl 𝒶 𝒷 a ≠ inr 𝒶 𝒷 b := λ hab, h (inl_eq_inr_iff.1 hab).1
lemma inl_ne_inr_right (h : b ≠ 𝒷) : inl 𝒶 𝒷 a ≠ inr 𝒶 𝒷 b := λ hab, h (inl_eq_inr_iff.1 hab).2

@[elab_as_eliminator]
protected lemma ind {f : 𝒶 ⊕ₚ 𝒷 → Prop} (h𝒶 : ∀ a, f (inl 𝒶 𝒷 a)) (h𝒷 : ∀ b, f (inr 𝒶 𝒷 b)) :
  ∀ i, f i :=
@quotient.ind _ (rel.setoid 𝒶 𝒷) _ $ by { refine sum.rec _ _, exacts [h𝒶, h𝒷] }

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

section fintype
variables (α 𝒷) [decidable_eq α] [decidable_eq β] [fintype α] [fintype β]

instance : fintype (𝒶 ⊕ₚ 𝒷) := @quotient.fintype _ _ (rel.setoid 𝒶 𝒷) $ rel.decidable_rel 𝒶 𝒷

lemma _root_.fintype.card_pointed_sum :
  fintype.card (𝒶 ⊕ₚ 𝒷) = fintype.card α + fintype.card β - 1 :=
begin
  sorry
end

end fintype

section lift_rel
variables (𝒶 𝒷) (r : α → α → Prop) (s : β → β → Prop)

/-- Lifts a relation to `𝒶 ⊕ₚ 𝒷` summand-wise. -/
inductive lift_rel : 𝒶 ⊕ₚ 𝒷 → 𝒶 ⊕ₚ 𝒷 → Prop
| inl {a b} : r a b → lift_rel (inl _ _ a) (inl _ _ b)
| inr {a b} : s a b → lift_rel (inr _ _ a) (inr _ _ b)

end lift_rel

section lift_trans_rel
variables (𝒶 𝒷) (r : α → α → Prop) (s : β → β → Prop)

/-- Lifts a relation to `𝒶 ⊕ₚ 𝒷` summand-wise while making sure it stays transitive. -/
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
  le_antisymm := λ _ _, antisymm_of (lift_trans_rel _ _ (≤) (≤)),
  .. pointed_sum.preorder 𝒶 𝒷 }

end order

/-! ### Twop -/

namespace category_theory
open limits

/-- The category of two-pointed types. -/
def Twop : Type* := bundled two_pointed

instance : inhabited Twop := ⟨bundled.of bool⟩

instance : category Twop :=
{ hom := λ α β, α.1 → β.1,
  id := λ α, id,
  comp := λ α β γ f g, g ∘ f }

def Twop.wedge : Twop × Twop ⥤ Twop := sorry

/-- A square coalgebra on a two-pointed type `α` is a map `α → α ⊕ₚₚ α`. -/
structure sq_coalgebra (α : Type*) :=
(two_pointed : two_pointed α)
(double_map : α → α ⊕ₚₚ α)

/-- `pointed_sum.inl` as a square coalgebra. -/
def sq_coalgebra.inl (α : Type*) [two_pointed α] : sq_coalgebra α := ⟨pointed_sum.inl _ _⟩

/-- `pointed_sum.inr` as a square coalgebra. -/
def sq_coalgebra.inr (α : Type*) [two_pointed α] : sq_coalgebra α := ⟨pointed_sum.inl _ _⟩

instance [two_pointed α] : inhabited (sq_coalgebra α) := ⟨sq_coalgebra.inl α⟩

/-- The category of square coalgebras. -/
def SqCoalgebra : Type* := bundled sq_coalgebra

instance : inhabited SqCoalgebra := ⟨@bundled.of _ bool default⟩

instance : category SqCoalgebra :=
{ hom := λ α β, α.1 → β.1,
  id := λ α, id,
  comp := λ α β γ f g, g ∘ f }

namespace SqCoalgebra

/-- The unit interval along with its doubling map as a square coalgebra. -/
def unit_interval (α : Type*) [linear_ordered_field α] : SqCoalgebra :=
{ α := Icc (0 : α) 1,
  str := begin
    refine ⟨⟨⟨0, left_mem_Icc.2 zero_le_one⟩, ⟨1, right_mem_Icc.2 zero_le_one⟩,
      ne_of_apply_ne subtype.val zero_ne_one⟩, λ a, if h : (a : α) ≤ 1/2 then _ else _⟩,
    sorry, sorry, -- insert doubling map here
  end }

lemma is_initial_unit_interval_ℚ : is_initial (unit_interval ℚ) := sorry

lemma is_terminal_unit_interval_ℝ : is_terminal (unit_interval ℝ) := sorry

end SqCoalgebra
end category_theory
