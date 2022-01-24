/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sum.basic
import logic.nontrivial

/-!
# Two-pointed types

This file defines `two_pointed`, a class holding a two-pointing of a type.

This is morally a Type-valued `nontrivial`.
-/

open function

variables {α β : Type*}

/-- Two-pointing of a type. Type-valued `nontrivial`. -/
class two_pointed (α : Type*) :=
(fst snd : α)
(fst_ne_snd : fst ≠ snd)

variables (α) [two_pointed α]

/-- The first pointed element of a pointed type. -/
def pointed_fst : α := two_pointed.fst

/-- The second pointed element of a pointed type. -/
def pointed_snd : α := two_pointed.snd

lemma pointed_fst_ne_snd : pointed_fst α ≠ pointed_snd α := two_pointed.fst_ne_snd
lemma pointed_snd_ne_fst : pointed_snd α ≠ pointed_fst α := (pointed_fst_ne_snd _).symm

/-- Swaps the two pointed elements. -/
def two_pointed_swap : two_pointed α := ⟨pointed_snd α, pointed_fst α, pointed_snd_ne_fst α⟩

@[priority 100] -- See note [lower instance priority]
instance two_pointed.to_nontrivial : nontrivial α :=
⟨⟨pointed_fst α, pointed_snd α, pointed_fst_ne_snd α⟩⟩

namespace pi
variables [nonempty β]

instance : two_pointed (β → α) :=
{ fst := λ _, pointed_fst α,
  snd := λ _, pointed_snd α,
  fst_ne_snd := λ h, pointed_fst_ne_snd α $ by convert congr_fun h (classical.arbitrary β) }

@[simp] protected lemma pointed_fst : pointed_fst (β → α) = const β (pointed_fst α) := rfl
@[simp] protected lemma pointed_snd : pointed_snd (β → α) = const β (pointed_snd α) := rfl

end pi

namespace prod
variables [two_pointed β]

instance : two_pointed (α × β) :=
{ fst := (pointed_fst α, pointed_fst β),
  snd := (pointed_snd α, pointed_snd β),
  fst_ne_snd := λ h, pointed_fst_ne_snd _ (congr_arg prod.fst h) }

@[simp] protected lemma pointed_fst : pointed_fst (α × β) = (pointed_fst α, pointed_fst β) := rfl
@[simp] protected lemma pointed_snd : pointed_snd (α × β) = (pointed_snd α, pointed_snd β) := rfl

end prod

namespace sum
variables [two_pointed β]

instance : two_pointed (α ⊕ β) := ⟨inl (pointed_fst α), inr (pointed_snd β), inl_ne_inr⟩

@[simp] protected lemma pointed_fst : pointed_fst (α ⊕ β) = inl (pointed_fst α) := rfl
@[simp] protected lemma pointed_snd : pointed_snd (α ⊕ β) = inr (pointed_snd β) := rfl

end sum

instance : two_pointed bool := ⟨ff, tt, bool.ff_ne_tt⟩
instance : two_pointed Prop := ⟨false, true, false_ne_true⟩
