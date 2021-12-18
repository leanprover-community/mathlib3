/-
Copyright (c) 2021 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import order.monotone

/-!
# Monovariance of functions

Two functions *vary together* if a strict change in the first implies a change in the second.

This is in some sense a way to say that two functions `f : ι → α`, `g : ι → β` are "monotone
together", without actually having an order on `ι`.

This condition comes up in the rearrangement inequality. See `algebra.order.rearrangement`.

## Main declarations

* `monovary f g`: `f` monovaries with `g`. If `g i < g j`, then `f i ≤ f j`.
* `antivary f g`: `f` antivaries with `g`. If `g i < g j`, then `f j ≤ f i`.
-/

open function

variables {ι α β γ : Type*}

section preorder
variables [preorder α] [preorder β] {f : ι → α} {g : ι → β}

/--  `f` monovaries with `g` if `g i < g j` implies `f i ≤ f j`. -/
def monovary (f : ι → α) (g : ι → β) : Prop := ∀ ⦃i j⦄, g i < g j → f i ≤ f j

/--  `f` antivaries with `g` if `g i < g j` implies `f j ≤ f i`. -/
def antivary (f : ι → α) (g : ι → β) : Prop := ∀ ⦃i j⦄, g i < g j → f j ≤ f i

lemma monovary_const_left (g : ι → β) (a : α) : monovary (const ι a) g := λ i j _, le_rfl
lemma antivary_const_left (g : ι → β) (a : α) : antivary (const ι a) g := λ i j _, le_rfl
lemma monovary_const_right (f : ι → α) (b : β) : monovary f (const ι b) := λ i j h, (h.ne rfl).elim
lemma antivary_const_right (f : ι → α) (b : β) : antivary f (const ι b) := λ i j h, (h.ne rfl).elim

section order_dual
open order_dual

lemma monovary.dual (h : monovary f g) : monovary (to_dual ∘ f) (to_dual ∘ g) := λ i j hij, h hij
lemma antivary.dual (h : antivary f g) : antivary (to_dual ∘ f) (to_dual ∘ g) := λ i j hij, h hij
lemma monovary.dual_left (h : monovary f g) : antivary (to_dual ∘ f) g := λ i j hij, h hij
lemma antivary.dual_left (h : antivary f g) : monovary (to_dual ∘ f) g := λ i j hij, h hij
lemma monovary.dual_right (h : monovary f g) : antivary f (to_dual ∘ g) := λ i j hij, h hij
lemma antivary.dual_right (h : antivary f g) : monovary f (to_dual ∘ g) := λ i j hij, h hij

end order_dual

variables [linear_order ι]

protected lemma monotone.monovary (hf : monotone f) (hg : monotone g) : monovary f g :=
λ i j hij, hf (hg.reflect_lt hij).le

protected lemma monotone.antivary (hf : monotone f) (hg : antitone g) : antivary f g :=
(hf.monovary hg.dual_right).dual_right

protected lemma antitone.monovary (hf : antitone f) (hg : antitone g) : monovary f g :=
(hf.dual_right.antivary hg).dual_left

protected lemma antitone.antivary (hf : antitone f) (hg : monotone g) : antivary f g :=
(hf.monovary hg.dual_right).dual_right

end preorder

section linear_order
variables [preorder α] [linear_order β] {f : ι → α} {g : ι → β}

protected lemma monovary.symm (h : monovary f g) : monovary g f :=
λ i j hf, le_of_not_lt $ λ hg, hf.not_le $ h hg

protected lemma antivary.symm (h : antivary f g) : antivary g f :=
λ i j hf, le_of_not_lt $ λ hg, hf.not_le $ h hg

end linear_order

section linear_order
variables [linear_order α] [linear_order β] {f : ι → α} {g : ι → β}

protected lemma monovary_comm : monovary f g ↔ monovary g f := ⟨monovary.symm, monovary.symm⟩

protected lemma antivary_comm : antivary f g ↔ antivary g f := ⟨antivary.symm, antivary.symm⟩

end linear_order
