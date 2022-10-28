/-
Copyright (c) 2022 Yaël Dillies, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Junyan Xu
-/
import data.prod.lex
import set_theory.ordinal.arithmetic

/-!
# Extend a well-founded order to a well-order

This file constructs a well-order (linear well-founded order) which is an extension of a given
well-founded order.

## Proof idea

Because our order `r : α → α → Prop` is well-founded, we can define its *rank* function
`rank : α → ordinal`. We can also find a (not necessarily well-founded) extension `s` of `r`. Then
we can define `a < b` as `rank a < rank b ∨ (rank a = rank b ∧ s a b)`.
-/

universe u

variables {α : Type u} {r : α → α → Prop}

namespace well_founded
variable (hwf : well_founded r)
include hwf

/-- An arbitrary well order on `α` that extends `r`. -/
noncomputable def well_order_extension : linear_order α :=
let l : linear_order α := is_well_order.linear_order well_ordering_rel in by exactI
  @linear_order.lift' α (ordinal ×ₗ α) _ (λ a : α, (hwf.rank a, a)) (λ _ _, congr_arg prod.snd)

instance well_order_extension.is_well_founded_lt : is_well_founded α hwf.well_order_extension.lt :=
⟨inv_image.wf _ $ prod.lex_wf ordinal.well_founded_lt.wf well_ordering_rel.is_well_order.wf⟩

/-- Any well-founded relation can be extended to a well-ordering on that type. -/
lemma exists_well_order_ge : ∃ s, r ≤ s ∧ is_well_order α s :=
⟨hwf.well_order_extension.lt, λ a b h, prod.lex.left _ _ (hwf.rank_lt_of_rel h), by split⟩

end well_founded

/-- A type alias for `α`, intended to extend a well-founded order on `α` to a well-order. -/
def well_order_extension (α) : Type* := α

/-- "Identity" equivalence between a well-founded order and its well-order extension. -/
def to_well_order_extension : α ≃ well_order_extension α := equiv.refl _

noncomputable instance [has_lt α] [well_founded_lt α] : linear_order (well_order_extension α) :=
(is_well_founded.wf : @well_founded α (<)).well_order_extension

instance well_order_extension.well_founded_lt [has_lt α] [well_founded_lt α] :
  @well_founded_lt (well_order_extension α)
    (@preorder.to_has_lt _ $ @partial_order.to_preorder _ $ @linear_order.to_partial_order _ $
      @well_order_extension.linear_order _ _ _) :=
well_founded.well_order_extension.is_well_founded_lt _

lemma to_well_order_extension_strict_mono [preorder α] [well_founded_lt α] :
  @strict_mono _ _ _ (@partial_order.to_preorder _ $ @linear_order.to_partial_order _ $
    @well_order_extension.linear_order _ _ _)
      (to_well_order_extension : α → well_order_extension α) :=
λ a b h, prod.lex.left _ _ $ well_founded.rank_lt_of_rel _ h
