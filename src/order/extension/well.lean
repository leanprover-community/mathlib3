/-
Copyright (c) 2022 Yaël Dillies, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Junyan Xu
-/
import data.prod.lex
import set_theory.ordinal.arithmetic

/-!
# Extend a well-founded order to a well-order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file constructs a well-order (linear well-founded order) which is an extension of a given
well-founded order.

## Proof idea

We can map our order into two well-orders:
* the first map respects the order but isn't necessarily injective. Namely, this is the *rank*
  function `rank : α → ordinal`.
* the second map is injective but doesn't necessarily respect the order. This is an arbitrary
  well-order on `α`.

Then their lexicographic product is a well-founded linear order which our original order injects in.
-/

universe u

variables {α : Type u} {r : α → α → Prop}

namespace well_founded
variable (hwf : well_founded r)
include hwf

/-- An arbitrary well order on `α` that extends `r`.

The construction maps `r` into two well-orders: the first map is `well_founded.rank`, which is not
necessarily injective but respects the order `r`; the other map is the identity (with an arbitrarily
chosen well-order on `α`), which is injective but doesn't respect `r`.

By taking the lexicographic product of the two, we get both properties, so we can pull it back and
get an well-order that extend our original order `r`. Another way to view this is that we choose an
arbitrary well-order to serve as a tiebreak between two elements of same rank.
-/
noncomputable def well_order_extension : linear_order α :=
let l : linear_order α := is_well_order.linear_order well_ordering_rel in by exactI
  @linear_order.lift' α (ordinal ×ₗ α) _
    (λ a : α, (well_founded.rank.{u} hwf a, a)) (λ _ _, congr_arg prod.snd)

instance well_order_extension.is_well_founded_lt : is_well_founded α hwf.well_order_extension.lt :=
⟨inv_image.wf _ $ prod.lex_wf ordinal.well_founded_lt.wf well_ordering_rel.is_well_order.wf⟩

/-- Any well-founded relation can be extended to a well-ordering on that type. -/
lemma exists_well_order_ge : ∃ s, r ≤ s ∧ is_well_order α s :=
⟨hwf.well_order_extension.lt, λ a b h, prod.lex.left _ _ (hwf.rank_lt_of_rel h), by split⟩

end well_founded

/-- A type alias for `α`, intended to extend a well-founded order on `α` to a well-order. -/
def well_order_extension (α) : Type* := α

instance [inhabited α] : inhabited (well_order_extension α) := ‹inhabited (well_order_extension α)›

/-- "Identity" equivalence between a well-founded order and its well-order extension. -/
def to_well_order_extension : α ≃ well_order_extension α := equiv.refl _

noncomputable instance [has_lt α] [well_founded_lt α] : linear_order (well_order_extension α) :=
(is_well_founded.wf : @well_founded α (<)).well_order_extension

instance well_order_extension.well_founded_lt [has_lt α] [well_founded_lt α] :
  well_founded_lt (well_order_extension α) :=
well_founded.well_order_extension.is_well_founded_lt _

lemma to_well_order_extension_strict_mono [preorder α] [well_founded_lt α] :
  strict_mono (to_well_order_extension : α → well_order_extension α) :=
λ a b h, prod.lex.left _ _ $ well_founded.rank_lt_of_rel _ h
