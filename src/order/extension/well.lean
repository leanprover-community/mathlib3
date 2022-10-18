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
