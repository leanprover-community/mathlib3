/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.cover
import order.locally_finite
import order.zorn

/-!
# Ranked -/

open finset

variables {α : Type*}

class rank_order (α : Type*) [preorder α] [order_bot α] :=
(rank : α → ℕ)
(rank_bot : rank ⊥ = 0)
(rank_covers {a b : α} (h : covers a b) : rank b = rank a + 1)

section preorder
variables [partial_order α] [order_bot α] [rank_order α] {a b : α}

def rank (a : α) : ℕ := rank_order.rank a

lemma rank_bot : rank (⊥ : α) = 0 := rank_order.rank_bot

protected lemma covers.rank (h : covers a b) : rank b = rank a + 1 := rank_order.rank_covers h

end preorder

section partial_order
variables [partial_order α] [order_bot α] [locally_finite_order α] [rank_order α] {s : finset α}
  {a b : α}

lemma card_Ico_eq_rank_sub_rank (a b : α) : (Ico a b).card = rank b - rank

end partial_order

section linear_order
variables [linear_order α] [order_bot α] [locally_finite_order α] {a b : α}

lemma card_Ico_eq_rank_sub_rank (a b : α) : (Ico a b).card = rank b - rank


end linear_order
