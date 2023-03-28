/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.card
import data.finset.lattice

/-!
# Lemmas relating fintypes and order/lattice structure.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open function
open_locale nat

universes u v

variables {α β γ : Type*}

namespace finset
variables [fintype α] {s : finset α}

/-- A special case of `finset.sup_eq_supr` that omits the useless `x ∈ univ` binder. -/
lemma sup_univ_eq_supr [complete_lattice β] (f : α → β) : finset.univ.sup f = supr f :=
(sup_eq_supr _ f).trans $ congr_arg _ $ funext $ λ a, supr_pos (mem_univ _)

/-- A special case of `finset.inf_eq_infi` that omits the useless `x ∈ univ` binder. -/
lemma inf_univ_eq_infi [complete_lattice β] (f : α → β) : finset.univ.inf f = infi f :=
sup_univ_eq_supr (by exact f : α → βᵒᵈ)

@[simp] lemma fold_inf_univ [semilattice_inf α] [order_bot α] (a : α) :
  finset.univ.fold (⊓) a (λ x, x) = ⊥ :=
eq_bot_iff.2 $ ((finset.fold_op_rel_iff_and $ @_root_.le_inf_iff α _).1 le_rfl).2 ⊥ $
  finset.mem_univ _

@[simp] lemma fold_sup_univ [semilattice_sup α] [order_top α] (a : α) :
  finset.univ.fold (⊔) a (λ x, x) = ⊤ :=
@fold_inf_univ αᵒᵈ ‹fintype α› _ _ _

end finset

open finset function

lemma finite.exists_max [finite α] [nonempty α] [linear_order β] (f : α → β) :
 ∃ x₀ : α, ∀ x, f x ≤ f x₀ :=
by { casesI nonempty_fintype α, simpa using exists_max_image univ f univ_nonempty }

lemma finite.exists_min [finite α] [nonempty α] [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x₀ ≤ f x :=
by { casesI nonempty_fintype α, simpa using exists_min_image univ f univ_nonempty }
