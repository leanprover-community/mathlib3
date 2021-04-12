/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/

import order.lattice
import data.fintype.basic

/-!
# Order structures on finite sets

This file shows that a `nonempty` `lattice` on a `fintype` gives a `complete_lattice`, and that a
`linear_order` on a nonempty `fintype` gives a `complete_linear_order`. The latter applies in
particular to `fin (n+1)`. Getting to a `bounded_lattice` from a `lattice` is computable, but the
subsequent definitions are not, since the definitions of `Sup` and `Inf` use `set.to_finset`, which
implicitly requires a `decidable_pred` instance for every `s : set α`.

An explicit instance is given for a `complete_lattice` on `fin (n+1)`, but the rest are given
as `def`s, to avoid loops in instance searches.
-/

/- The maximum element in a `fintype` -/
def fintype.top (α : Type*) [inhabited α] [fintype α] [semilattice_sup α] : α :=
  finset.fold (⊔) (arbitrary α) id finset.univ

/- The minimum element in a `fintype` -/
def fintype.bot (α : Type*) [inhabited α] [fintype α] [semilattice_inf α] : α :=
  finset.fold (⊓) (arbitrary α) id finset.univ

lemma fintype.bot_le (α : Type*) [inhabited α] [fintype α] [semilattice_inf α] (a : α) :
  fintype.bot α ≤ a :=
((@finset.fold_op_rel_iff_and
  _ _ (⊓) _ _ id (arbitrary α) finset.univ (≤) (λ _ _ _, le_inf_iff) (fintype.bot α )).mp le_rfl).2
    a (finset.mem_univ _)

lemma fintype.exists_bot (α : Type*) [i : nonempty α] [fintype α] [semilattice_inf α] :
  ∃ m, ∀ a : α, m ≤ a :=
⟨@fintype.bot α ⟨i.some⟩ _ _, @fintype.bot_le α ⟨i.some⟩ _ _⟩

lemma fintype.le_top (α : Type*) [inhabited α] [fintype α] [semilattice_sup α] (a : α) :
  a ≤ fintype.top α :=
(((@finset.fold_op_rel_iff_and _ _ (⊔) _ _ id (arbitrary α) finset.univ (λ x y, y ≤ x)
  (λ _ _ _, sup_le_iff) (fintype.top α))).mp le_rfl).2 a (finset.mem_univ a)

lemma fintype.exists_top (α : Type*) [i : nonempty α] [fintype α] [semilattice_sup α] :
  ∃ m, ∀ a : α, a ≤ m :=
⟨@fintype.top α ⟨i.some⟩ _ _, @fintype.le_top α ⟨i.some⟩ _ _⟩

def fintype.bounded_lattice (α : Type*) [inhabited α] [fintype α] [lattice α] :
  bounded_lattice α :=
{ bot := fintype.bot α,
  bot_le := fintype.bot_le α,
  top := fintype.top α,
  le_top := fintype.le_top α,
  .. (infer_instance : lattice α)}

open_locale classical

noncomputable def fintype.complete_lattice (α : Type*) [i : nonempty α] [fintype α] [lattice α] :
  complete_lattice α :=
let isb := (@semilattice_sup_bot_of_bounded_lattice α (@fintype.bounded_lattice α ⟨i.some⟩ _ _)),
    iit := (@semilattice_inf_top_of_bounded_lattice α (@fintype.bounded_lattice α ⟨i.some⟩ _ _)) in
{ Sup := λ s, @finset.sup _ _ isb s.to_finset id,
  Inf := λ s, @finset.inf _ _ iit s.to_finset id,
  le_Sup := λ _ _ ha, @finset.le_sup _ _ isb _ _ _ (set.mem_to_finset.mpr ha),
  Sup_le := λ s _ ha, @finset.sup_le _ _ isb s.to_finset _ _
    (λ b hb, ha _ (by rwa set.mem_to_finset at hb)),
  Inf_le := λ _ _ ha, @finset.inf_le _ _ iit _ _ _ (set.mem_to_finset.mpr ha),
  le_Inf := λ s _ ha, @finset.le_inf _ _ iit s.to_finset _ _
    (λ b hb, ha _ (by rwa set.mem_to_finset at hb)),
  ..(@fintype.bounded_lattice α ⟨i.some⟩ _ _)}

noncomputable def fintype.complete_linear_order_of_linear_order (α : Type*)
  [fintype α] [nonempty α] [linear_order α] :
  complete_linear_order α :=
{ ..fintype.complete_lattice α,
  ..(infer_instance : linear_order α) }

noncomputable instance {n : ℕ} : complete_linear_order (fin (n+1)) :=
  fintype.complete_linear_order_of_linear_order _

section

local attribute [instance] fintype.complete_lattice

/-- The `Sup` induced by `fintype.complete_semilattice` unfolds to `finset.sup`. -/
lemma fintype.Sup_eq {α : Type*} [nonempty α] [fintype α] [lattice α] (s : set α)
  [decidable_pred (∈ s)] : Sup s = s.to_finset.sup id :=
by {convert rfl}

/-- The `Sup` induced by `fintype.complete_semilattice` unfolds to `finset.sup`. -/
lemma fintype.Inf_eq {α : Type*} [nonempty α] [fintype α] [lattice α] (s : set α)
  [decidable_pred (∈ s)] : Inf s = s.to_finset.inf id :=
by {convert rfl}

end
