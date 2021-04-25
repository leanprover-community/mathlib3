/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/

import order.lattice
import data.fintype.basic
import order.category.NonemptyFinLinOrd

/-!
# Order structures on finite sets

This file shows that a `nonempty` `lattice` on a `fintype` gives a `complete_lattice`, and that a
`linear_order` on a nonempty `fintype` gives a `complete_linear_order`. The latter applies in
particular to `fin (n+1)`. Getting to a `bounded_lattice` from a `lattice` is computable, but the
subsequent definitions are not, since the definitions of `Sup` and `Inf` use `set.to_finset`, which
implicitly requires a `decidable_pred` instance for every `s : set α`.

An explicit instance is given for a `complete_linear_order` on `fin (n+1)`, but the rest are given
as `def`s, to avoid loops in instance searches.
-/

section to_bot_top

/-- a finite inhabited `semilattice_inf` has a `⊥` -/
def fintype.semilattice_inf_bot (α : Type*) [inhabited α] [fintype α] [semilattice_inf α] :
  semilattice_inf_bot α :=
let bot := finset.fold (⊓) (arbitrary α) id finset.univ in
{ bot := bot,
  bot_le := λ a, ((@finset.fold_op_rel_iff_and _ _ (⊓) _ _ _ _ _ _
    (λ _ _ _, le_inf_iff) bot).mp le_rfl).2 a (finset.mem_univ _),
  .. (infer_instance : semilattice_inf α)}

/-- a finite inhabited `semilattice_sup` has a `⊤` -/
def fintype.semilattice_sup_top (α : Type*) [inhabited α] [fintype α] [semilattice_sup α] :
  semilattice_sup_top α :=
let top := finset.fold (⊔) (arbitrary α) id finset.univ in
{ top := top,
  le_top := λ a, (((@finset.fold_op_rel_iff_and _ _ (⊔) _ _ _ (arbitrary α) _ (λ x y, y ≤ x)
  (λ _ _ _, sup_le_iff) top )).mp le_rfl).2 a (finset.mem_univ a),
  .. (infer_instance : semilattice_sup α)}

/-- An inhabited finite `lattice` is bounded  -/
def fintype.bounded_lattice (α : Type*) [inhabited α] [fintype α] [lattice α] :
  bounded_lattice α :=
{ .. fintype.semilattice_inf_bot α,
  .. fintype.semilattice_sup_top α}

end to_bot_top

section bot_top_eq

local attribute [instance] fintype.semilattice_inf_bot

lemma fintype.bot_eq {α : Type*} [inhabited α] [fintype α] [semilattice_inf α] :
  ⊥ = finset.fold (⊓) (arbitrary α) id finset.univ :=
rfl

local attribute [instance] fintype.semilattice_sup_top

lemma fintype.top_eq {α : Type*} [inhabited α] [fintype α] [semilattice_sup α] :
  ⊤ = finset.fold (⊔) (arbitrary α) id finset.univ :=
rfl

end bot_top_eq

section complete

open_locale classical

/-- A finite bounded lattice is complete -/
noncomputable def fintype.complete_lattice (α : Type*) [fintype α] [h : bounded_lattice α] :
  complete_lattice α :=
{ Sup := λ s, s.to_finset.sup id,
  Inf := λ s, s.to_finset.inf id,
  le_Sup := λ _ _ ha, finset.le_sup (set.mem_to_finset.mpr ha),
  Sup_le := λ s _ ha, finset.sup_le (λ b hb, ha _ (set.mem_to_finset.mp hb)),
  Inf_le := λ _ _ ha, finset.inf_le (set.mem_to_finset.mpr ha),
  le_Inf := λ s _ ha, finset.le_inf (λ b hb, ha _ (set.mem_to_finset.mp hb)),
  ..h}

/-- A nonempty finite lattice is complete. If the lattice is already a `bounded_lattice`, then use
`fintype.complete_lattice` instead, as this gives definitional equality for `⊥` and `⊤` -/
noncomputable def fintype.complete_lattice_of_lattice (α : Type*) [fintype α] [i : nonempty α]
  [lattice α] : complete_lattice α :=
@fintype.complete_lattice _ _ (@fintype.bounded_lattice α ⟨i.some⟩ _ _)

/-- A nonempty finite linear order is complete.

If the lattice is already a `bounded_lattice`, then build this object manually instead by combining
`fintype.complete_lattice` and an appropriate `linear_order` instance, as this gives definitional
equality for `⊥` and `⊤` -/
noncomputable def fintype.complete_linear_order (α : Type*)
  [fintype α] [nonempty α] [linear_order α] : complete_linear_order α :=
{ .. fintype.complete_lattice_of_lattice α,
  .. (infer_instance : linear_order α) }

noncomputable instance fin.complete_linear_order {n : ℕ} : complete_linear_order (fin (n+1)) :=
{ .. fintype.complete_lattice (fin (n+1)),
  .. (infer_instance : linear_order (fin (n+1)))}

end complete

section decidable_Sup_Inf

local attribute [instance] fintype.complete_lattice

/-- The `Sup` induced by `fintype.complete_semilattice` unfolds to `finset.sup`. -/
lemma fintype.Sup_eq {α : Type*} [fintype α] [bounded_lattice α] (s : set α)
  [decidable_pred (∈ s)] : Sup s = s.to_finset.sup id :=
by {convert rfl}

/-- The `Inf` induced by `fintype.complete_semilattice` unfolds to `finset.inf`. -/
lemma fintype.Inf_eq {α : Type*} [fintype α] [bounded_lattice α] (s : set α)
  [decidable_pred (∈ s)] : Inf s = s.to_finset.inf id :=
by {convert rfl}

end decidable_Sup_Inf
