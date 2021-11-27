/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import data.fintype.basic

/-!
# Order structures on finite types

This file provides order instances on fintypes:
* A `semilattice_inf` instance on a `fintype` allows constructing an `order_bot`.
* A `semilattice_sup` instance on a `fintype` allows constructing an `order_top`.
* A `lattice` instance on a `fintype` allows constructing a `bounded_order`.
* A `lattice` instance on a `fintype` can be promoted to a `complete_lattice`.
* A `linear_order` instance on a `fintype` can be promoted to a `complete_linear_order`.

Getting to a `bounded_order` from a `lattice` is computable, but the
subsequent definitions are not, since the definitions of `Sup` and `Inf` use `set.to_finset`, which
implicitly requires a `decidable_pred` instance for every `s : set α`.

The `complete_linear_order` instance for `fin (n + 1)` is the only proper instance in this file. The
rest are `def`s to avoid loops in typeclass inference.
-/

section inhabited
variables (α : Type*) [inhabited α] [fintype α]

/-- Constructs the `⊥` of a finite inhabited `semilattice_inf`. -/
def fintype.to_order_bot [semilattice_inf α] : order_bot α :=
{ bot := finset.fold (⊓) (arbitrary α) id finset.univ,
  bot_le := λ a, ((finset.fold_op_rel_iff_and (@le_inf_iff α _)).1 le_rfl).2 a (finset.mem_univ _) }

/-- Constructs the `⊤` of a finite inhabited `semilattice_sup` -/
def fintype.to_order_top [semilattice_sup α] : order_top α :=
{ top := finset.fold (⊔) (arbitrary α) id finset.univ,
  le_top := λ a,
    ((finset.fold_op_rel_iff_and (λ x y z, show x ≥ y ⊔ z ↔ _, from sup_le_iff)).mp le_rfl).2
      a (finset.mem_univ a) }

/-- Constructs the `⊤` and `⊥` of a finite inhabited `lattice`. -/
def fintype.to_bounded_order [lattice α] : bounded_order α :=
{ .. fintype.to_order_bot α,
  .. fintype.to_order_top α }

variables {α}

local attribute [instance] fintype.to_order_bot
local attribute [instance] fintype.to_order_top

lemma fintype.fold_inf_univ [semilattice_inf α] : finset.univ.fold (⊓) (arbitrary α) id = ⊥ := rfl
lemma fintype.fold_sup_univ [semilattice_sup α] : finset.univ.fold (⊔) (arbitrary α) id = ⊤ := rfl

end inhabited

section nonempty
variables (α : Type*) [fintype α]

open_locale classical

/-- A finite bounded lattice is complete. -/
noncomputable def fintype.to_complete_lattice [hl : lattice α] [hb : bounded_order α] :
  complete_lattice α :=
{ Sup := λ s, s.to_finset.sup id,
  Inf := λ s, s.to_finset.inf id,
  le_Sup := λ _ _ ha, finset.le_sup (set.mem_to_finset.mpr ha),
  Sup_le := λ s _ ha, finset.sup_le (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  Inf_le := λ _ _ ha, finset.inf_le (set.mem_to_finset.mpr ha),
  le_Inf := λ s _ ha, finset.le_inf (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  .. hl, .. hb }

variables [nonempty α]

/-- A nonempty finite lattice is complete. If the lattice is already a `bounded_order`, then use
`fintype.to_complete_lattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
noncomputable def fintype.to_complete_lattice_of_lattice [lattice α] : complete_lattice α :=
@fintype.to_complete_lattice _ _ _ $ @fintype.to_bounded_order α ⟨classical.arbitrary α⟩ _ _

/-- A nonempty finite linear order is complete.

If the lattice is already a `bounded_order`, then build this object manually instead by combining
`fintype.to_complete_lattice` and an appropriate `linear_order` instance, as this gives definitional
equality for `⊥` and `⊤`. -/
noncomputable def fintype.to_complete_linear_order [h : linear_order α] : complete_linear_order α :=
{ .. fintype.to_complete_lattice_of_lattice α,
  .. h }

end nonempty

section decidable_Sup_Inf
variables {ι α : Type*} [fintype ι] [fintype α] [lattice α] [bounded_order α]

-- this line is crucially *after* the `variables` so that `bounded_order` gets filled in correctly
local attribute [instance] fintype.to_complete_lattice

/-- The `Sup` induced by `fintype.to_complete_lattice` unfolds to `finset.sup`. -/
lemma fintype.Sup_eq (s : set α) [decidable_pred (∈ s)] : Sup s = s.to_finset.sup id :=
by convert rfl

/-- The `Inf` induced by `fintype.to_complete_lattice` unfolds to `finset.inf`. -/
lemma fintype.Inf_eq (s : set α) [decidable_pred (∈ s)] : Inf s = s.to_finset.inf id :=
by convert rfl

/-- The `supr` induced by `fintype.to_complete_lattice` unfolds to `finset.sup`. -/
lemma fintype.supr_eq (f : ι → α) : supr f = finset.univ.sup f :=
begin
  classical,
  rw [supr, fintype.Sup_eq, set.to_finset_range, finset.sup_image, function.comp.left_id],
end

/-- The `infi` induced by `fintype.to_complete_lattice` unfolds to `finset.sup`. -/
lemma fintype.infi_eq (f : ι → α) : infi f = finset.univ.inf f :=
begin
  classical,
  rw [infi, fintype.Inf_eq, set.to_finset_range, finset.inf_image, function.comp.left_id],
end

end decidable_Sup_Inf

/-! ### `fin` -/

variables {ι : Type*} [fintype ι] {n : ℕ}

noncomputable instance fin.complete_linear_order : complete_linear_order (fin (n + 1)) :=
{ .. fintype.to_complete_lattice _,
  .. fin.linear_order }

/-- The `Sup` induced by `fintype.to_complete_lattice` unfolds to `finset.sup`. -/
lemma fin.Sup_eq (s : set (fin (n + 1))) [decidable_pred (∈ s)] : Sup s = s.to_finset.sup id :=
fintype.Sup_eq s

/-- The `Inf` induced by `fintype.to_complete_lattice` unfolds to `finset.inf`. -/
lemma fin.Inf_eq (s : set (fin (n + 1))) [decidable_pred (∈ s)] : Inf s = s.to_finset.inf id :=
fintype.Inf_eq s

/-- The `supr` induced by `fintype.to_complete_lattice` unfolds to `finset.sup`. -/
lemma fin.supr_eq (f : ι → (fin (n + 1))) : supr f = finset.univ.sup f := fintype.supr_eq _

/-- The `infi` induced by `fintype.to_complete_lattice` unfolds to `finset.sup`. -/
lemma fin.infi_eq (f : ι → (fin (n + 1))) : infi f = finset.univ.inf f := fintype.infi_eq _
