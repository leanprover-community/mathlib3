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

variables {ι α : Type*} [fintype ι] [fintype α]

section inhabited
variables (α) [inhabited α]

/-- Constructs the `⊥` of a finite inhabited `semilattice_inf`. -/
@[reducible] -- See note [reducible non-instances]
def fintype.to_order_bot [semilattice_inf α] : order_bot α :=
{ bot := finset.fold (⊓) (arbitrary α) id finset.univ,
  bot_le := λ a, ((finset.fold_op_rel_iff_and (@le_inf_iff α _)).1 le_rfl).2 a (finset.mem_univ _) }

/-- Constructs the `⊤` of a finite inhabited `semilattice_sup` -/
@[reducible] -- See note [reducible non-instances]
def fintype.to_order_top [semilattice_sup α] : order_top α :=
{ top := finset.fold (⊔) (arbitrary α) id finset.univ,
  le_top := λ a,
    ((finset.fold_op_rel_iff_and (λ x y z, show x ≥ y ⊔ z ↔ _, from sup_le_iff)).mp le_rfl).2
      a (finset.mem_univ a) }

/-- Constructs the `⊤` and `⊥` of a finite inhabited `lattice`. -/
@[reducible] -- See note [reducible non-instances]
def fintype.to_bounded_order [lattice α] : bounded_order α :=
{ .. fintype.to_order_bot α,
  .. fintype.to_order_top α }

end inhabited

section bounded_order
variables (α)

open_locale classical

/-- A finite bounded lattice is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_lattice [hl : lattice α] [hb : bounded_order α] :
  complete_lattice α :=
{ Sup := λ s, s.to_finset.sup id,
  Inf := λ s, s.to_finset.inf id,
  le_Sup := λ _ _ ha, finset.le_sup (set.mem_to_finset.mpr ha),
  Sup_le := λ s _ ha, finset.sup_le (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  Inf_le := λ _ _ ha, finset.inf_le (set.mem_to_finset.mpr ha),
  le_Inf := λ s _ ha, finset.le_inf (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  .. hl, .. hb }

/-- A finite bounded linear order is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_linear_order [h : linear_order α] [bounded_order α] :
  complete_linear_order α :=
{ .. fintype.to_complete_lattice α, .. h }

end bounded_order

section nonempty
variables (α) [nonempty α]

/-- A nonempty finite lattice is complete. If the lattice is already a `bounded_order`, then use
`fintype.to_complete_lattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_lattice_of_lattice [lattice α] : complete_lattice α :=
@fintype.to_complete_lattice _ _ _ $ @fintype.to_bounded_order α _ ⟨classical.arbitrary α⟩ _

/-- A nonempty finite linear order is complete. If the linear order is already a `bounded_order`,
then use `fintype.to_complete_linear_order` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_linear_order_of_linear_order [h : linear_order α] :
  complete_linear_order α :=
{ .. fintype.to_complete_lattice_of_lattice α,
  .. h }

end nonempty

/-! ### `fin` -/

noncomputable instance fin.complete_linear_order {n : ℕ} : complete_linear_order (fin (n + 1)) :=
fintype.to_complete_linear_order _
