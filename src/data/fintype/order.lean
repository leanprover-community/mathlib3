/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
import data.fintype.lattice
import data.finset.order

/-!
# Order structures on finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides order instances on fintypes.

## Computable instances

On a `fintype`, we can construct
* an `order_bot` from `semilattice_inf`.
* an `order_top` from `semilattice_sup`.
* a `bounded_order` from `lattice`.

Those are marked as `def` to avoid defeqness issues.

## Completion instances

Those instances are noncomputable because the definitions of `Sup` and `Inf` use `set.to_finset` and
set membership is undecidable in general.

On a `fintype`, we can promote:
* a `lattice` to a `complete_lattice`.
* a `distrib_lattice` to a `complete_distrib_lattice`.
* a `linear_order`  to a `complete_linear_order`.
* a `boolean_algebra` to a `complete_boolean_algebra`.

Those are marked as `def` to avoid typeclass loops.

## Concrete instances

We provide a few instances for concrete types:
* `fin.complete_linear_order`
* `bool.complete_linear_order`
* `bool.complete_boolean_algebra`
-/

open finset

namespace fintype
variables {ι α : Type*} [fintype ι] [fintype α]

section nonempty
variables (α) [nonempty α]

/-- Constructs the `⊥` of a finite nonempty `semilattice_inf`. -/
@[reducible] -- See note [reducible non-instances]
def to_order_bot [semilattice_inf α] : order_bot α :=
{ bot := univ.inf' univ_nonempty id,
  bot_le := λ a, inf'_le _ $ mem_univ a }

/-- Constructs the `⊤` of a finite nonempty `semilattice_sup` -/
@[reducible] -- See note [reducible non-instances]
def to_order_top [semilattice_sup α] : order_top α :=
{ top := univ.sup' univ_nonempty id,
  le_top := λ a, le_sup' _ $ mem_univ a }

/-- Constructs the `⊤` and `⊥` of a finite nonempty `lattice`. -/
@[reducible] -- See note [reducible non-instances]
def to_bounded_order [lattice α] : bounded_order α := { ..to_order_bot α, ..to_order_top α }

end nonempty

section bounded_order
variables (α)

open_locale classical

/-- A finite bounded lattice is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def to_complete_lattice [lattice α] [bounded_order α] :
  complete_lattice α :=
{ Sup := λ s, s.to_finset.sup id,
  Inf := λ s, s.to_finset.inf id,
  le_Sup := λ _ _ ha, finset.le_sup (set.mem_to_finset.mpr ha),
  Sup_le := λ s _ ha, finset.sup_le (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  Inf_le := λ _ _ ha, finset.inf_le (set.mem_to_finset.mpr ha),
  le_Inf := λ s _ ha, finset.le_inf (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  .. ‹lattice α›, .. ‹bounded_order α› }

/-- A finite bounded distributive lattice is completely distributive. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def to_complete_distrib_lattice [distrib_lattice α] [bounded_order α] :
  complete_distrib_lattice α :=
{ infi_sup_le_sup_Inf := λ a s, begin
    convert (finset.inf_sup_distrib_left _ _ _).ge,
    convert (finset.inf_eq_infi _ _).symm,
    simp_rw set.mem_to_finset,
    refl,
  end,
  inf_Sup_le_supr_inf := λ a s, begin
    convert (finset.sup_inf_distrib_left _ _ _).le,
    convert (finset.sup_eq_supr _ _).symm,
    simp_rw set.mem_to_finset,
    refl,
  end,
  ..to_complete_lattice α }

/-- A finite bounded linear order is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def to_complete_linear_order [linear_order α] [bounded_order α] :
  complete_linear_order α :=
{ ..to_complete_lattice α, .. ‹linear_order α› }

/-- A finite boolean algebra is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def to_complete_boolean_algebra [boolean_algebra α] :
  complete_boolean_algebra α :=
{ ..fintype.to_complete_distrib_lattice α, .. ‹boolean_algebra α› }

end bounded_order

section nonempty
variables (α) [nonempty α]

/-- A nonempty finite lattice is complete. If the lattice is already a `bounded_order`, then use
`fintype.to_complete_lattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def to_complete_lattice_of_nonempty [lattice α] : complete_lattice α :=
@to_complete_lattice _ _ _ $ @to_bounded_order α _ ⟨classical.arbitrary α⟩ _

/-- A nonempty finite linear order is complete. If the linear order is already a `bounded_order`,
then use `fintype.to_complete_linear_order` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def to_complete_linear_order_of_nonempty [linear_order α] :
  complete_linear_order α :=
{ ..to_complete_lattice_of_nonempty α, .. ‹linear_order α› }

end nonempty
end fintype

/-! ### Concrete instances -/

noncomputable instance {n : ℕ} : complete_linear_order (fin (n + 1)) :=
fintype.to_complete_linear_order _

noncomputable instance : complete_linear_order bool := fintype.to_complete_linear_order _
noncomputable instance : complete_boolean_algebra bool := fintype.to_complete_boolean_algebra _

/-! ### Directed Orders -/
variable {α : Type*}

theorem directed.fintype_le {r : α → α → Prop} [is_trans α r]
  {β γ : Type*} [nonempty γ] {f : γ → α} [fintype β] (D : directed r f) (g : β → γ) :
  ∃ z, ∀ i, r (f (g i)) (f z) :=
begin
  classical,
  obtain ⟨z, hz⟩ := D.finset_le (finset.image g finset.univ),
  exact ⟨z, λ i, hz (g i) (finset.mem_image_of_mem g (finset.mem_univ i))⟩,
end

lemma fintype.exists_le [nonempty α] [preorder α] [is_directed α (≤)]
  {β : Type*} [fintype β] (f : β → α) :
  ∃ M, ∀ i, (f i) ≤ M :=
directed_id.fintype_le _

lemma fintype.bdd_above_range [nonempty α] [preorder α] [is_directed α (≤)]
  {β : Type*} [fintype β] (f : β → α) :
  bdd_above (set.range f) :=
begin
  obtain ⟨M, hM⟩ := fintype.exists_le f,
  refine ⟨M, λ a ha, _⟩,
  obtain ⟨b, rfl⟩ := ha,
  exact hM b,
end
