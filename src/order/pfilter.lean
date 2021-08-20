/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
import order.ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections
require more structure, such as a bottom element, a top element, or
a join-semilattice structure.

- `order.pfilter P`: The type of nonempty, downward directed, upward closed
               subsets of `P`. This is dual to `order.ideal`, so it
               simply wraps `order.ideal (order_dual P)`.
- `order.is_pfilter P`: a predicate for when a `set P` is a filter.


Note the relation between `order/filter` and `order/pfilter`: for any
type `α`, `filter α` represents the same mathematical object as
`pfilter (set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/

namespace order

variables {P : Type*}

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure pfilter (P) [preorder P] :=
(dual : ideal (order_dual P))

/-- A predicate for when a subset of `P` is a filter. -/
def is_pfilter [preorder P] (F : set P) : Prop :=
@is_ideal (order_dual P) _ F

lemma is_pfilter.of_def [preorder P] {F : set P} (nonempty : F.nonempty)
  (directed : directed_on (≥) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) : is_pfilter F :=
by { use [nonempty, directed], exact λ _ _ _ _, mem_of_le ‹_› ‹_› }

/-- Create an element of type `order.pfilter` from a set satisfying the predicate
`order.is_pfilter`. -/
def is_pfilter.to_pfilter [preorder P] {F : set P} (h : is_pfilter F) : pfilter P :=
⟨h.to_ideal⟩

namespace pfilter

section preorder
variables [preorder P] {x y : P} (F : pfilter P)

/-- A filter on `P` is a subset of `P`. -/
instance : has_coe (pfilter P) (set P) := ⟨λ F, F.dual.carrier⟩

/-- For the notation `x ∈ F`. -/
instance : has_mem P (pfilter P) := ⟨λ x F, x ∈ (F : set P)⟩

@[simp] lemma mem_coe : x ∈ (F : set P) ↔ x ∈ F := iff_of_eq rfl

lemma is_pfilter : is_pfilter (F : set P) :=
F.dual.is_ideal

lemma nonempty : (F : set P).nonempty := F.dual.nonempty

lemma directed : directed_on (≥) (F : set P) := F.dual.directed

lemma mem_of_le {F : pfilter P} : x ≤ y → x ∈ F → y ∈ F := λ h, F.dual.mem_of_le h

/-- The smallest filter containing a given element. -/
def principal (p : P) : pfilter P := ⟨ideal.principal p⟩

instance [inhabited P] : inhabited (pfilter P) := ⟨⟨default _⟩⟩

/-- Two filters are equal when their underlying sets are equal. -/
@[ext] lemma ext : ∀ (F G : pfilter P), (F : set P) = G → F = G
| ⟨⟨_, _, _, _⟩⟩ ⟨⟨_, _, _, _⟩⟩ rfl := rfl

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance : partial_order (pfilter P) := partial_order.lift coe ext

@[trans] lemma mem_of_mem_of_le {F G : pfilter P} : x ∈ F → F ≤ G → x ∈ G :=
ideal.mem_of_mem_of_le

@[simp] lemma principal_le_iff {F : pfilter P} : principal x ≤ F ↔ x ∈ F :=
ideal.principal_le_iff

end preorder

section order_top
variables [order_top P] {F : pfilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp] lemma top_mem : ⊤ ∈ F :=
ideal.bot_mem

/-- There is a bottom filter when `P` has a top element. -/
instance : order_bot (pfilter P) :=
{ bot := ⟨⊥⟩,
  bot_le := λ F, (bot_le : ⊥ ≤ F.dual),
  .. pfilter.partial_order }

end order_top

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [order_bot P] : order_top (pfilter P) :=
{ top := ⟨⊤⟩,
  le_top := λ F, (le_top : F.dual ≤ ⊤),
  .. pfilter.partial_order }

section semilattice_inf
variables [semilattice_inf P] {x y : P} {F : pfilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
lemma inf_mem (x y ∈ F) : x ⊓ y ∈ F :=
ideal.sup_mem x y ‹x ∈ F› ‹y ∈ F›

@[simp] lemma inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F :=
ideal.sup_mem_iff

end semilattice_inf

end pfilter

end order
