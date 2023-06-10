/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
import order.ideal

/-!
# Order filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections
require more structure, such as a bottom element, a top element, or
a join-semilattice structure.

- `order.pfilter P`: The type of nonempty, downward directed, upward closed
               subsets of `P`. This is dual to `order.ideal`, so it
               simply wraps `order.ideal Pᵒᵈ`.
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
(dual : ideal Pᵒᵈ)

/-- A predicate for when a subset of `P` is a filter. -/
def is_pfilter [preorder P] (F : set P) : Prop :=
@is_ideal Pᵒᵈ _ F

lemma is_pfilter.of_def [preorder P] {F : set P} (nonempty : F.nonempty)
  (directed : directed_on (≥) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) : is_pfilter F :=
⟨λ _ _ _ _, mem_of_le ‹_› ‹_›,  nonempty, directed⟩

/-- Create an element of type `order.pfilter` from a set satisfying the predicate
`order.is_pfilter`. -/
def is_pfilter.to_pfilter [preorder P] {F : set P} (h : is_pfilter F) : pfilter P :=
⟨h.to_ideal⟩

namespace pfilter

section preorder
variables [preorder P] {x y : P} (F s t : pfilter P)

instance [inhabited P] : inhabited (pfilter P) := ⟨⟨default⟩⟩

/-- A filter on `P` is a subset of `P`. -/
instance : has_coe (pfilter P) (set P) := ⟨λ F, F.dual.carrier⟩

/-- For the notation `x ∈ F`. -/
instance : has_mem P (pfilter P) := ⟨λ x F, x ∈ (F : set P)⟩

@[simp] lemma mem_coe : x ∈ (F : set P) ↔ x ∈ F := iff_of_eq rfl

lemma is_pfilter : is_pfilter (F : set P) :=
F.dual.is_ideal

lemma nonempty : (F : set P).nonempty := F.dual.nonempty

lemma directed : directed_on (≥) (F : set P) := F.dual.directed

lemma mem_of_le {F : pfilter P} : x ≤ y → x ∈ F → y ∈ F := λ h, F.dual.lower h

/-- Two filters are equal when their underlying sets are equal. -/
@[ext] lemma ext (h : (s : set P) = t) : s = t :=
by { cases s, cases t, exact congr_arg _ (ideal.ext h) }

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance : partial_order (pfilter P) := partial_order.lift coe ext

@[trans] lemma mem_of_mem_of_le {F G : pfilter P} : x ∈ F → F ≤ G → x ∈ G :=
ideal.mem_of_mem_of_le

/-- The smallest filter containing a given element. -/
def principal (p : P) : pfilter P := ⟨ideal.principal p⟩

@[simp] lemma mem_def (x : P) (I : ideal Pᵒᵈ) :
  x ∈ (⟨I⟩ : pfilter P) ↔ order_dual.to_dual x ∈ I :=
iff.rfl

@[simp] lemma principal_le_iff {F : pfilter P} : principal x ≤ F ↔ x ∈ F :=
ideal.principal_le_iff

@[simp] lemma mem_principal : x ∈ principal y ↔ y ≤ x :=
ideal.mem_principal -- defeq abuse

lemma antitone_principal : antitone (principal : P → pfilter P) := by delta antitone; simp

lemma principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q :=
by simp

end preorder

section order_top
variables [preorder P] [order_top P] {F : pfilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp] lemma top_mem : ⊤ ∈ F := ideal.bot_mem _

/-- There is a bottom filter when `P` has a top element. -/
instance : order_bot (pfilter P) :=
{ bot := ⟨⊥⟩,
  bot_le := λ F, (bot_le : ⊥ ≤ F.dual) }

end order_top

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [preorder P] [order_bot P] : order_top (pfilter P) :=
{ top := ⟨⊤⟩,
  le_top := λ F, (le_top : F.dual ≤ ⊤) }

section semilattice_inf
variables [semilattice_inf P] {x y : P} {F : pfilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
lemma inf_mem (hx : x ∈ F) (hy : y ∈ F) : x ⊓ y ∈ F := ideal.sup_mem hx hy

@[simp] lemma inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F :=
ideal.sup_mem_iff

end semilattice_inf

section complete_semilattice_Inf

variables [complete_semilattice_Inf P] {F : pfilter P}

lemma Inf_gc : galois_connection (λ x, order_dual.to_dual (principal x))
  (λ F, Inf (order_dual.of_dual F : pfilter P)) :=
λ x F, by { simp, refl }

/-- If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois coinsertion. -/
def Inf_gi : galois_coinsertion (λ x, order_dual.to_dual (principal x))
  (λ F, Inf (order_dual.of_dual F : pfilter P)) :=
{ choice := λ F _, Inf (id F : pfilter P),
  gc := Inf_gc,
  u_l_le := λ s, Inf_le $ mem_principal.2 $ le_refl s,
  choice_eq := λ _ _, rfl }

end complete_semilattice_Inf

end pfilter

end order
