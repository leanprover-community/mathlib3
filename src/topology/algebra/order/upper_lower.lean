/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.upper_lower
import topology.algebra.group.basic
import topology.order.basic

/-!
# Topological facts about upper/lower/order-connected sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

## Implementation notes

The same lemmas are true in the additive/multiplicative worlds. To avoid code duplication, we
provide `has_upper_lower_closure`, an ad hoc axiomatisation of the properties we need.
-/

section
variables {α : Type*} [preorder α] {s : set α} {a : α}

open set

lemma mem_upper_bounds_iff_subset_Iic : a ∈ upper_bounds s ↔ s ⊆ Iic a := iff.rfl
lemma mem_lower_bounds_iff_subset_Ici : a ∈ lower_bounds s ↔ s ⊆ Ici a := iff.rfl

end

open function set
open_locale pointwise

/-- Ad hoc class stating that the closure of an upper set is an upper set. This is used to state
lemmas that do not mention algebraic operations for both the additive and multiplicative versions
simultaneously. If you find a satisfying replacement for this typeclass, please remove it! -/
class has_upper_lower_closure (α : Type*) [topological_space α] [preorder α] : Prop :=
(is_upper_set_closure : ∀ s : set α, is_upper_set s → is_upper_set (closure s))
(is_lower_set_closure : ∀ s : set α, is_lower_set s → is_lower_set (closure s))
(is_open_upper_closure : ∀ s : set α, is_open s → is_open (upper_closure s : set α))
(is_open_lower_closure : ∀ s : set α, is_open s → is_open (lower_closure s : set α))

variables {α : Type*} [topological_space α]

@[to_additive, priority 100] -- See note [lower instance priority]
instance ordered_comm_group.to_has_upper_lower_closure [ordered_comm_group α]
  [has_continuous_const_smul α α] : has_upper_lower_closure α :=
{ is_upper_set_closure := λ s h x y hxy hx, closure_mono (h.smul_subset $ one_le_div'.2 hxy) $
    by { rw closure_smul, exact ⟨x, hx, div_mul_cancel' _ _⟩ },
  is_lower_set_closure := λ s h x y hxy hx, closure_mono (h.smul_subset $ div_le_one'.2 hxy) $
    by { rw closure_smul, exact ⟨x, hx, div_mul_cancel' _ _⟩ },
  is_open_upper_closure := λ s hs, by { rw [←mul_one s, ←mul_upper_closure], exact hs.mul_right },
  is_open_lower_closure := λ s hs, by { rw [←mul_one s, ←mul_lower_closure], exact hs.mul_right } }

variables [preorder α]

section order_closed_topology
variables [order_closed_topology α] {s : set α}

@[simp] lemma upper_bounds_closure (s : set α) :
  upper_bounds (closure s : set α) = upper_bounds s :=
ext $ λ a, by simp_rw [mem_upper_bounds_iff_subset_Iic, is_closed_Iic.closure_subset_iff]

@[simp] lemma lower_bounds_closure (s : set α) :
  lower_bounds (closure s : set α) = lower_bounds s :=
ext $ λ a, by simp_rw [mem_lower_bounds_iff_subset_Ici, is_closed_Ici.closure_subset_iff]

@[simp] lemma bdd_above_closure : bdd_above (closure s) ↔ bdd_above s :=
by simp_rw [bdd_above, upper_bounds_closure]

@[simp] lemma bdd_below_closure : bdd_below (closure s) ↔ bdd_below s :=
by simp_rw [bdd_below, lower_bounds_closure]

alias bdd_above_closure ↔ bdd_above.of_closure bdd_above.closure
alias bdd_below_closure ↔ bdd_below.of_closure bdd_below.closure

attribute [protected] bdd_above.closure bdd_below.closure

end order_closed_topology

variables [has_upper_lower_closure α] {s : set α}

protected lemma is_upper_set.closure : is_upper_set s → is_upper_set (closure s) :=
has_upper_lower_closure.is_upper_set_closure _

protected lemma is_lower_set.closure : is_lower_set s → is_lower_set (closure s) :=
has_upper_lower_closure.is_lower_set_closure _

protected lemma is_open.upper_closure : is_open s → is_open (upper_closure s : set α) :=
has_upper_lower_closure.is_open_upper_closure _

protected lemma is_open.lower_closure : is_open s → is_open (lower_closure s : set α) :=
has_upper_lower_closure.is_open_lower_closure _

instance : has_upper_lower_closure αᵒᵈ :=
{ is_upper_set_closure := @is_lower_set.closure α _ _ _,
  is_lower_set_closure := @is_upper_set.closure α _ _ _,
  is_open_upper_closure := @is_open.lower_closure α _ _ _,
  is_open_lower_closure := @is_open.upper_closure α _ _ _ }

/-
Note: `s.ord_connected` does not imply `(closure s).ord_connected`, as we can see by taking
`s := Ioo 0 1 × Ioo 1 2 ∪ Ioo 2 3 × Ioo 0 1` because then
`closure s = Icc 0 1 × Icc 1 2 ∪ Icc 2 3 × Icc 0 1` is not order-connected as
`(1, 1) ∈ closure s`, `(2, 1) ∈ closure s` but `Icc (1, 1) (2, 1) ⊈ closure s`.

`s` looks like
```
xxooooo
xxooooo
oooooxx
oooooxx
```
-/

protected lemma is_upper_set.interior (h : is_upper_set s) : is_upper_set (interior s) :=
by { rw [←is_lower_set_compl, ←closure_compl], exact h.compl.closure }

protected lemma is_lower_set.interior (h : is_lower_set s) : is_lower_set (interior s) :=
h.of_dual.interior

protected lemma set.ord_connected.interior (h : s.ord_connected) : (interior s).ord_connected :=
begin
  rw [←h.upper_closure_inter_lower_closure, interior_inter],
  exact (upper_closure s).upper.interior.ord_connected.inter
    (lower_closure s).lower.interior.ord_connected,
end
