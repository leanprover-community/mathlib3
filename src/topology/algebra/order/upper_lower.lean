/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.upper_lower
import topology.algebra.group

/-!
# Topological facts about upper/lower/order-connected sets

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

## Notes

The lemmas don't mention additive/multiplicative operations. As a result, we decide to prime the
multiplicative lemma names to indicate that there is probably a commong generalisation to each pair
of additive/multiplicative lemma.
-/

open function set
open_locale pointwise

/-- Ad hoc class stating that the closure of an upper set is an upper set. This is used to state
lemmas that do not mention algebraic operations for both the additive and multiplicative versions
simultaneously. If you find a satisfying replacement for this typeclass, please remove it! -/
class has_upper_lower_closure (α : Type*) [topological_space α] [has_le α] : Prop :=
(upper_closure : ∀ s : set α, is_upper_set s → is_upper_set (closure s))
(lower_closure : ∀ s : set α, is_lower_set s → is_lower_set (closure s))

variables {α : Type*} [topological_space α]

instance [has_le α] [has_upper_lower_closure α] : has_upper_lower_closure αᵒᵈ :=
{ upper_closure := @has_upper_lower_closure.lower_closure α _ _ _,
  lower_closure := @has_upper_lower_closure.upper_closure α _ _ _ }

@[to_additive, priority 100] -- See note [lower instance priority]
instance ordered_comm_group.to_has_upper_lower_closure [ordered_comm_group α]
  [has_continuous_const_smul α α] : has_upper_lower_closure α :=
{ upper_closure := λ s h x y hxy hx, closure_mono (h.smul_subset $ one_le_div'.2 hxy) $
    by { rw closure_smul, exact ⟨x, hx, div_mul_cancel' _ _⟩ },
  lower_closure := λ s h x y hxy hx, closure_mono (h.smul_subset $ div_le_one'.2 hxy) $
    by { rw closure_smul, exact ⟨x, hx, div_mul_cancel' _ _⟩ } }

section has_upper_lower_closure
variables [preorder α] [has_upper_lower_closure α] {s : set α}

protected lemma is_upper_set.closure : is_upper_set s → is_upper_set (closure s) :=
has_upper_lower_closure.upper_closure _

protected lemma is_lower_set.closure : is_lower_set s → is_lower_set (closure s) :=
has_upper_lower_closure.lower_closure _

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

end has_upper_lower_closure

section has_continuous_const_smul
variables [ordered_comm_group α] [has_continuous_const_smul α α] {s : set α}

@[to_additive is_open.upper_closure]
protected lemma is_open.upper_closure' (hs : is_open s) : is_open (upper_closure s : set α) :=
by { rw [←mul_one s, ←mul_upper_closure], exact hs.mul_right }

@[to_additive is_open.lower_closure]
protected lemma is_open.lower_closure' (hs : is_open s) : is_open (lower_closure s : set α) :=
by { rw [←mul_one s, ←mul_lower_closure], exact hs.mul_right }

end has_continuous_const_smul

