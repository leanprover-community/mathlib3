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
-/

open function set
open_locale pointwise

variables {α : Type*} [topological_space α] [ordered_comm_group α]

section has_continuous_const_smul
variables [has_continuous_const_smul α α] {s : set α}

@[to_additive is_upper_set.closure]
protected lemma is_upper_set.closure' (h : is_upper_set s) : is_upper_set (closure s) :=
λ x y hxy hx, closure_mono (h.smul_subset $ one_le_div'.2 hxy) $
  by { rw closure_smul, exact ⟨x, hx, div_mul_cancel' _ _⟩ }

@[to_additive is_lower_set.closure]
protected lemma is_lower_set.closure' (h : is_lower_set s) : is_lower_set (closure s) :=
h.of_dual.closure'

/-
Note: ` s.ord_connected` does not imply `(closure s).ord_connected`, as we can see by taking
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

@[to_additive is_upper_set.interior]
protected lemma is_upper_set.interior' (h : is_upper_set s) : is_upper_set (interior s) :=
by { rw [←is_lower_set_compl, ←closure_compl], exact h.compl.closure' }

@[to_additive is_lower_set.interior]
protected lemma is_lower_set.interior' (h : is_lower_set s) : is_lower_set (interior s) :=
h.of_dual.interior'

@[to_additive set.ord_connected.interior]
protected lemma set.ord_connected.interior' (h : s.ord_connected) : (interior s).ord_connected :=
begin
  rw [←h.upper_closure_inter_lower_closure, interior_inter],
  exact (upper_closure s).upper.interior'.ord_connected.inter
    (lower_closure s).lower.interior'.ord_connected,
end

--TODO: Additivize `is_central_scalar`
@[to_additive is_open.upper_closure]
protected lemma is_open.upper_closure' (hs : is_open s) : is_open (upper_closure s : set α) :=
by { rw [←mul_one s, ←mul_upper_closure], exact hs.mul_right }

@[to_additive is_open.lower_closure]
protected lemma is_open.lower_closure' (hs : is_open s) : is_open (lower_closure s : set α) :=
by { rw [←mul_one s, ←mul_lower_closure], exact hs.mul_right }

end has_continuous_const_smul
