/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.field.basic
import data.fintype.lattice

/-!
# Lemmas about (finite domain) functions into fields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We split this from `algebra.order.field.basic` to avoid importing the finiteness hierarchy there.
-/

variables {α ι : Type*} [linear_ordered_semifield α]

lemma pi.exists_forall_pos_add_lt [has_exists_add_of_le α] [finite ι] {x y : ι → α}
  (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i :=
begin
  casesI nonempty_fintype ι,
  casesI is_empty_or_nonempty ι,
  { exact ⟨1, zero_lt_one, is_empty_elim⟩ },
  choose ε hε hxε using λ i, exists_pos_add_of_lt' (h i),
  obtain rfl : x + ε = y := funext hxε,
  have hε : 0 < finset.univ.inf' finset.univ_nonempty ε := (finset.lt_inf'_iff _).2 (λ i _, hε _),
  exact ⟨_, half_pos hε, λ i, add_lt_add_left ((half_lt_self hε).trans_le $ finset.inf'_le _ $
    finset.mem_univ _) _⟩,
end
