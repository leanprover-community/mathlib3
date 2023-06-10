/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import data.sign
import topology.order.basic

/-!
# Topology on `sign_type`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives `sign_type` the discrete topology, and proves continuity results for `sign` in
an `order_topology`.

-/

instance : topological_space sign_type := ⊥
instance : discrete_topology sign_type := ⟨rfl⟩

variables {α : Type*} [has_zero α] [topological_space α]

section partial_order

variables [partial_order α] [decidable_rel ((<) : α → α → Prop)] [order_topology α]

lemma continuous_at_sign_of_pos {a : α} (h : 0 < a) : continuous_at sign a :=
begin
  refine (continuous_at_const : continuous_at (λ x, (1 : sign_type)) a).congr _,
  rw [filter.eventually_eq, eventually_nhds_iff],
  exact ⟨{x | 0 < x}, λ x hx, (sign_pos hx).symm, is_open_lt' 0, h⟩
end

lemma continuous_at_sign_of_neg {a : α} (h : a < 0) : continuous_at sign a :=
begin
  refine (continuous_at_const : continuous_at (λ x, (-1 : sign_type)) a).congr _,
  rw [filter.eventually_eq, eventually_nhds_iff],
  exact ⟨{x | x < 0}, λ x hx, (sign_neg hx).symm, is_open_gt' 0, h⟩
end

end partial_order

section linear_order

variables [linear_order α] [order_topology α]

lemma continuous_at_sign_of_ne_zero {a : α} (h : a ≠ 0) : continuous_at sign a :=
begin
  rcases h.lt_or_lt with h_neg|h_pos,
  { exact continuous_at_sign_of_neg h_neg },
  { exact continuous_at_sign_of_pos h_pos }
end

end linear_order
