/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .factor

/-!
# Forcing edges and forcing sets
-/


variables {α : Type*}

namespace simple_graph
variables (k : ℕ) (G H : simple_graph α)

def is_forcing (k : ℕ) (G H : simple_graph α) : Prop :=
(∃ (I : simple_graph α) [h : I.locally_finite], H ≤ I ∧ by exactI G.is_factor k I) ∧
  ∀ ⦃I : simple_graph α⦄ [I.locally_finite], by exactI G.is_factor k I → H ≤ I

structure forcings (G : simple_graph α) (k : ℕ) :=
(forcing : simple_graph α)
(factor : simple_graph α)
(locally_finite : factor.locally_finite)
(factor_is_factor : by exactI G.is_factor k factor)
(max_factor : ∀ ⦃I : simple_graph α⦄ [I.locally_finite], by exactI G.is_factor k I → forcing ≤ I)

instance [fintype α] : fintype (forcings G k) := sorry

end simple_graph
