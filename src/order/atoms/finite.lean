/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.set.finite
import order.atoms

/-!
# Atoms, Coatoms, Simple Lattices, and Finiteness

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module contains some results on atoms and simple lattices in the finite context.

## Main results
  * `finite.to_is_atomic`, `finite.to_is_coatomic`: Finite partial orders with bottom resp. top
    are atomic resp. coatomic.

-/

variables {α β : Type*}

namespace is_simple_order
section decidable_eq

/- It is important that `is_simple_order` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply. -/
@[priority 200]
instance {α} [decidable_eq α] [has_le α] [bounded_order α] [is_simple_order α] : fintype α :=
fintype.of_equiv bool equiv_bool.symm

end decidable_eq
end is_simple_order

namespace fintype
namespace is_simple_order
variables [partial_order α] [bounded_order α] [is_simple_order α] [decidable_eq α]

lemma univ : (finset.univ : finset α) = {⊤, ⊥} :=
begin
  change finset.map _ (finset.univ : finset bool) = _,
  rw fintype.univ_bool,
  simp only [finset.map_insert, function.embedding.coe_fn_mk, finset.map_singleton],
  refl,
end

lemma card : fintype.card α = 2 :=
(fintype.of_equiv_card _).trans fintype.card_bool

end is_simple_order
end fintype

namespace bool

instance : is_simple_order bool :=
⟨λ a, begin
  rw [← finset.mem_singleton, or.comm, ← finset.mem_insert,
      top_eq_tt, bot_eq_ff, ← fintype.univ_bool],
  apply finset.mem_univ,
end⟩

end bool

section fintype

open finset

@[priority 100]  -- see Note [lower instance priority]
instance finite.to_is_coatomic [partial_order α] [order_top α] [finite α] : is_coatomic α :=
begin
  refine is_coatomic.mk (λ b, or_iff_not_imp_left.2 (λ ht, _)),
  obtain ⟨c, hc, hmax⟩ := set.finite.exists_maximal_wrt id { x : α | b ≤ x ∧ x ≠ ⊤ }
    (set.to_finite _) ⟨b, le_rfl, ht⟩,
  refine ⟨c, ⟨hc.2, λ y hcy, _⟩, hc.1⟩,
  by_contra hyt,
  obtain rfl : c = y := hmax y ⟨hc.1.trans hcy.le, hyt⟩ hcy.le,
  exact (lt_self_iff_false _).mp hcy
end

@[priority 100]  -- see Note [lower instance priority]
instance finite.to_is_atomic [partial_order α] [order_bot α] [finite α] : is_atomic α :=
is_coatomic_dual_iff_is_atomic.mp finite.to_is_coatomic

end fintype
