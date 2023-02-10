/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import group_theory.subgroup.actions

/-!
# Simple groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `is_simple_group G`, a class indicating that a group has exactly two normal
subgroups.

## Main definitions

- `is_simple_group G`, a class indicating that a group has exactly two normal subgroups.

## Tags
subgroup, subgroups

-/

set_option old_structure_cmd true

variables {G : Type*} [group G]
variables {A : Type*} [add_group A]

section
variables (G) (A)

/-- A `group` is simple when it has exactly two normal `subgroup`s. -/
class is_simple_group extends nontrivial G : Prop :=
(eq_bot_or_eq_top_of_normal : ∀ H : subgroup G, H.normal → H = ⊥ ∨ H = ⊤)

/-- An `add_group` is simple when it has exactly two normal `add_subgroup`s. -/
class is_simple_add_group extends nontrivial A : Prop :=
(eq_bot_or_eq_top_of_normal : ∀ H : add_subgroup A, H.normal → H = ⊥ ∨ H = ⊤)

attribute [to_additive] is_simple_group

variables {G} {A}

@[to_additive]
lemma subgroup.normal.eq_bot_or_eq_top [is_simple_group G] {H : subgroup G} (Hn : H.normal) :
  H = ⊥ ∨ H = ⊤ :=
is_simple_group.eq_bot_or_eq_top_of_normal H Hn

namespace is_simple_group

@[to_additive]
instance {C : Type*} [comm_group C] [is_simple_group C] :
  is_simple_order (subgroup C) :=
⟨λ H, H.normal_of_comm.eq_bot_or_eq_top⟩

open _root_.subgroup

@[to_additive]
lemma is_simple_group_of_surjective {H : Type*} [group H] [is_simple_group G]
  [nontrivial H] (f : G →* H) (hf : function.surjective f) :
  is_simple_group H :=
⟨nontrivial.exists_pair_ne, λ H iH, begin
  refine ((iH.comap f).eq_bot_or_eq_top).imp (λ h, _) (λ h, _),
  { rw [←map_bot f, ←h, map_comap_eq_self_of_surjective hf] },
  { rw [←comap_top f] at h, exact comap_injective hf h }
end⟩

end is_simple_group

end
