/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.order.ring.defs

/-!
# Constructing an ordered ring from a ring with a specified positive cone.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

/-! ### Positive cones -/

set_option old_structure_cmd true

variables {α : Type*} [ring α] [nontrivial α]

namespace ring

/-- A positive cone in a ring consists of a positive cone in underlying `add_comm_group`,
which contains `1` and such that the positive elements are closed under multiplication. -/
@[nolint has_nonempty_instance]
structure positive_cone (α : Type*) [ring α] extends add_comm_group.positive_cone α :=
(one_nonneg : nonneg 1)
(mul_pos : ∀ (a b), pos a → pos b → pos (a * b))

/-- Forget that a positive cone in a ring respects the multiplicative structure. -/
add_decl_doc positive_cone.to_positive_cone

/-- A total positive cone in a nontrivial ring induces a linear order. -/
@[nolint has_nonempty_instance]
structure total_positive_cone (α : Type*) [ring α]
  extends positive_cone α, add_comm_group.total_positive_cone α

/-- Forget that a `total_positive_cone` in a ring is total. -/
add_decl_doc total_positive_cone.to_positive_cone

/-- Forget that a `total_positive_cone` in a ring respects the multiplicative structure. -/
add_decl_doc total_positive_cone.to_total_positive_cone

lemma positive_cone.one_pos (C : positive_cone α) : C.pos 1 :=
(C.pos_iff _).2 ⟨C.one_nonneg, λ h, one_ne_zero $ C.nonneg_antisymm C.one_nonneg h⟩

end ring

open ring

/-- Construct a `strict_ordered_ring` by designating a positive cone in an existing `ring`. -/
def strict_ordered_ring.mk_of_positive_cone (C : positive_cone α) : strict_ordered_ring α :=
{ exists_pair_ne := ⟨0, 1, λ h, by simpa [←h, C.pos_iff] using C.one_pos⟩,
  zero_le_one := by { change C.nonneg (1 - 0), convert C.one_nonneg, simp, },
  mul_pos := λ x y xp yp, begin
    change C.pos (x*y - 0),
    convert C.mul_pos x y (by { convert xp, simp, }) (by { convert yp, simp, }),
    simp,
  end,
  ..‹ring α›,
  ..ordered_add_comm_group.mk_of_positive_cone C.to_positive_cone }

/-- Construct a `linear_ordered_ring` by
designating a positive cone in an existing `ring`. -/
def linear_ordered_ring.mk_of_positive_cone (C : total_positive_cone α) : linear_ordered_ring α :=
{ ..strict_ordered_ring.mk_of_positive_cone C.to_positive_cone,
  ..linear_ordered_add_comm_group.mk_of_positive_cone C.to_total_positive_cone, }
