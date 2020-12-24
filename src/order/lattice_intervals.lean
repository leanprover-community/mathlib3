/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson.
-/

import order.bounded_lattice
import data.set.intervals.basic

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.

## Main definitions
  * `set.Iic.bounded_lattice`
  * `set.Ici.bounded_lattice`

-/

variable {α : Type*}

namespace set

namespace Iic

instance lattice [lattice α] {a : α} : lattice (Iic a) :=
subtype.lattice (λ x y hx hy, mem_Iic.2 (sup_le hx hy)) (λ x y hx hy, le_trans inf_le_left hx)

instance order_top [partial_order α] {a : α} : order_top (Iic a) :=
{ top := ⟨a, le_refl a⟩,
  le_top := λ x, x.prop,
.. (subtype.partial_order _) }

@[simp] lemma coe_top [partial_order α] {a : α} : ↑(⊤ : Iic a) = a := rfl

instance bounded_lattice [bounded_lattice α] {a : α} :
  bounded_lattice (Iic a) :=
{ bot := ⟨⊥, mem_Iic.2 bot_le⟩,
  bot_le := λ ⟨_, _⟩, subtype.mk_le_mk.2 bot_le,
  .. (set.Iic.order_top),
  .. (set.Iic.lattice) }

@[simp] lemma coe_bot [bounded_lattice α] {a : α} : ↑(⊥ : Iic a) = (⊥ : α) := rfl

end Iic

namespace Ici

instance lattice [lattice α] {a : α} : lattice (Ici a) :=
subtype.lattice (λ x y hx hy, le_trans hx le_sup_left) (λ x y hx hy, le_inf hx hy)

instance order_bot [partial_order α] {a : α} : order_bot (Ici a) :=
{ bot := ⟨a, le_refl a⟩,
  bot_le := λ x, x.prop,
.. (subtype.partial_order _) }

@[simp] lemma coe_bot [partial_order α] {a : α} : ↑(⊥ : Ici a) = a := rfl

instance bounded_lattice [bounded_lattice α] {a : α} :
  bounded_lattice (Ici a) :=
{ top := ⟨⊤, mem_Ici.2 le_top⟩,
  le_top := λ ⟨_, _⟩, subtype.mk_le_mk.2 le_top,
  .. (set.Ici.order_bot),
  .. (set.Ici.lattice) }

@[simp] lemma coe_top [bounded_lattice α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) := rfl

end Ici

end set
