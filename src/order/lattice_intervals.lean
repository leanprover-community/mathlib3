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
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances.

## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.semilattice_inf_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.semilattice_sup_top`
  * `set.I*c.semillatice_inf`
  * `set.Iic.bounded_lattice`, within a `bounded_lattice`
  * `set.Ici.bounded_lattice`, within a `bounded_lattice`

-/

variable {α : Type*}

namespace set

namespace Ico

instance semilattice_inf [semilattice_inf α] {a b : α} : semilattice_inf (Ico a b) :=
subtype.semilattice_inf (λ x y hx hy, ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩)

/-- `Ico a b` has a bottom element whenever `a < b`. -/
def order_bot [partial_order α] {a b : α} (h : a < b) : order_bot (Ico a b) :=
{ bot := ⟨a, ⟨le_refl a, h⟩⟩,
  bot_le := λ x, x.prop.1,
  .. (subtype.partial_order _) }

/-- `Ico a b` is a `semilattice_inf_bot` whenever `a < b`. -/
def semilattice_inf_bot [semilattice_inf α] {a b : α} (h : a < b) : semilattice_inf_bot (Ico a b) :=
{ .. (Ico.semilattice_inf), .. (Ico.order_bot h) }

end Ico

namespace Iio

instance semilattice_inf [semilattice_inf α] {a : α} : semilattice_inf (Iio a) :=
subtype.semilattice_inf (λ x y hx hy, lt_of_le_of_lt inf_le_left hx)

end Iio

namespace Ioc

instance semilattice_sup [semilattice_sup α] {a b : α} : semilattice_sup (Ioc a b) :=
subtype.semilattice_sup (λ x y hx hy, ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩)

/-- `Ioc a b` has a top element whenever `a < b`. -/
def order_top [partial_order α] {a b : α} (h : a < b) : order_top (Ioc a b) :=
{ top := ⟨b, ⟨h, le_refl b⟩⟩,
  le_top := λ x, x.prop.2,
  .. (subtype.partial_order _) }

/-- `Ioc a b` is a `semilattice_sup_top` whenever `a < b`. -/
def semilattice_sup_top [semilattice_sup α] {a b : α} (h : a < b) : semilattice_sup_top (Ioc a b) :=
{ .. (Ioc.semilattice_sup), .. (Ioc.order_top h) }

end Ioc

namespace Iio

instance semilattice_sup [semilattice_sup α] {a : α} : semilattice_sup (Ioi a) :=
subtype.semilattice_sup (λ x y hx hy, lt_of_lt_of_le hx le_sup_left)

end Iio

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
