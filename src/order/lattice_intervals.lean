/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import order.bounds.basic

/-!
# Intervals in Lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.order_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.order_top`
  * `set.I*c.semillatice_inf`
  * `set.I**.lattice`
  * `set.Iic.bounded_order`, within an `order_bot`
  * `set.Ici.bounded_order`, within an `order_top`

-/

variable {α : Type*}

namespace set

namespace Ico

instance [semilattice_inf α] {a b : α} : semilattice_inf (Ico a b) :=
subtype.semilattice_inf (λ x y hx hy, ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩)

/-- `Ico a b` has a bottom element whenever `a < b`. -/
@[reducible] protected def order_bot [partial_order α] {a b : α} (h : a < b) :
  order_bot (Ico a b) :=
(is_least_Ico h).order_bot

end Ico

namespace Iio

instance [semilattice_inf α] {a : α} : semilattice_inf (Iio a) :=
subtype.semilattice_inf (λ x y hx hy, lt_of_le_of_lt inf_le_left hx)

end Iio

namespace Ioc

instance [semilattice_sup α] {a b : α} : semilattice_sup (Ioc a b) :=
subtype.semilattice_sup (λ x y hx hy, ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩)

/-- `Ioc a b` has a top element whenever `a < b`. -/
@[reducible] protected def order_top [partial_order α] {a b : α} (h : a < b) :
  order_top (Ioc a b) :=
(is_greatest_Ioc h).order_top

end Ioc

namespace Ioi

instance [semilattice_sup α] {a : α} : semilattice_sup (Ioi a) :=
subtype.semilattice_sup (λ x y hx hy, lt_of_lt_of_le hx le_sup_left)

end Ioi

namespace Iic

instance [semilattice_inf α] {a : α} : semilattice_inf (Iic a) :=
subtype.semilattice_inf (λ x y hx hy, le_trans inf_le_left hx)

instance [semilattice_sup α] {a : α} : semilattice_sup (Iic a) :=
subtype.semilattice_sup (λ x y hx hy, sup_le hx hy)

instance [lattice α] {a : α} : lattice (Iic a) :=
{ .. Iic.semilattice_inf,
  .. Iic.semilattice_sup }

instance [preorder α] {a : α} : order_top (Iic a) :=
{ top := ⟨a, le_refl a⟩,
  le_top := λ x, x.prop }

@[simp] lemma coe_top [preorder α] {a : α} : ↑(⊤ : Iic a) = a := rfl

instance [preorder α] [order_bot α] {a : α} : order_bot (Iic a) :=
{ bot := ⟨⊥, bot_le⟩,
  bot_le := λ ⟨_,_⟩, subtype.mk_le_mk.2 bot_le }

@[simp] lemma coe_bot [preorder α] [order_bot α] {a : α} : ↑(⊥ : Iic a) = (⊥ : α) := rfl

instance [preorder α] [order_bot α] {a : α} : bounded_order (Iic a) :=
{ .. Iic.order_top,
  .. Iic.order_bot }

end Iic

namespace Ici

instance [semilattice_inf α] {a : α}: semilattice_inf (Ici a) :=
subtype.semilattice_inf (λ x y hx hy, le_inf hx hy)

instance [semilattice_sup α] {a : α} : semilattice_sup (Ici a) :=
subtype.semilattice_sup (λ x y hx hy, le_trans hx le_sup_left)

instance [lattice α] {a : α} : lattice (Ici a) :=
{ .. Ici.semilattice_inf,
  .. Ici.semilattice_sup }

instance [distrib_lattice α] {a : α} : distrib_lattice (Ici a) :=
{ le_sup_inf := λ a b c, le_sup_inf,
  .. Ici.lattice }

instance [preorder α] {a : α} : order_bot (Ici a) :=
{ bot := ⟨a, le_refl a⟩,
  bot_le := λ x, x.prop }

@[simp] lemma coe_bot [preorder α] {a : α} : ↑(⊥ : Ici a) = a := rfl

instance [preorder α] [order_top α] {a : α}: order_top (Ici a) :=
{ top := ⟨⊤, le_top⟩,
  le_top := λ ⟨_,_⟩, subtype.mk_le_mk.2 le_top }

@[simp] lemma coe_top [preorder α] [order_top α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) := rfl

instance [preorder α] [order_top α] {a : α}: bounded_order (Ici a) :=
{ .. Ici.order_top,
  .. Ici.order_bot }

end Ici

namespace Icc

instance [semilattice_inf α] {a b : α} : semilattice_inf (Icc a b) :=
subtype.semilattice_inf (λ x y hx hy, ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩)

instance [semilattice_sup α] {a b : α} : semilattice_sup (Icc a b) :=
subtype.semilattice_sup (λ x y hx hy, ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩)

instance [lattice α] {a b : α} : lattice (Icc a b) :=
{ .. Icc.semilattice_inf,
  .. Icc.semilattice_sup }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
@[reducible] protected def order_bot [preorder α] {a b : α} (h : a ≤ b) : order_bot (Icc a b) :=
(is_least_Icc h).order_bot

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
@[reducible] protected def order_top [preorder α] {a b : α} (h : a ≤ b) : order_top (Icc a b) :=
(is_greatest_Icc h).order_top

/-- `Icc a b` is a `bounded_order` whenever `a ≤ b`. -/
@[reducible] protected def bounded_order [preorder α] {a b : α} (h : a ≤ b) :
  bounded_order (Icc a b) :=
{ .. Icc.order_top h,
  .. Icc.order_bot h }

end Icc

end set
