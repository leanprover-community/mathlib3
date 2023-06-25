/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.surreal.basic

/-!
# Ordinals as surreals

We define the canonical map `ordinal → surreal` as the composition of `ordinal.to_pgame` and
`surreal.mk`, as an order embedding.
-/

open pgame surreal

local infix ` ♯ `:65 := ordinal.nadd

namespace ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def to_surreal : ordinal ↪o surreal :=
{ to_fun := λ o, mk _ (numeric_to_pgame o),
  inj' := λ a b h, to_pgame_equiv_iff.1 (quotient.exact h),
  map_rel_iff' := @to_pgame_le_iff }

theorem to_surreal_strict_mono : strict_mono to_surreal :=
to_pgame_strict_mono

@[simp] theorem zero_to_surreal : to_surreal 0 = 0 :=
quotient.sound zero_to_pgame_equiv

@[simp] theorem one_to_surreal : to_surreal 1 = 1 :=
quotient.sound one_to_pgame_equiv

@[simp] theorem to_surreal_add (a b : ordinal) : a.to_surreal + b.to_surreal = (a ♯ b).to_surreal :=
quot.sound (to_pgame_add a b)

@[simp] theorem to_surreal_add_one (a : ordinal) : a.to_surreal + 1 = (order.succ a).to_surreal :=
quot.sound (to_pgame_add_one a)

@[simp] theorem to_surreal_one_add (a : ordinal) : 1 + a.to_surreal = (order.succ a).to_surreal :=
quot.sound (to_pgame_one_add a)

@[simp] theorem nat_cast_to_surreal (n : ℕ) : to_surreal n = n :=
by { rw ←mk_nat_cast, exact quot.sound (nat_cast_to_pgame n) }

@[simp] theorem to_surreal_add_nat (a : ordinal) (n : ℕ) : a.to_surreal + n = (a + n).to_surreal :=
by rw [←nat_cast_to_surreal, to_surreal_add, nadd_nat]

@[simp] theorem to_surreal_nat_add (a : ordinal) (n : ℕ) : ↑n + a.to_surreal = (a + n).to_surreal :=
by rw [add_comm, to_surreal_add_nat]

end ordinal

/-- The cast from `nat_ordinal` to `surreal` preserves addition. -/
noncomputable def nat_ordinal.to_surreal : nat_ordinal →+o surreal :=
{ to_fun := λ o, o.to_ordinal.to_surreal,
  map_zero' := ordinal.zero_to_surreal,
  map_add' := λ a b, (ordinal.to_surreal_add _ _).symm,
  monotone' := ordinal.to_surreal_strict_mono.monotone }
