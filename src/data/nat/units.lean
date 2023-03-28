/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import data.nat.basic
import algebra.group.units

/-! # The units of the natural numbers as a `monoid` and `add_monoid`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

namespace nat

theorem units_eq_one (u : ℕˣ) : u = 1 :=
units.ext $ nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

theorem add_units_eq_zero (u : add_units ℕ) : u = 0 :=
add_units.ext $ (nat.eq_zero_of_add_eq_zero u.val_neg).1

@[simp] protected theorem is_unit_iff {n : ℕ} : is_unit n ↔ n = 1 :=
iff.intro
  (λ ⟨u, hu⟩, match n, u, hu, nat.units_eq_one u with _, _, rfl, rfl := rfl end)
  (λ h, h.symm ▸ ⟨1, rfl⟩)

instance unique_units : unique ℕˣ :=
{ default := 1, uniq := nat.units_eq_one }

instance unique_add_units : unique (add_units ℕ) :=
{ default := 0, uniq := nat.add_units_eq_zero }

end nat
