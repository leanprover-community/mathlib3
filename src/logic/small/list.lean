/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import logic.small.basic
import data.vector.basic

/-!
# Instances for `small (list α)` and `small (vector α)`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These must not be in `logic.small.basic` as this is very low in the import hierarchy,
and is used by category theory files which do not need everything imported by `data.vector.basic`.
-/

universes u v

instance small_vector {α : Type v} {n : ℕ} [small.{u} α] :
  small.{u} (vector α n) :=
small_of_injective (equiv.vector_equiv_fin α n).injective

instance small_list {α : Type v} [small.{u} α] :
  small.{u} (list α) :=
begin
  let e : (Σ n, vector α n) ≃ list α := equiv.sigma_fiber_equiv list.length,
  exact small_of_surjective e.surjective,
end
