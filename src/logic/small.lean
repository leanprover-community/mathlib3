/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.basic

/-!
# Small types

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `shrink α : Type w`, and `equiv_shrink α : α ≃ shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `small.{w} α ↔ small.{w} β`.
-/

universes w v

/--
A type is `small.{w}` if there exists an equivalence to some `S : Type w`.
-/
class small (α : Type v) : Prop :=
(equiv_small : ∃ (S : Type w) (e : α ≃ S), true)

/--
Constructor for `small α` from an explicit witness type and equivalence.
-/
lemma small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : small.{w} α :=
⟨⟨S, e, trivial⟩⟩

/--
An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[nolint has_inhabited_instance]
def shrink (α : Type v) [small.{w} α] : Type w :=
classical.some (@small.equiv_small α _)

/--
The noncomputable equivalence between a `w`-small type and a model.
-/
noncomputable
def equiv_shrink (α : Type v) [small.{w} α] : α ≃ shrink α :=
classical.some (classical.some_spec (@small.equiv_small α _))

@[priority 100]
instance small_self (α : Type v) : small.{v} α :=
small.mk' (equiv.refl _)

@[priority 100]
instance small_max (α : Type v) : small.{max w v} α :=
small.mk' equiv.ulift.{w}.symm

instance small_ulift (α : Type v) : small.{v} (ulift.{w} α) :=
small.mk' equiv.ulift

section
open_locale classical

lemma small_of_subsingleton (α : Type v) [subsingleton α] : small.{w} α :=
if w : nonempty α then
  by exactI small.mk' equiv.punit_of_nonempty_of_subsingleton
else
  small.mk' (equiv.pempty_of_not_nonempty w)
end

theorem small_congr {α : Type*} {β : Type*} (e : α ≃ β) : small.{w} α ↔ small.{w} β :=
begin
  fsplit,
  { rintro ⟨S, f, -⟩,
    exact small.mk' (e.symm.trans f), },
  { rintro ⟨S, f, -⟩,
    exact small.mk' (e.trans f), },
end
