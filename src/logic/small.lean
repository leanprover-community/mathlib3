/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.encodable.basic
import data.fintype.basic

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
(equiv_small : ∃ (S : Type w), nonempty (α ≃ S))

/--
Constructor for `small α` from an explicit witness type and equivalence.
-/
lemma small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : small.{w} α :=
⟨⟨S, ⟨e⟩⟩⟩

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
nonempty.some (classical.some_spec (@small.equiv_small α _))

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

theorem small_congr {α : Type*} {β : Type*} (e : α ≃ β) : small.{w} α ↔ small.{w} β :=
begin
  fsplit,
  { rintro ⟨S, ⟨f⟩⟩,
    exact small.mk' (e.symm.trans f), },
  { rintro ⟨S, ⟨f⟩⟩,
    exact small.mk' (e.trans f), },
end

instance small_subtype (α : Type v) [small.{w} α] (P : α → Prop) : small.{w} { x // P x } :=
begin
  rw small_congr (equiv_shrink α).subtype_equiv_of_subtype',
  apply_instance,
end

@[priority 100]
instance small_of_fintype (α : Type v) [fintype α] : small.{w} α :=
begin
  obtain ⟨n, ⟨e⟩⟩ := fintype.exists_equiv_fin α,
  rw small_congr e,
  apply_instance,
end

theorem small_of_injective {α : Type*} {β : Type*} [small.{w} β]
  (f : α → β) (hf : function.injective f) : small.{w} α :=
begin
  rw small_congr (equiv.set.range f hf),
  apply_instance,
end

@[priority 100]
instance small_of_encodable (α : Type v) [encodable α] : small.{w} α :=
small_of_injective _ (encodable.encode_injective)

end
