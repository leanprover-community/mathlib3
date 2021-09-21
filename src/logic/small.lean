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

universes u w v

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

theorem small_type : small.{max (u+1) v} (Type u) := small_max.{max (u+1) v} _

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

theorem small_of_injective {α : Type*} {β : Type*} [small.{w} β]
  (f : α → β) (hf : function.injective f) : small.{w} α :=
begin
  rw small_congr (equiv.of_injective f hf),
  apply_instance,
end

@[priority 100]
instance small_subsingleton (α : Type v) [subsingleton α] : small.{w} α :=
begin
  rcases is_empty_or_nonempty α; resetI,
  { rw small_congr (equiv.equiv_pempty α), apply small_self, },
  { rw small_congr equiv.punit_of_nonempty_of_subsingleton,
    apply small_self, assumption, assumption, },
end

/-!
We don't define `small_of_fintype` or `small_of_encodable` in this file,
to keep imports to `logic` to a minimum.
-/

instance small_Pi {α} (β : α → Type*) [small.{w} α] [∀ a, small.{w} (β a)] :
  small.{w} (Π a, β a) :=
⟨⟨Π a' : shrink α, shrink (β ((equiv_shrink α).symm a')),
  ⟨equiv.Pi_congr (equiv_shrink α) (λ a, by simpa using equiv_shrink (β a))⟩⟩⟩

instance small_sigma {α} (β : α → Type*) [small.{w} α] [∀ a, small.{w} (β a)] :
  small.{w} (Σ a, β a) :=
⟨⟨Σ a' : shrink α, shrink (β ((equiv_shrink α).symm a')),
  ⟨equiv.sigma_congr (equiv_shrink α) (λ a, by simpa using equiv_shrink (β a))⟩⟩⟩

instance small_prod {α β} [small.{w} α] [small.{w} β] : small.{w} (α × β) :=
⟨⟨shrink α × shrink β,
  ⟨equiv.prod_congr (equiv_shrink α) (equiv_shrink β)⟩⟩⟩

instance small_sum {α β} [small.{w} α] [small.{w} β] : small.{w} (α ⊕ β) :=
⟨⟨shrink α ⊕ shrink β,
  ⟨equiv.sum_congr (equiv_shrink α) (equiv_shrink β)⟩⟩⟩

instance small_set {α} [small.{w} α] : small.{w} (set α) :=
⟨⟨set (shrink α), ⟨equiv.set.congr (equiv_shrink α)⟩⟩⟩

theorem not_small_type : ¬ small.{u} (Type (max u v))
| ⟨⟨S, ⟨e⟩⟩⟩ := @function.cantor_injective (Σ α, e.symm α)
  (λ a, ⟨_, cast (e.3 _).symm a⟩)
  (λ a b e, (cast_inj _).1 $ eq_of_heq (sigma.mk.inj e).2)

end
