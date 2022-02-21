/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set_like.basic
import order.zorn

/-!
# Flags of an order

This file defines

-/

section zorn
variables {α : Type*} [has_le α] {s : set α}
open set

lemma is_max_chain.bot_mem [order_bot α] (h : is_max_chain (≤) s) : ⊥ ∈ s :=
(h.2 (h.1.insert $ λ a _ _, or.inl bot_le) $ subset_insert _ _).symm ▸ mem_insert _ _

lemma is_max_chain.top_mem [order_top α] (h : is_max_chain (≤) s) : ⊤ ∈ s :=
(h.2 (h.1.insert $ λ a _ _, or.inr le_top) $ subset_insert _ _).symm ▸ mem_insert _ _

end zorn

lemma of_eq {α : Type*} {r : α → α → Prop} [is_refl α r] : ∀ {a b}, a = b → r a b
| _ _ ⟨h⟩ := refl _

namespace set
variables {α : Type*} {s : set α} {r : α → α → Prop} {a b : α}

lemma pairwise_iff_of_refl [is_refl α r] : s.pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
forall₄_congr $ λ a _ b _, or_iff_not_imp_left.symm.trans $ or_iff_right_of_imp of_eq

alias pairwise_iff_of_refl ↔ pairwise.of_refl _

lemma _root_.reflexive.pairwise_iff (hr : reflexive r) :
  s.pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
forall₄_congr $ λ a _ b _, or_iff_not_imp_left.symm.trans $ or_iff_right_of_imp $ eq.rec $ hr a


end set

variables {α : Type*}

/-- The type of flags, aka maximal chains, of `α`. -/
structure flag (α : Type*) [has_le α] :=
(carrier : set α)
(chain' : is_chain (≤) carrier)
(max_chain' : ∀ ⦃s⦄, is_chain (≤) s → carrier ⊆ s → carrier = s)

namespace flag
section has_le
variables [has_le α]

instance : set_like (flag α) α :=
{ coe := carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : flag α} : (s : set α) = t → s = t := set_like.ext'

protected lemma chain (s : flag α) : is_chain (≤) (s : set α) := s.chain'
protected lemma max_chain (s : flag α) : @is_max_chain _ (≤) (s : set α) := ⟨s.chain, s.max_chain'⟩

lemma top_mem [order_top α] (s : flag α) : (⊤ : α) ∈ s := s.max_chain.top_mem
lemma bot_mem [order_bot α] (s : flag α) : (⊥ : α) ∈ s := s.max_chain.bot_mem

end has_le

instance subtype.decidable_le [preorder α] [@decidable_rel α (≤)] {p : α → Prop} :
  @decidable_rel (subtype p) (≤) :=
λ a b, decidable_of_iff _ subtype.coe_le_coe

instance subtype.decidable_lt [preorder α] [@decidable_rel α (<)] {p : α → Prop} :
  @decidable_rel (subtype p) (<) :=
λ a b, decidable_of_iff _ subtype.coe_lt_coe

instance [preorder α] [bounded_order α] {p : α → Prop} (hbot : p ⊥) (htop : p ⊤) :
  bounded_order (subtype p) :=
{ ..subtype.order_top htop, ..subtype.order_bot hbot }

instance [partial_order α] [decidable_eq α] [@decidable_rel α (≤)] [@decidable_rel α (<)]
  (φ : flag α) : linear_order φ :=
{ le_total := λ a b, begin
    have : reflexive (λ a b : α, a ≤ b ∨ b ≤ a) := λ a, or.inl le_rfl,
    exact this.pairwise_iff.1 φ.chain a.2 b.2,
  end,
  decidable_eq := subtype.decidable_eq,
  decidable_le := subtype.decidable_le,
  decidable_lt := subtype.decidable_lt,
  ..subtype.partial_order _ }

instance [preorder α] [order_top α] (φ : flag α) : order_top φ := subtype.order_top φ.top_mem
instance [preorder α] [order_bot α] (φ : flag α) : order_bot φ := subtype.order_bot φ.bot_mem
instance [preorder α] [bounded_order α] (φ : flag α) : bounded_order φ :=
subtype.bounded_order φ.bot_mem φ.top_mem

end flag
