/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Anne Baanen
-/
import logic.function.iterate
import order.galois_connection
import order.hom.basic

/-!
# Lattice structure on order homomorphisms

This file defines the lattice structure on order homomorphisms, which are bundled
monotone functions.

## Main definitions

 * `order_hom.complete_lattice`: if `β` is a complete lattice, so is `α →o β`

## Tags

monotone map, bundled morphism
-/

namespace order_hom

variables {α β : Type*}

section preorder

variables [preorder α]

@[simps]
instance [semilattice_sup β] : has_sup (α →o β) :=
{ sup := λ f g, ⟨λ a, f a ⊔ g a, f.mono.sup g.mono⟩ }

instance [semilattice_sup β] : semilattice_sup (α →o β) :=
{ sup := has_sup.sup,
  le_sup_left := λ a b x, le_sup_left,
  le_sup_right := λ a b x, le_sup_right,
  sup_le := λ a b c h₀ h₁ x, sup_le (h₀ x) (h₁ x),
  .. (_ : partial_order (α →o β)) }

@[simps]
instance [semilattice_inf β] : has_inf (α →o β) :=
{ inf := λ f g, ⟨λ a, f a ⊓ g a, f.mono.inf g.mono⟩ }

instance [semilattice_inf β] : semilattice_inf (α →o β) :=
{ inf := (⊓),
  .. (_ : partial_order (α →o β)),
  .. (dual_iso α β).symm.to_galois_insertion.lift_semilattice_inf }

instance [lattice β] : lattice (α →o β) :=
{ .. (_ : semilattice_sup (α →o β)),
  .. (_ : semilattice_inf (α →o β)) }

@[simps]
instance [preorder β] [order_bot β] : has_bot (α →o β) :=
{ bot := const α ⊥ }

instance [preorder β] [order_bot β] : order_bot (α →o β) :=
{ bot := ⊥,
  bot_le := λ a x, bot_le }

@[simps]
instance [preorder β] [order_top β] : has_top (α →o β) :=
{ top := const α ⊤ }

instance [preorder β] [order_top β] : order_top (α →o β) :=
{ top := ⊤,
  le_top := λ a x, le_top }

instance [complete_lattice β] : has_Inf (α →o β) :=
{ Inf := λ s, ⟨λ x, ⨅ f ∈ s, (f : _) x, λ x y h, binfi_le_binfi (λ f _, f.mono h)⟩ }

@[simp] lemma Inf_apply [complete_lattice β] (s : set (α →o β)) (x : α) :
  Inf s x = ⨅ f ∈ s, (f : _) x := rfl

lemma infi_apply {ι : Sort*} [complete_lattice β] (f : ι → α →o β) (x : α) :
  (⨅ i, f i) x = ⨅ i, f i x :=
(Inf_apply _ _).trans infi_range

@[simp, norm_cast] lemma coe_infi {ι : Sort*} [complete_lattice β] (f : ι → α →o β) :
  ((⨅ i, f i : α →o β) : α → β) = ⨅ i, f i :=
funext $ λ x, (infi_apply f x).trans (@_root_.infi_apply _ _ _ _ (λ i, f i) _).symm

instance [complete_lattice β] : has_Sup (α →o β) :=
{ Sup := λ s, ⟨λ x, ⨆ f ∈ s, (f : _) x, λ x y h, bsupr_le_bsupr (λ f _, f.mono h)⟩ }

@[simp] lemma Sup_apply [complete_lattice β] (s : set (α →o β)) (x : α) :
  Sup s x = ⨆ f ∈ s, (f : _) x := rfl

lemma supr_apply {ι : Sort*} [complete_lattice β] (f : ι → α →o β) (x : α) :
  (⨆ i, f i) x = ⨆ i, f i x :=
(Sup_apply _ _).trans supr_range

@[simp, norm_cast] lemma coe_supr {ι : Sort*} [complete_lattice β] (f : ι → α →o β) :
  ((⨆ i, f i : α →o β) : α → β) = ⨆ i, f i :=
funext $ λ x, (supr_apply f x).trans (@_root_.supr_apply _ _ _ _ (λ i, f i) _).symm

instance [complete_lattice β] : complete_lattice (α →o β) :=
{ Sup := Sup,
  le_Sup := λ s f hf x, le_supr_of_le f (le_supr _ hf),
  Sup_le := λ s f hf x, bsupr_le (λ g hg, hf g hg x),
  Inf := Inf,
  le_Inf := λ s f hf x, le_binfi (λ g hg, hf g hg x),
  Inf_le := λ s f hf x, infi_le_of_le f (infi_le _ hf),
  .. (_ : lattice (α →o β)),
  .. order_hom.order_top,
  .. order_hom.order_bot }

lemma iterate_sup_le_sup_iff {α : Type*} [semilattice_sup α] (f : α →o α) :
  (∀ n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) ≤ (f^[n₁] a₁) ⊔ (f^[n₂] a₂)) ↔
  (∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ (f a₁) ⊔ a₂) :=
begin
  split; intros h,
  { exact h 1 0, },
  { intros n₁ n₂ a₁ a₂, have h' : ∀ n a₁ a₂, f^[n] (a₁ ⊔ a₂) ≤ (f^[n] a₁) ⊔ a₂,
    { intros n, induction n with n ih; intros a₁ a₂,
      { refl, },
      { calc f^[n + 1] (a₁ ⊔ a₂) = (f^[n] (f (a₁ ⊔ a₂))) : function.iterate_succ_apply f n _
                             ... ≤ (f^[n] ((f a₁) ⊔ a₂)) : f.mono.iterate n (h a₁ a₂)
                             ... ≤ (f^[n] (f a₁)) ⊔ a₂ : ih _ _
                             ... = (f^[n + 1] a₁) ⊔ a₂ : by rw ← function.iterate_succ_apply, }, },
    calc f^[n₁ + n₂] (a₁ ⊔ a₂) = (f^[n₁] (f^[n₂] (a₁ ⊔ a₂))) : function.iterate_add_apply f n₁ n₂ _
                           ... = (f^[n₁] (f^[n₂] (a₂ ⊔ a₁))) : by rw sup_comm
                           ... ≤ (f^[n₁] ((f^[n₂] a₂) ⊔ a₁)) : f.mono.iterate n₁ (h' n₂ _ _)
                           ... = (f^[n₁] (a₁ ⊔ (f^[n₂] a₂))) : by rw sup_comm
                           ... ≤ (f^[n₁] a₁) ⊔ (f^[n₂] a₂) : h' n₁ a₁ _, },
end

end preorder

end order_hom
