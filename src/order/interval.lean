/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.intervals.basic

/-!
# Order intervals

This file defines intervals in an order as pairs where the second element is greater than the first.
This is a prototype for interval arithmetic.
-/

open function order_dual set

/-- The intervals in an order. -/
@[ext] structure interval (α : Type*) [has_le α] extends α × α :=
(fst_le_snd : fst ≤ snd)

namespace interval
variables {α β γ : Type*}

section has_le
variables [has_le α] {a b : interval α}

/-- The injection from which we get the order. -/
def to_dual_prod : interval α → αᵒᵈ × α := interval.to_prod

lemma to_dual_prod_injective : injective (to_dual_prod : interval α → αᵒᵈ × α) :=
λ a b, (ext_iff _ _).2

instance [is_empty α] : is_empty (interval α) := ⟨λ a, is_empty_elim a.fst⟩
instance [subsingleton α] : subsingleton (interval α) := to_dual_prod_injective.subsingleton

instance : has_le (interval α) := ⟨λ a b, b.fst ≤ a.fst ∧ a.snd ≤ b.snd⟩

lemma le_def : a ≤ b ↔ b.fst ≤ a.fst ∧ a.snd ≤ b.snd := iff.rfl

/-- Turn an interval into an interval in the dual order. -/
def dual : interval α ≃ interval αᵒᵈ :=
{ to_fun := λ a, ⟨a.to_prod.swap, a.fst_le_snd⟩,
  inv_fun := λ a, ⟨a.to_prod.swap, a.fst_le_snd⟩,
  left_inv := λ a, ext _ _ $ prod.swap_swap _,
  right_inv := λ a, ext _ _ $ prod.swap_swap _ }

@[simp] lemma fst_dual (a : interval α) : a.dual.fst = to_dual a.snd := rfl
@[simp] lemma snd_dual (a : interval α) : a.dual.snd = to_dual a.fst := rfl

end has_le

section preorder
variables [preorder α] [preorder β] [preorder γ]

instance : preorder (interval α) := preorder.lift interval.to_dual_prod

/-- `{a}` as an interval. -/
@[simps] def pure (a : α) : interval α := ⟨⟨a, a⟩, le_rfl⟩

lemma pure_injective : injective (pure : α → interval α) := λ a b, congr_arg $ prod.fst ∘ to_prod

@[simp] lemma dual_pure (a : α) : (pure a).dual = pure (to_dual a) := rfl

instance [inhabited α] : inhabited (interval α) := ⟨pure default⟩
instance : ∀ [nonempty α], nonempty (interval α) := nonempty.map pure
instance [nontrivial α] : nontrivial (interval α) := pure_injective.nontrivial

/-- Pushforward of intervals. -/
@[simps] def map (f : α →o β) (a : interval α) : interval β :=
⟨a.to_prod.map f f, f.mono a.fst_le_snd⟩

@[simp] lemma map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) := rfl
@[simp] lemma map_map (g : β →o γ) (f : α →o β) (a : interval α) :
  (a.map f).map g = a.map (g.comp f) := rfl

@[simp] lemma dual_map (f : α →o β) (a : interval α) : (a.map f).dual = a.dual.map f.dual := rfl

variables [bounded_order α]

instance : order_top (interval α) :=
{ top := ⟨⟨⊥, ⊤⟩, bot_le⟩,
  le_top := λ a, ⟨bot_le, le_top⟩ }

@[simp] lemma dual_top : (⊤ : interval α).dual = ⊤ := rfl

end preorder

section partial_order
variables [partial_order α]

instance : partial_order (interval α) := partial_order.lift _ to_dual_prod_injective

/-- Consider an interval `[a, b]` as the set `[a, b]`. -/
def to_set : interval α ↪o set α :=
{ to_fun := λ a, Icc a.fst a.snd,
  inj' := λ a b h, begin
    ext,
    { exact (h.symm.subst $ left_mem_Icc.2 b.fst_le_snd).1.antisymm
        (h.subst $ left_mem_Icc.2 a.fst_le_snd).1 },
    { exact (h.subst $ right_mem_Icc.2 a.fst_le_snd).2.antisymm
        (h.symm.subst $ right_mem_Icc.2 b.fst_le_snd).2 }
  end,
  map_rel_iff' := λ a b, Icc_subset_Icc_iff a.fst_le_snd }

@[simp] lemma to_set_dual (a : interval α) : a.dual.to_set = of_dual ⁻¹' a.to_set := dual_Icc
@[simp] lemma to_set_pure (a : α) : (pure a).to_set = {a} := Icc_self _
@[simp] lemma to_set_top [bounded_order α] : (⊤ : interval α).to_set = univ := Icc_bot_top

lemma to_set_nonempty (a : interval α) : a.to_set.nonempty := nonempty_Icc.2 a.fst_le_snd

end partial_order

section lattice
variables [lattice α]

instance : has_sup (interval α) :=
⟨λ a b, ⟨⟨a.fst ⊓ b.fst, a.snd ⊔ b.snd⟩, inf_le_left.trans $ a.fst_le_snd.trans le_sup_left⟩⟩

instance : semilattice_sup (interval α) := to_dual_prod_injective.semilattice_sup _ $ λ _ _, rfl

@[simp] lemma fst_sup (a b : interval α) : (a ⊔ b).fst = a.fst ⊓ b.fst := rfl
@[simp] lemma snd_sup (a b : interval α) : (a ⊔ b).snd = a.snd ⊔ b.snd := rfl

end lattice
end interval
