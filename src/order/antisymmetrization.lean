/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.basic

/-!
# Turning a preorder into a partial order

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `order.indistinguishable`: `a` and `b` are order-indistinguishable if `a ≤ b` and `b ≤ a`.
* `antisymmetrization α`: The quotient of `α` by `order.indistinguishable`. Even when `α` is just
  a preorder, `antisymmetrization α` is a partial order.
-/

open function order_dual

variables {α β : Type*}

namespace order
section has_le
variables [has_le α] {a b : α}

/-- `order.indistinguishable a b` means that `a ≤ b` and `b ≤ a`. -/
def indistinguishable (a b : α) : Prop := a ≤ b ∧ b ≤ a

@[symm] lemma indistinguishable.symm : indistinguishable a b → indistinguishable b a := and.symm

instance : is_symm α indistinguishable := ⟨λ a b h, h.symm⟩

instance indistinguishable.decidable_rel [@decidable_rel α (≤)] :
  @decidable_rel α (indistinguishable) := λ _ _, and.decidable

end has_le

section preorder
variables [preorder α] [preorder β] {f : α → β} {a b c : α}

@[refl] lemma indistinguishable_refl (a : α) : indistinguishable a a := ⟨le_rfl, le_rfl⟩
lemma indistinguishable_rfl : indistinguishable a a := indistinguishable_refl _

@[trans] lemma indistinguishable.trans (hab : indistinguishable a b) (hbc : indistinguishable b c) :
  indistinguishable a c :=
⟨hab.1.trans hbc.1, hbc.2.trans hab.2⟩

instance : is_refl α indistinguishable := ⟨indistinguishable_refl⟩
instance : is_trans α indistinguishable := ⟨λ a b c h, h.trans⟩

lemma indistinguishable.image (h : indistinguishable a b) (hf : monotone f) :
  indistinguishable (f a) (f b) :=
⟨hf h.1, hf h.2⟩

variables (α)

/-- `order.indistinguishable` as an equivalence relation. -/
@[simps] def indistinguishable.setoid : setoid α :=
⟨@indistinguishable α _, indistinguishable_refl, λ _ _, symm, λ _ _ _, trans⟩

end preorder

@[simp] lemma indistinguishable_iff_eq [partial_order α] {a b : α} :
  indistinguishable a b ↔ a = b := antisymm_iff

alias indistinguishable_iff_eq ↔ indistinguishable.eq _

attribute [protected] indistinguishable.eq

end order

open order

section preorder
variables (α) [preorder α]

/-- The partial order derived from a preorder by making pairwise comparable elements equal. This is
the quotient by `λ a b, a ≤ b ∧ b ≤ a`. -/
def antisymmetrization : Type* := quotient $ order.indistinguishable.setoid α

variables {α} [preorder β] {a b : α}

/-- Turn an element into its antisymmetrization. -/
def to_antisymmetrization : α → antisymmetrization α := quotient.mk'

/-- Get a representative from the antisymmetrization. -/
noncomputable def of_antisymmetrization : antisymmetrization α → α := quotient.out'

instance [inhabited α] : inhabited (antisymmetrization α) := quotient.inhabited _

@[elab_as_eliminator]
protected lemma antisymmetrization.ind {p : antisymmetrization α → Prop} :
  (∀ a, p $ to_antisymmetrization a) → ∀ q, p q :=
quot.ind

@[elab_as_eliminator]
protected lemma antisymmetrization.induction_on {p : antisymmetrization α → Prop}
  (a : antisymmetrization α) (h : ∀ a, p $ to_antisymmetrization a) : p a :=
quotient.induction_on' a h

@[simp] lemma to_antisymmetrization_of_antisymmetrization (a : antisymmetrization α) :
  to_antisymmetrization (of_antisymmetrization a) = a := quotient.out_eq' _

instance : partial_order (antisymmetrization α) :=
{ le := λ a b, quotient.lift_on₂' a b (≤) $ λ (a₁ a₂ b₁ b₂ : α) h₁ h₂,
    propext ⟨λ h, h₁.2.trans $ h.trans h₂.1, λ h, h₁.1.trans $ h.trans h₂.2⟩,
  lt := λ a b, quotient.lift_on₂' a b (<) $ λ (a₁ a₂ b₁ b₂ : α) h₁ h₂,
    propext ⟨λ h, h₁.2.trans_lt $ h.trans_le h₂.1, λ h, h₁.1.trans_lt $ h.trans_le h₂.2⟩,
  le_refl := λ a, quotient.induction_on' a $ le_refl,
  le_trans := λ a b c, quotient.induction_on₃' a b c $ λ a b c, le_trans,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂' a b $ λ a b, lt_iff_le_not_le,
  le_antisymm := λ a b, quotient.induction_on₂' a b $ λ a b hab hba, quotient.sound' ⟨hab, hba⟩ }

instance [@decidable_rel α (≤)] [@decidable_rel α (<)] [is_total α (≤)] :
  linear_order (antisymmetrization α) :=
{ le_total := λ a b, quotient.induction_on₂' a b $ total_of (≤),
  decidable_eq := @quotient.decidable_eq _ (indistinguishable.setoid _)
    indistinguishable.decidable_rel,
  decidable_le := λ _ _, quotient.lift_on₂'.decidable _ _ _ _,
  decidable_lt := λ _ _, quotient.lift_on₂'.decidable _ _ _ _,
  ..antisymmetrization.partial_order }

@[simp] lemma to_antisymmetrization_le_to_antisymmetrization_iff :
  to_antisymmetrization a ≤ to_antisymmetrization b ↔ a ≤ b := iff.rfl

@[simp] lemma to_antisymmetrization_lt_to_antisymmetrization_iff :
  to_antisymmetrization a < to_antisymmetrization b ↔ a < b := iff.rfl

@[simp] lemma of_antisymmetrization_le_of_antisymmetrization_iff {a b : antisymmetrization α} :
  of_antisymmetrization a ≤ of_antisymmetrization b ↔ a ≤ b :=
by convert to_antisymmetrization_le_to_antisymmetrization_iff.symm;
  exact (to_antisymmetrization_of_antisymmetrization _).symm

@[simp] lemma of_antisymmetrization_lt_of_antisymmetrization_iff {a b : antisymmetrization α} :
  of_antisymmetrization a < of_antisymmetrization b ↔ a < b :=
by convert to_antisymmetrization_lt_to_antisymmetrization_iff.symm;
  exact (to_antisymmetrization_of_antisymmetrization _).symm

@[mono] lemma to_antisymmetrization_mono : monotone (@to_antisymmetrization α _) := λ a b, id

/-- `to_antisymmetrization` as an order homomorphism. -/
@[simps] def order_hom.to_antisymmetrization : α →o antisymmetrization α :=
⟨to_antisymmetrization, λ a b, id⟩

private lemma lift_fun_indistinguishable (f : α →o β) :
  ((indistinguishable.setoid α).r ⇒ (indistinguishable.setoid β).r) f f :=
λ a b h, ⟨f.mono h.1, f.mono h.2⟩

/-- Turns an order homomorphism from `α` to `β` into one from `antisymmetrization α` to
`antisymmetrization β`. `antisymmetrization` is actually a functor. See `Preorder_to_PartialOrder`.
-/
protected def order_hom.antisymmetrization (f : α →o β) :
  antisymmetrization α →o antisymmetrization β :=
⟨quotient.map' f $ lift_fun_indistinguishable f, λ a b, quotient.induction_on₂' a b $ f.mono⟩

@[simp] lemma order_hom.coe_antisymmetrization (f : α →o β) :
  ⇑f.antisymmetrization = quotient.map' f (lift_fun_indistinguishable f) := rfl

@[simp] lemma order_hom.antisymmetrization_apply (f : α →o β) (a : antisymmetrization α) :
  f.antisymmetrization a = quotient.map' f (lift_fun_indistinguishable f) a := rfl

@[simp] lemma order_hom.antisymmetrization_apply_mk (f : α →o β) (a : α) :
  f.antisymmetrization (to_antisymmetrization a) = (to_antisymmetrization (f a)) :=
quotient.map'_mk' f (lift_fun_indistinguishable f) _

variables (α)

/-- `of_antisymmetrization` as an order embedding. -/
@[simps] noncomputable def order_embedding.of_antisymmetrization : antisymmetrization α ↪o α :=
{ to_fun := of_antisymmetrization,
  inj' := λ _ _, quotient.out_inj.1,
  map_rel_iff' := λ a b, of_antisymmetrization_le_of_antisymmetrization_iff }

/-- `antisymmetrization` and `order_dual` commute. -/
def order_iso.dual_antisymmetrization :
  (antisymmetrization α)ᵒᵈ ≃o antisymmetrization αᵒᵈ :=
{ to_fun := quotient.map' id $ λ _ _, and.symm,
  inv_fun := quotient.map' id $ λ _ _, and.symm,
  left_inv := λ a, quotient.induction_on' a $ λ a, by simp_rw [quotient.map'_mk', id],
  right_inv := λ a, quotient.induction_on' a $ λ a, by simp_rw [quotient.map'_mk', id],
  map_rel_iff' := λ a b, quotient.induction_on₂' a b $ λ a b, iff.rfl }

@[simp] lemma order_iso.dual_antisymmetrization_apply (a : α) :
  order_iso.dual_antisymmetrization _ (to_dual $ to_antisymmetrization a) =
    to_antisymmetrization (to_dual a) := rfl

@[simp] lemma order_iso.dual_antisymmetrization_symm_apply (a : α) :
  (order_iso.dual_antisymmetrization _).symm (to_antisymmetrization $ to_dual a) =
    to_dual (to_antisymmetrization a) := rfl

end preorder
