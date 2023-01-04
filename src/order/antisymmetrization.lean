/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.basic
import logic.relation

/-!
# Turning a preorder into a partial order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `antisymm_rel`: The antisymmetrization relation. `antisymm_rel r a b` means that `a` and `b` are
  related both ways by `r`.
* `antisymmetrization α r`: The quotient of `α` by `antisymm_rel r`. Even when `r` is just a
  preorder, `antisymmetrization α` is a partial order.
-/

open function order_dual

variables {α β : Type*}

section relation
variables (r : α → α → Prop)

/-- The antisymmetrization relation. -/
def antisymm_rel (a b : α) : Prop := r a b ∧ r b a

lemma antisymm_rel_swap : antisymm_rel (swap r) = antisymm_rel r :=
funext $ λ _, funext $ λ _, propext and.comm

@[refl] lemma antisymm_rel_refl [is_refl α r] (a : α) : antisymm_rel r a a := ⟨refl _, refl _⟩

variables {r}

@[symm] lemma antisymm_rel.symm {a b : α} : antisymm_rel r a b → antisymm_rel r b a := and.symm

@[trans] lemma antisymm_rel.trans [is_trans α r] {a b c : α} (hab : antisymm_rel r a b)
  (hbc : antisymm_rel r b c) :
  antisymm_rel r a c :=
⟨trans hab.1 hbc.1, trans hbc.2 hab.2⟩

instance antisymm_rel.decidable_rel [decidable_rel r] : decidable_rel (antisymm_rel r) :=
λ _ _, and.decidable

@[simp] lemma antisymm_rel_iff_eq [is_refl α r] [is_antisymm α r] {a b : α} :
  antisymm_rel r a b ↔ a = b := antisymm_iff

alias antisymm_rel_iff_eq ↔ antisymm_rel.eq _

end relation

section is_preorder
variables (α) (r : α → α → Prop) [is_preorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps] def antisymm_rel.setoid : setoid α :=
⟨antisymm_rel r, antisymm_rel_refl _, λ _ _, antisymm_rel.symm, λ _ _ _, antisymm_rel.trans⟩

/-- The partial order derived from a preorder by making pairwise comparable elements equal. This is
the quotient by `λ a b, a ≤ b ∧ b ≤ a`. -/
def antisymmetrization : Type* := quotient $ antisymm_rel.setoid α r

variables {α}

/-- Turn an element into its antisymmetrization. -/
def to_antisymmetrization : α → antisymmetrization α r := quotient.mk'

/-- Get a representative from the antisymmetrization. -/
noncomputable def of_antisymmetrization : antisymmetrization α r → α := quotient.out'

instance [inhabited α] : inhabited (antisymmetrization α r) := quotient.inhabited _

@[elab_as_eliminator]
protected lemma antisymmetrization.ind {p : antisymmetrization α r → Prop} :
  (∀ a, p $ to_antisymmetrization r a) → ∀ q, p q :=
quot.ind

@[elab_as_eliminator]
protected lemma antisymmetrization.induction_on {p : antisymmetrization α r → Prop}
  (a : antisymmetrization α r) (h : ∀ a, p $ to_antisymmetrization r a) : p a :=
quotient.induction_on' a h

@[simp] lemma to_antisymmetrization_of_antisymmetrization (a : antisymmetrization α r) :
  to_antisymmetrization r (of_antisymmetrization r a) = a := quotient.out_eq' _

end is_preorder

section preorder
variables {α} [preorder α] [preorder β] {a b : α}

lemma antisymm_rel.image {a b : α} (h : antisymm_rel (≤) a b) {f : α → β} (hf : monotone f) :
  antisymm_rel (≤) (f a) (f b) :=
⟨hf h.1, hf h.2⟩

instance : partial_order (antisymmetrization α (≤)) :=
{ le := λ a b, quotient.lift_on₂' a b (≤) $ λ (a₁ a₂ b₁ b₂ : α) h₁ h₂,
    propext ⟨λ h, h₁.2.trans $ h.trans h₂.1, λ h, h₁.1.trans $ h.trans h₂.2⟩,
  lt := λ a b, quotient.lift_on₂' a b (<) $ λ (a₁ a₂ b₁ b₂ : α) h₁ h₂,
    propext ⟨λ h, h₁.2.trans_lt $ h.trans_le h₂.1, λ h, h₁.1.trans_lt $ h.trans_le h₂.2⟩,
  le_refl := λ a, quotient.induction_on' a $ le_refl,
  le_trans := λ a b c, quotient.induction_on₃' a b c $ λ a b c, le_trans,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂' a b $ λ a b, lt_iff_le_not_le,
  le_antisymm := λ a b, quotient.induction_on₂' a b $ λ a b hab hba, quotient.sound' ⟨hab, hba⟩ }

lemma antisymmetrization_fibration :
  relation.fibration (<) (<) (@to_antisymmetrization α (≤) _) :=
by { rintro a ⟨b⟩ h, exact ⟨b, h, rfl⟩ }

lemma acc_antisymmetrization_iff : acc (<) (to_antisymmetrization (≤) a) ↔ acc (<) a :=
⟨λ h, by { have := inv_image.accessible _ h, exact this },
  acc.of_fibration _ antisymmetrization_fibration⟩

lemma well_founded_antisymmetrization_iff :
  well_founded (@has_lt.lt (antisymmetrization α (≤)) _) ↔ well_founded (@has_lt.lt α _) :=
⟨λ h, ⟨λ a, acc_antisymmetrization_iff.1 $ h.apply _⟩,
  λ h, ⟨by { rintro ⟨a⟩, exact acc_antisymmetrization_iff.2 (h.apply a) }⟩⟩

instance [well_founded_lt α] : well_founded_lt (antisymmetrization α (≤)) :=
⟨well_founded_antisymmetrization_iff.2 is_well_founded.wf⟩

instance [@decidable_rel α (≤)] [@decidable_rel α (<)] [is_total α (≤)] :
  linear_order (antisymmetrization α (≤)) :=
{ le_total := λ a b, quotient.induction_on₂' a b $ total_of (≤),
  decidable_eq := @quotient.decidable_eq _ (antisymm_rel.setoid _ (≤)) antisymm_rel.decidable_rel,
  decidable_le := λ _ _, quotient.lift_on₂'.decidable _ _ _ _,
  decidable_lt := λ _ _, quotient.lift_on₂'.decidable _ _ _ _,
  ..antisymmetrization.partial_order }

@[simp] lemma to_antisymmetrization_le_to_antisymmetrization_iff :
  to_antisymmetrization (≤) a ≤ to_antisymmetrization (≤) b ↔ a ≤ b := iff.rfl

@[simp] lemma to_antisymmetrization_lt_to_antisymmetrization_iff :
  to_antisymmetrization (≤) a < to_antisymmetrization (≤) b ↔ a < b := iff.rfl

@[simp] lemma of_antisymmetrization_le_of_antisymmetrization_iff {a b : antisymmetrization α (≤)} :
  of_antisymmetrization (≤) a ≤ of_antisymmetrization (≤) b ↔ a ≤ b :=
by convert to_antisymmetrization_le_to_antisymmetrization_iff.symm;
  exact (to_antisymmetrization_of_antisymmetrization _ _).symm

@[simp] lemma of_antisymmetrization_lt_of_antisymmetrization_iff {a b : antisymmetrization α (≤)} :
  of_antisymmetrization (≤) a < of_antisymmetrization (≤) b ↔ a < b :=
by convert to_antisymmetrization_lt_to_antisymmetrization_iff.symm;
  exact (to_antisymmetrization_of_antisymmetrization _ _).symm

@[mono] lemma to_antisymmetrization_mono : monotone (@to_antisymmetrization α (≤) _) := λ a b, id

/-- `to_antisymmetrization` as an order homomorphism. -/
@[simps] def order_hom.to_antisymmetrization : α →o antisymmetrization α (≤) :=
⟨to_antisymmetrization (≤), λ a b, id⟩

private lemma lift_fun_antisymm_rel (f : α →o β) :
  ((antisymm_rel.setoid α (≤)).r ⇒ (antisymm_rel.setoid β (≤)).r) f f :=
λ a b h, ⟨f.mono h.1, f.mono h.2⟩

/-- Turns an order homomorphism from `α` to `β` into one from `antisymmetrization α` to
`antisymmetrization β`. `antisymmetrization` is actually a functor. See `Preorder_to_PartialOrder`.
-/
protected def order_hom.antisymmetrization (f : α →o β) :
  antisymmetrization α (≤) →o antisymmetrization β (≤) :=
⟨quotient.map' f $ lift_fun_antisymm_rel f, λ a b, quotient.induction_on₂' a b $ f.mono⟩

@[simp] lemma order_hom.coe_antisymmetrization (f : α →o β) :
  ⇑f.antisymmetrization = quotient.map' f (lift_fun_antisymm_rel f) := rfl

@[simp] lemma order_hom.antisymmetrization_apply (f : α →o β) (a : antisymmetrization α (≤)) :
  f.antisymmetrization a = quotient.map' f (lift_fun_antisymm_rel f) a := rfl

@[simp] lemma order_hom.antisymmetrization_apply_mk (f : α →o β) (a : α) :
  f.antisymmetrization (to_antisymmetrization _ a) = (to_antisymmetrization _ (f a)) :=
quotient.map'_mk' f (lift_fun_antisymm_rel f) _

variables (α)

/-- `of_antisymmetrization` as an order embedding. -/
@[simps] noncomputable def order_embedding.of_antisymmetrization : antisymmetrization α (≤) ↪o α :=
{ to_fun := of_antisymmetrization _,
  inj' := λ _ _, quotient.out_inj.1,
  map_rel_iff' := λ a b, of_antisymmetrization_le_of_antisymmetrization_iff }

/-- `antisymmetrization` and `order_dual` commute. -/
def order_iso.dual_antisymmetrization :
  (antisymmetrization α (≤))ᵒᵈ ≃o antisymmetrization αᵒᵈ (≤) :=
{ to_fun := quotient.map' id $ λ _ _, and.symm,
  inv_fun := quotient.map' id $ λ _ _, and.symm,
  left_inv := λ a, quotient.induction_on' a $ λ a, by simp_rw [quotient.map'_mk', id],
  right_inv := λ a, quotient.induction_on' a $ λ a, by simp_rw [quotient.map'_mk', id],
  map_rel_iff' := λ a b, quotient.induction_on₂' a b $ λ a b, iff.rfl }

@[simp] lemma order_iso.dual_antisymmetrization_apply (a : α) :
  order_iso.dual_antisymmetrization _ (to_dual $ to_antisymmetrization _ a) =
    to_antisymmetrization _ (to_dual a) := rfl

@[simp] lemma order_iso.dual_antisymmetrization_symm_apply (a : α) :
  (order_iso.dual_antisymmetrization _).symm (to_antisymmetrization _ $ to_dual a) =
    to_dual (to_antisymmetrization _ a) := rfl

end preorder
