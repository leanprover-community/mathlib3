/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.galois_connection

/-!
# Heyting regular elements

This file defines Heyting regular elements, elements of an Heyting algebra that are their own double
complement, and proves that they form a boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.

## Main declarations

* `is_heyting_regular`: `a` is Heyting-regular if `aᶜᶜ = a`.
* `heyting_regular`: The subtype of Heyting-regular elements.
* `heyting_regular.boolean_algebra`: Heyting-regular elements form a boolean algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

open function

variables {α : Type*}

section heyting_algebra
variables [heyting_algebra α] {a b : α}

/-- An element of an Heyting algebra is regular if its double complement is itself. -/
def is_heyting_regular (a : α) : Prop := aᶜᶜ = a

protected lemma is_heyting_regular.eq : is_heyting_regular a → aᶜᶜ = a := id

lemma is_heyting_regular_bot : is_heyting_regular (⊥ : α) :=
by rw [is_heyting_regular, compl_bot, compl_top]

lemma is_heyting_regular_top : is_heyting_regular (⊤ : α) :=
by rw [is_heyting_regular, compl_top, compl_bot]

lemma is_heyting_regular.inf (ha : is_heyting_regular a) (hb : is_heyting_regular b) :
  is_heyting_regular (a ⊓ b) :=
by rw [is_heyting_regular, compl_compl_inf_distrib, ha.eq, hb.eq]

lemma is_heyting_regular.himp (ha : is_heyting_regular a) (hb : is_heyting_regular b) :
  is_heyting_regular (a ⇨ b) :=
by rw [is_heyting_regular, compl_compl_himp_distrib, ha.eq, hb.eq]

lemma is_heyting_regular_compl (a : α) : is_heyting_regular aᶜ := compl_compl_compl _

protected lemma is_heyting_regular.disjoint_compl_left_iff (ha : is_heyting_regular a) :
  disjoint aᶜ b ↔ b ≤ a :=
by rw [←le_compl_iff_disjoint_left, ha.eq]

protected lemma is_heyting_regular.disjoint_compl_right_iff (hb : is_heyting_regular b) :
  disjoint a bᶜ ↔ a ≤ b :=
by rw [←le_compl_iff_disjoint_right, hb.eq]

/-- A Heyting algebra where all elements are regular is a boolean algebra. -/
@[reducible] -- See note [reducible non-instances]
def boolean_algebra.of_heyting_regular (h : ∀ a : α, is_heyting_regular (a ⊔ aᶜ)) :
  boolean_algebra α :=
have ∀ a : α, is_compl a aᶜ := λ a, ⟨disjoint_compl_right, codisjoint_iff.2 $
  by erw [←(h a).eq, compl_sup, inf_compl_eq_bot, compl_bot]⟩,
{ himp_eq := λ a b, eq_of_forall_le_iff $ λ c,
    le_himp_iff.trans ((this _).le_sup_right_iff_inf_left_le).symm,
  inf_compl_le_bot := λ a, (this _).1,
  top_le_sup_compl := λ a, (this _).2,
  ..‹heyting_algebra α›, ..generalized_heyting_algebra.to_distrib_lattice }

variables (α)

/-- The boolean algebra of Heyting regular elements. -/
def heyting_regular : Type* := {a : α // is_heyting_regular a}

variables {α}

namespace heyting_regular

instance : has_coe (heyting_regular α) α := coe_subtype

lemma coe_injective : injective (coe : heyting_regular α → α) := subtype.coe_injective
@[simp] lemma coe_inj {a b : heyting_regular α} : (a : α) = b ↔ a = b := subtype.coe_inj

instance : has_top (heyting_regular α) := ⟨⟨⊤, is_heyting_regular_top⟩⟩
instance : has_bot (heyting_regular α) := ⟨⟨⊥, is_heyting_regular_bot⟩⟩
instance : has_inf (heyting_regular α) := ⟨λ a b, ⟨a ⊓ b, a.2.inf b.2⟩⟩
instance : has_himp (heyting_regular α) := ⟨λ a b, ⟨a ⇨ b, a.2.himp b.2⟩⟩
instance : has_compl (heyting_regular α) := ⟨λ a, ⟨aᶜ, is_heyting_regular_compl _⟩⟩

@[simp, norm_cast] lemma coe_top : ((⊤ : heyting_regular α) : α) = ⊤ := rfl
@[simp, norm_cast] lemma coe_bot : ((⊥ : heyting_regular α) : α) = ⊥ := rfl
@[simp, norm_cast] lemma coe_inf (a b : heyting_regular α) : (↑(a ⊓ b) : α) = a ⊓ b := rfl
@[simp, norm_cast] lemma coe_himp (a b : heyting_regular α) : (↑(a ⇨ b) : α) = a ⇨ b := rfl
@[simp, norm_cast] lemma coe_compl (a : heyting_regular α) : (↑(aᶜ) : α) = aᶜ := rfl

instance : inhabited (heyting_regular α) := ⟨⊥⟩
instance : semilattice_inf (heyting_regular α) := coe_injective.semilattice_inf _ coe_inf
instance : bounded_order (heyting_regular α) := bounded_order.lift coe (λ _ _, id) coe_top coe_bot

@[simp, norm_cast] lemma coe_le_coe {a b : heyting_regular α} : (a : α) ≤ b ↔ a ≤ b := iff.rfl
@[simp, norm_cast] lemma coe_lt_coe {a b : heyting_regular α} : (a : α) < b ↔ a < b := iff.rfl

/-- The smallest regular element greater than `a`. -/
def to_heyting_regular : α →o heyting_regular α :=
⟨λ a, ⟨aᶜᶜ, is_heyting_regular_compl _⟩, λ a b h, coe_le_coe.1 $ compl_le_compl $ compl_le_compl h⟩

@[simp, norm_cast] lemma coe_to_heyting_regular (a : α) : (to_heyting_regular a : α) = aᶜᶜ := rfl
@[simp] lemma to_heyting_regular_coe (a : heyting_regular α) : to_heyting_regular (a : α) = a :=
coe_injective a.2

/-- The Galois insertion between `heyting_regular.to_heyting_regular` and `coe`. -/
def gi : galois_insertion to_heyting_regular (coe : heyting_regular α → α) :=
{ choice := λ a ha, ⟨a, ha.antisymm le_compl_compl⟩,
  gc := λ a b, coe_le_coe.symm.trans $
    ⟨le_compl_compl.trans, λ h, (compl_anti $ compl_anti h).trans_eq b.2⟩,
  le_l_u := λ _, le_compl_compl,
  choice_eq := λ a ha, coe_injective $ le_compl_compl.antisymm ha }

instance : lattice (heyting_regular α) := gi.lift_lattice

@[simp, norm_cast] lemma coe_sup (a b : heyting_regular α) : (↑(a ⊔ b) : α) = (a ⊔ b)ᶜᶜ := rfl

instance : boolean_algebra (heyting_regular α) :=
{ le_sup_inf := λ a b c, coe_le_coe.1 $ by { dsimp, rw [sup_inf_left, compl_compl_inf_distrib] },
  inf_compl_le_bot := λ a, coe_le_coe.1 disjoint_compl_right,
  top_le_sup_compl := λ a, coe_le_coe.1 $
    by { dsimp, rw [compl_sup, inf_compl_eq_bot, compl_bot], refl },
  himp_eq := λ a b, coe_injective begin
    dsimp,
    rw [compl_sup, a.prop.eq],
    refine eq_of_forall_le_iff (λ c, le_himp_iff.trans _),
    rw [le_compl_iff_disjoint_right, disjoint_left_comm, b.prop.disjoint_compl_left_iff],
  end,
  ..heyting_regular.lattice, ..heyting_regular.bounded_order, ..heyting_regular.has_himp,
  ..heyting_regular.has_compl }

@[simp, norm_cast] lemma coe_sdiff (a b : heyting_regular α) : (↑(a \ b) : α) = a ⊓ bᶜ := rfl

end heyting_regular
end heyting_algebra

variables [boolean_algebra α]

lemma is_heyting_regular_of_boolean : ∀ a : α, is_heyting_regular a := compl_compl
