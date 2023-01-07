/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.galois_connection

/-!
# Heyting regular elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines Heyting regular elements, elements of an Heyting algebra that are their own double
complement, and proves that they form a boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.

## Main declarations

* `is_regular`: `a` is Heyting-regular if `aᶜᶜ = a`.
* `regular`: The subtype of Heyting-regular elements.
* `regular.boolean_algebra`: Heyting-regular elements form a boolean algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

open function

variables {α : Type*}

namespace heyting
section has_compl
variables [has_compl α] {a : α}

/-- An element of an Heyting algebra is regular if its double complement is itself. -/
def is_regular (a : α) : Prop := aᶜᶜ = a

protected lemma is_regular.eq : is_regular a → aᶜᶜ = a := id

instance is_regular.decidable_pred [decidable_eq α] : @decidable_pred α is_regular :=
λ _, ‹decidable_eq α› _ _

end has_compl

section heyting_algebra
variables [heyting_algebra α] {a b : α}

lemma is_regular_bot : is_regular (⊥ : α) := by rw [is_regular, compl_bot, compl_top]
lemma is_regular_top : is_regular (⊤ : α) := by rw [is_regular, compl_top, compl_bot]

lemma is_regular.inf (ha : is_regular a) (hb : is_regular b) : is_regular (a ⊓ b) :=
by rw [is_regular, compl_compl_inf_distrib, ha.eq, hb.eq]

lemma is_regular.himp (ha : is_regular a) (hb : is_regular b) : is_regular (a ⇨ b) :=
by rw [is_regular, compl_compl_himp_distrib, ha.eq, hb.eq]

lemma is_regular_compl (a : α) : is_regular aᶜ := compl_compl_compl _

protected lemma is_regular.disjoint_compl_left_iff (ha : is_regular a) : disjoint aᶜ b ↔ b ≤ a :=
by rw [←le_compl_iff_disjoint_left, ha.eq]

protected lemma is_regular.disjoint_compl_right_iff (hb : is_regular b) : disjoint a bᶜ ↔ a ≤ b :=
by rw [←le_compl_iff_disjoint_right, hb.eq]

/-- A Heyting algebra with regular excluded middle is a boolean algebra. -/
@[reducible] -- See note [reducible non-instances]
def _root_.boolean_algebra.of_regular (h : ∀ a : α, is_regular (a ⊔ aᶜ)) : boolean_algebra α :=
have ∀ a : α, is_compl a aᶜ := λ a, ⟨disjoint_compl_right, codisjoint_iff.2 $
  by erw [←(h a).eq, compl_sup, inf_compl_eq_bot, compl_bot]⟩,
{ himp_eq := λ a b, eq_of_forall_le_iff $ λ c,
    le_himp_iff.trans ((this _).le_sup_right_iff_inf_left_le).symm,
  inf_compl_le_bot := λ a, (this _).1.le_bot,
  top_le_sup_compl := λ a, (this _).2.top_le,
  ..‹heyting_algebra α›, ..generalized_heyting_algebra.to_distrib_lattice }

variables (α)

/-- The boolean algebra of Heyting regular elements. -/
def regular : Type* := {a : α // is_regular a}

variables {α}

namespace regular

instance : has_coe (regular α) α := coe_subtype

lemma coe_injective : injective (coe : regular α → α) := subtype.coe_injective
@[simp] lemma coe_inj {a b : regular α} : (a : α) = b ↔ a = b := subtype.coe_inj

instance : has_top (regular α) := ⟨⟨⊤, is_regular_top⟩⟩
instance : has_bot (regular α) := ⟨⟨⊥, is_regular_bot⟩⟩
instance : has_inf (regular α) := ⟨λ a b, ⟨a ⊓ b, a.2.inf b.2⟩⟩
instance : has_himp (regular α) := ⟨λ a b, ⟨a ⇨ b, a.2.himp b.2⟩⟩
instance : has_compl (regular α) := ⟨λ a, ⟨aᶜ, is_regular_compl _⟩⟩

@[simp, norm_cast] lemma coe_top : ((⊤ : regular α) : α) = ⊤ := rfl
@[simp, norm_cast] lemma coe_bot : ((⊥ : regular α) : α) = ⊥ := rfl
@[simp, norm_cast] lemma coe_inf (a b : regular α) : (↑(a ⊓ b) : α) = a ⊓ b := rfl
@[simp, norm_cast] lemma coe_himp (a b : regular α) : (↑(a ⇨ b) : α) = a ⇨ b := rfl
@[simp, norm_cast] lemma coe_compl (a : regular α) : (↑(aᶜ) : α) = aᶜ := rfl

instance : inhabited (regular α) := ⟨⊥⟩
instance : semilattice_inf (regular α) := coe_injective.semilattice_inf _ coe_inf
instance : bounded_order (regular α) := bounded_order.lift coe (λ _ _, id) coe_top coe_bot

@[simp, norm_cast] lemma coe_le_coe {a b : regular α} : (a : α) ≤ b ↔ a ≤ b := iff.rfl
@[simp, norm_cast] lemma coe_lt_coe {a b : regular α} : (a : α) < b ↔ a < b := iff.rfl

/-- **Regularization** of `a`. The smallest regular element greater than `a`. -/
def to_regular : α →o regular α :=
⟨λ a, ⟨aᶜᶜ, is_regular_compl _⟩, λ a b h, coe_le_coe.1 $ compl_le_compl $ compl_le_compl h⟩

@[simp, norm_cast] lemma coe_to_regular (a : α) : (to_regular a : α) = aᶜᶜ := rfl
@[simp] lemma to_regular_coe (a : regular α) : to_regular (a : α) = a := coe_injective a.2

/-- The Galois insertion between `regular.to_regular` and `coe`. -/
def gi : galois_insertion to_regular (coe : regular α → α) :=
{ choice := λ a ha, ⟨a, ha.antisymm le_compl_compl⟩,
  gc := λ a b, coe_le_coe.symm.trans $
    ⟨le_compl_compl.trans, λ h, (compl_anti $ compl_anti h).trans_eq b.2⟩,
  le_l_u := λ _, le_compl_compl,
  choice_eq := λ a ha, coe_injective $ le_compl_compl.antisymm ha }

instance : lattice (regular α) := gi.lift_lattice

@[simp, norm_cast] lemma coe_sup (a b : regular α) : (↑(a ⊔ b) : α) = (a ⊔ b)ᶜᶜ := rfl

instance : boolean_algebra (regular α) :=
{ le_sup_inf := λ a b c, coe_le_coe.1 $ by { dsimp, rw [sup_inf_left, compl_compl_inf_distrib] },
  inf_compl_le_bot := λ a, coe_le_coe.1 $ disjoint_iff_inf_le.1 disjoint_compl_right,
  top_le_sup_compl := λ a, coe_le_coe.1 $
    by { dsimp, rw [compl_sup, inf_compl_eq_bot, compl_bot], refl },
  himp_eq := λ a b, coe_injective begin
    dsimp,
    rw [compl_sup, a.prop.eq],
    refine eq_of_forall_le_iff (λ c, le_himp_iff.trans _),
    rw [le_compl_iff_disjoint_right, disjoint_left_comm, b.prop.disjoint_compl_left_iff],
  end,
  ..regular.lattice, ..regular.bounded_order, ..regular.has_himp,
  ..regular.has_compl }

@[simp, norm_cast] lemma coe_sdiff (a b : regular α) : (↑(a \ b) : α) = a ⊓ bᶜ := rfl

end regular
end heyting_algebra

variables [boolean_algebra α]

lemma is_regular_of_boolean : ∀ a : α, is_regular a := compl_compl

/-- A decidable proposition is intuitionistically Heyting-regular. -/
@[nolint decidable_classical]
lemma is_regular_of_decidable (p : Prop) [decidable p] : is_regular p :=
propext $ decidable.not_not_iff _

end heyting
