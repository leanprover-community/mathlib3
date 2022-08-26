/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.galois_connection

/-!
# The boolean algebra of complemented elements

This file defines Heyting regular elements, elements of an Heyting algebra that are their own double
complement, and proves that they form a boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.
-/

open function

variables {α : Type*}

section heyting_algebra
variables [heyting_algebra α] {a a' b b' : α}

/-- A Heyting algebra where the pseudo-complement is a true complement is a boolean algebra. -/
@[reducible] -- See note [reducible non-instances]
def boolean_algebra.of_is_compl_compl (h : ∀ a : α, is_compl a aᶜ) : boolean_algebra α :=
{ himp_eq := λ a b, eq_of_forall_le_iff $ λ c,
    le_himp_iff.trans ((h _).le_sup_right_iff_inf_left_le).symm,
  inf_compl_le_bot := λ a, (h _).1,
  top_le_sup_compl := λ a, (h _).2,
  ..‹heyting_algebra α›, ..generalized_heyting_algebra.to_distrib_lattice }

/-- A complemented Heyting algebra is a boolean algebra. -/
@[reducible] -- See note [reducible non-instances]
def boolean_algebra.of_complemented [complemented_lattice α] : boolean_algebra α :=
boolean_algebra.of_is_compl_compl $ λ a, let ⟨b, hb⟩ := exists_is_compl a in by rwa hb.compl_eq

lemma is_complemented.himp : is_complemented a → is_complemented b → is_complemented (a ⇨ b) :=
by { rintro ⟨a', ha⟩ ⟨b', hb⟩, refine ⟨a' ⊓ b'ᶜ, sorry⟩ }

lemma is_complemented.compl : is_complemented a → is_complemented aᶜ :=
by { rintro ⟨b, hb⟩, refine ⟨bᶜ, sorry⟩ }

namespace complementeds

instance : has_himp (complementeds α) := ⟨λ a b, ⟨a ⇨ b, a.2.himp b.2⟩⟩
instance : has_compl (complementeds α) := ⟨λ a, ⟨aᶜ, a.2.compl⟩⟩

@[simp, norm_cast] lemma coe_himp (a b : complementeds α) : (↑(a ⇨ b) : α) = a ⇨ b := rfl
@[simp, norm_cast] lemma coe_compl (a : complementeds α) : (↑(aᶜ) : α) = aᶜ := rfl

instance : heyting_algebra (complementeds α) :=
coe_injective.heyting_algebra _ coe_sup coe_inf coe_top coe_bot coe_compl coe_himp

instance : boolean_algebra (complementeds α) := boolean_algebra.of_complemented

end complementeds
end heyting_algebra
