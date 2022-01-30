/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.bounded_order

/-!
# Heyting algebras

This file defines Heyting algebras.
-/

variables {ι α : Type*}

/-- Syntax typeclass for Heyting implication. -/
@[notation_class] class has_himp (α : Type*) := (himp : α → α → α)

/-- Syntax typeclass for lattice complement. -/
@[notation_class] class has_compl (α : Type*) := (compl : α → α)

export has_himp (himp) has_compl (compl)

infixr ` ⇨ `:60 := himp
postfix `ᶜ`:(max+1) := compl

/-- A Heyting algebra is a distributive lattice with an additional binary operation called Heyting
implication. -/
class heyting_algebra (α : Type*) extends distrib_lattice α, has_himp α, has_compl α, order_top α :=
(le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c)
(compl_sup_eq_himp (a b : α) : aᶜ ⊔ b = a ⇨ b)

section heyting_algebra
variables [heyting_algebra α] {a b c : α}

-- `p → q → r ↔ p ∧ q → r`
@[simp] lemma le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c := heyting_algebra.le_himp_iff _ _ _

@[simp] lemma compl_sup_eq_himp (a b : α) : aᶜ ⊔ b = a ⇨ b := heyting_algebra.compl_sup_eq_himp _ _
@[simp] lemma sup_compl_eq_himp (a b : α) : b ⊔ aᶜ = a ⇨ b := by rw [sup_comm, compl_sup_eq_himp]

-- `p → q → r ↔ q → p → r`
lemma le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by rw [le_himp_iff, le_himp_iff, inf_comm]

-- `p → q → p`
lemma le_himp (a b : α) : a ≤ b ⇨ a := le_himp_iff.2 inf_le_left

-- `p → p → q ↔ p → q`
@[simp] lemma le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by rw [le_himp_iff, inf_idem]

-- `p → p`
@[simp] lemma himp_self (a : α) : a ⇨ a = ⊤ := top_le_iff.1 $ le_himp_iff.2 inf_le_right

-- `(p → q) ∧ p → q`
lemma himp_inf_le : (a ⇨ b) ⊓ a ≤ b := le_himp_iff.1 le_rfl

-- `p ∧ (p → q) → q`
lemma inf_himp_le : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm, ←le_himp_iff]

-- `p ∧ (p → q) ↔ p ∧ q`
@[simp] lemma inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
le_antisymm (le_inf inf_le_left $ by rw [inf_comm, ←le_himp_iff]) $ inf_le_inf le_rfl $ le_himp _ _

-- `(p → q) ∧ p ↔ q ∧ p`
@[simp] lemma himp_inf (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]

-- example (p q r : Prop) : p → ¬ p ↔ ¬ p := by library_search

@[simp] lemma himp_eq_top : a ⇨ b = ⊤ ↔ a ≤ b := by rw [←top_le_iff, le_himp_iff, top_inf_eq]

-- `p → true`
@[simp] lemma himp_top (a : α) : a ⇨ ⊤ = ⊤ := himp_eq_top.2 le_top

-- `true → p ↔ p`
@[simp] lemma top_himp (a : α) : ⊤ ⇨ a = a := by rw [←sup_compl_eq_himp]

-- `p → ¬ p ↔ ¬ p`
@[simp] lemma himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [←compl_sup_eq_himp, sup_idem]

lemma le_compl_compl (a : α) : a ≤ aᶜᶜ := sorry

lemma himp_himp :

instance pi.heyting_algebra : heyting_algebra (ι → α) :=
by { pi_instance, exact λ a b c, forall_congr (λ i, le_himp_iff) }

variables [order_bot α]

lemma compl_top : (⊤ : α)ᶜ = ⊥ :=
begin
  refine le_bot_iff.1 (sup_eq_right.1 _), rw bot_sup_eq,
end

-- `false → p`
@[simp] lemma bot_himp (a : α) : ⊥ ⇨ a = ⊤ := himp_eq_top.2 bot_le

-- `p → false ↔ ¬ p`
@[simp] lemma himp_bot (a : α) : a ⇨ ⊥ = aᶜ := by rw [←sup_compl_eq_himp, bot_sup_eq]

@[simp] lemma compl_bot : (⊥ : α)ᶜ = ⊤ :=
begin
  refine top_le_iff.1 (sup_eq_right.1 _), rw sup_compl_eq_himp,
end

@[simp] lemma inter_compl_self (a : α) : a ⊓ aᶜ = ⊥ := le_bot_iff.1 $ le_himp_iff.1 begin
  rw ←sup_compl_eq_himp,
end

end heyting_algebra

instance : heyting_algebra Prop :=
{ himp := (→),
  compl := not,
  le_himp_iff := λ p q r, and_imp.symm,
  compl_sup_eq_himp := λ p q, imp_iff_not_or.symm.to_eq,
  ..Prop.distrib_lattice }

/-- Constructs a Heyting algebra, from the Heyting implication alone. -/
@[reducible] -- see note [reducible non instances]
def heyting_algebra.of_himp [distrib_lattice α] [bounded_order α] (himp : α → α → α)
  (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a ⊓ b ≤ c) : heyting_algebra α :=
{ himp := himp,
  compl := λ a, himp a ⊥,
  le_himp_iff := le_himp_iff,
  compl_sup_eq_himp := λ a b, begin
    refine eq_of_forall_le_iff (λ c, _),
    rw [le_himp_iff],
    refine ⟨λ h, _, _⟩,
    {

    }
  end }

/-- Constructs a Heyting algebra, from the Heyting implication alone. -/
@[reducible] -- see note [reducible non instances]
def heyting_algebra.of_compl [distrib_lattice α] [bounded_order α] (compl : α → α)
  (le_himp_iff : ∀ a b c, a ≤ compl b ⊔ c ↔ a ⊓ b ≤ c) : heyting_algebra α :=
{ himp := λ a, (⊔) (compl a),
  compl := compl,
  le_himp_iff := le_himp_iff,
  compl_sup_eq_himp := λ _ _, rfl,
  ..‹distrib_lattice α›, .. ‹bounded_order α› }

/-- A bounded linear order is a Heyting algebra by setting `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = ⊥`
otherwise. -/
@[reducible] -- see note [reducible non instances]
def linear_order.to_heyting_algebra [linear_order α] [bounded_order α] : heyting_algebra \ :=
