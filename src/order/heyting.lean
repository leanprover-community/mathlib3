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

open order_dual

variables {ι α β : Type*}

/-! ### Notation -/

/-- Syntax typeclass for Heyting implication. -/
@[notation_class] class has_himp (α : Type*) := (himp : α → α → α)

/-- Syntax typeclass for Heyting negation. -/
@[notation_class] class has_hnot (α : Type*) := (hnot : α → α)

/-- Syntax typeclass for lattice complement. -/
@[notation_class] class has_compl (α : Type*) := (compl : α → α)

export has_himp (himp) has_sdiff (sdiff) has_compl (compl) has_hnot (hnot)

infixr ` ⇨ `:60 := himp
postfix `ᶜ`:(max+1) := compl
prefix `￢ `:40 := hnot

instance [has_himp α] [has_himp β] : has_himp (α × β) := ⟨λ a b, (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩
instance [has_hnot α] [has_hnot β] : has_hnot (α × β) := ⟨λ a, (￢ a.1, ￢ a.2)⟩
instance [has_sdiff α] [has_sdiff β] : has_sdiff (α × β) := ⟨λ a b, (a.1 \ b.1, a.2 \ b.2)⟩
instance [has_compl α] [has_compl β] : has_compl (α × β) := ⟨λ a, (a.1ᶜ, a.2ᶜ)⟩

@[simp] lemma fst_himp [has_himp α] [has_himp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 := rfl
@[simp] lemma snd_himp [has_himp α] [has_himp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 := rfl
@[simp] lemma fst_hnot [has_hnot α] [has_hnot β] (a : α × β) : (￢ a).1 = ￢ a.1 := rfl
@[simp] lemma snd_hnot [has_hnot α] [has_hnot β] (a : α × β) : (￢ a).2 = ￢ a.2 := rfl
@[simp] lemma fst_sdiff [has_sdiff α] [has_sdiff β] (a b : α × β) : (a \ b).1 = a.1 \ b.1 := rfl
@[simp] lemma snd_sdiff [has_sdiff α] [has_sdiff β] (a b : α × β) : (a \ b).2 = a.2 \ b.2 := rfl
@[simp] lemma fst_compl [has_compl α] [has_compl β] (a : α × β) : aᶜ.1 = a.1ᶜ := rfl
@[simp] lemma snd_compl [has_compl α] [has_compl β] (a : α × β) : aᶜ.2 = a.2ᶜ := rfl

namespace pi
variables {π : ι → Type*}

instance [Π i, has_himp (π i)] : has_himp (Π i, π i) := ⟨λ a b i, a i ⇨ b i⟩
instance [Π i, has_hnot (π i)] : has_hnot (Π i, π i) := ⟨λ a i, ￢ a i⟩
instance [Π i, has_compl (π i)] : has_compl (Π i, π i) := ⟨λ a i, (a i)ᶜ⟩
instance [Π i, has_sdiff (π i)] : has_sdiff (Π i, π i) := ⟨λ a b i, a i \ b i⟩

lemma himp_def [Π i, has_himp (α i)] (a b : Π i, α i) : (a ⇨ b) = λ i, a i ⇨ b i := rfl
lemma hnot_def [Π i, hnot_def (α i)] (a : Π i, α i) : ￢ a = λ i, ￢ a i := rfl
lemma sdiff_def [Π i, has_sdiff (α i)] (a b : Π i, α i) : a \ b = λ i, a i \ b i := rfl
lemma compl_def [Π i, has_compl (α i)] (a : Π i, α i) : aᶜ = λ i, (a i)ᶜ := rfl

@[simp] lemma himp_apply [Π i, has_himp (π i)] (a b : Π i, π i) (i : ι) : (a ⇨ b) i = a i ⇨ b i :=
rfl
@[simp] lemma hnot_apply [Π i, has_hnot (π i)] (a : Π i, π i) (i : ι) : (￢ a) i = ￢ a i := rfl
@[simp] lemma sdiff_apply [Π i, has_sdiff (π i)] (a b : Π i, π i) (i : ι) : (a \ b) i = a i \ b i :=
@[simp] lemma compl_apply [Π i, has_compl (π i)] (a : Π i, π i) (i : ι) : aᶜ i = (a i)ᶜ := rfl
rfl

end pi

/-- A Heyting algebra is a lattice with an additional binary operation `⇨` called Heyting
implication such that `a ⇨` is right adjoint to `a ⊓`. -/
class heyting_algebra (α : Type*) extends lattice α, bounded_order α, has_himp α, has_compl α :=
(le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c)
(himp_bot (a : α) : a ⇨ ⊥ = aᶜ)

/-- A Brouwer algebra is a lattice with an additional binary difference operation `\` such that
`\ a` is right adjoint to `⊔ a`. -/
class brouwer_algebra (α : Type*) extends lattice α, bounded_order α, has_hnot α, has_sdiff α :=
(sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c)
(top_sdiff (a : α) : ⊤ \ a = ￢a)

/-- A bi-Heyting algebra is a Heyting algebra that is also a Brouwer algebra. -/
class biheyting_algebra (α : Type*) extends heyting_algebra α, has_hnot α, has_sdiff α :=
(sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ⊓ b ≤ c)
(top_sdiff (a : α) : ⊤ \ a = ￢a)

section heyting_algebra
variables [heyting_algebra α] {a b c : α}

-- `p → q → r ↔ p ∧ q → r`
@[simp] lemma le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c := heyting_algebra.le_himp_iff _ _ _
-- lemma himp_sup_gc (a : α) : galois_connection ((⇨) a) (⊓ b) :=

-- `p → false ↔ ¬ p`
@[simp] lemma himp_bot (a : α) : a ⇨ ⊥ = aᶜ := heyting_algebra.himp_bot _

instance : brouwer_algebra (order_dual α) :=
{ hnot := to_dual ∘ compl ∘ of_dual,
  sdiff := λ a b, to_dual (of_dual b ⇨ of_dual a),
  sdiff_le_iff := λ a b c, by { rw sup_comm, exact le_himp_iff },
  top_sdiff := himp_bot,
  ..order_dual.lattice α, ..order_dual.bounded_order α }

@[simp] lemma compl_of_dual (a : order_dual α) : (of_dual a)ᶜ = of_dual (￢ a) := rfl

@[simp] lemma hnot_to_dual (a : α) : ￢ to_dual a = to_dual (aᶜ) := rfl

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

-- @[simp] lemma himp_eq_bot : a ⇨ b = ⊥ ↔ a ≤ bᶜ := by rw [←himp_bot, le_himp_iff, ←le_bot_iff]

@[simp] lemma le_compl_iff : a ≤ bᶜ ↔ disjoint a b := by rw [←himp_bot, le_himp_iff, disjoint]

-- `p → true`
@[simp] lemma himp_top (a : α) : a ⇨ ⊤ = ⊤ := himp_eq_top.2 le_top

-- `true → p ↔ p`
@[simp] lemma top_himp (a : α) : ⊤ ⇨ a = a :=
eq_of_forall_le_iff $ λ b, by rw [le_himp_iff, inf_top_eq]

-- `false → p`
@[simp] lemma bot_himp (a : α) : ⊥ ⇨ a = ⊤ := himp_eq_top.2 bot_le

-- `p → ¬ p ↔ ¬ p`
@[simp] lemma himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [←compl_sup_eq_himp, sup_idem]

lemma le_compl_compl (a : α) : a ≤ aᶜᶜ := sorry

lemma himp_himp :

lemma compl_top : (⊤ : α)ᶜ = ⊥ :=
begin
  refine le_bot_iff.1 (sup_eq_right.1 _), rw bot_sup_eq,
end

@[simp] lemma compl_bot : (⊥ : α)ᶜ = ⊤ :=
begin
  refine top_le_iff.1 (sup_eq_right.1 _), rw sup_compl_eq_himp,
end

@[simp] lemma inter_compl_self (a : α) : a ⊓ aᶜ = ⊥ := le_bot_iff.1 $ le_himp_iff.1 begin
  rw ←sup_compl_eq_himp,
end

instance prod.heyting_algebra [heyting_algebra β] : heyting_algebra (α × β) :=
{ le_himp_iff := λ a b c, and_congr le_himp_iff le_himp_iff,
  himp_bot := λ a, prod.ext (himp_bot a.1) (himp_bot a.2),
  ..prod.lattice α β, ..prod.bounded_order α β, ..prod.has_himp, ..prod.has_compl }

instance pi.heyting_algebra : heyting_algebra (ι → α) :=
by { pi_instance, exact λ a b c, forall_congr (λ i, le_himp_iff) }

end heyting_algebra

instance : heyting_algebra Prop :=
{ himp := (→),
  compl := not,
  le_himp_iff := λ p q r, and_imp.symm,
  himp_bot := λ p, rfl,
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
