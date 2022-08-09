/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.bounded_order

/-!
# Heyting algebras

This file defines Heyting algebras.

## Main declarations

* `generalized_heyting_algebra`
* `generalized_coheyting_algebra`
* `heyting_algebra`
* `coheyting_algebra`
* `biheyting_algebra`
-/

set_option old_structure_cmd true

open order_dual

universes u
variables {ι α β : Type*}

/-! ### Notation -/

/-- Syntax typeclass for Heyting implication. -/
@[notation_class] class has_himp (α : Type*) := (himp : α → α → α)

/-- Syntax typeclass for Heyting negation. -/
@[notation_class] class has_hnot (α : Type*) := (hnot : α → α)

export has_himp (himp) has_sdiff (sdiff) has_hnot (hnot)

infixr ` ⇨ `:60 := himp
prefix `￢`:72 := hnot

instance [has_himp α] [has_himp β] : has_himp (α × β) := ⟨λ a b, (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩
instance [has_hnot α] [has_hnot β] : has_hnot (α × β) := ⟨λ a, (￢a.1, ￢a.2)⟩
instance [has_sdiff α] [has_sdiff β] : has_sdiff (α × β) := ⟨λ a b, (a.1 \ b.1, a.2 \ b.2)⟩
instance [has_compl α] [has_compl β] : has_compl (α × β) := ⟨λ a, (a.1ᶜ, a.2ᶜ)⟩

@[simp] lemma fst_himp [has_himp α] [has_himp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 := rfl
@[simp] lemma snd_himp [has_himp α] [has_himp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 := rfl
@[simp] lemma fst_hnot [has_hnot α] [has_hnot β] (a : α × β) : (￢a).1 = ￢a.1 := rfl
@[simp] lemma snd_hnot [has_hnot α] [has_hnot β] (a : α × β) : (￢a).2 = ￢a.2 := rfl
@[simp] lemma fst_sdiff [has_sdiff α] [has_sdiff β] (a b : α × β) : (a \ b).1 = a.1 \ b.1 := rfl
@[simp] lemma snd_sdiff [has_sdiff α] [has_sdiff β] (a b : α × β) : (a \ b).2 = a.2 \ b.2 := rfl
@[simp] lemma fst_compl [has_compl α] [has_compl β] (a : α × β) : aᶜ.1 = a.1ᶜ := rfl
@[simp] lemma snd_compl [has_compl α] [has_compl β] (a : α × β) : aᶜ.2 = a.2ᶜ := rfl

namespace pi
variables {π : ι → Type*}

instance [Π i, has_himp (π i)] : has_himp (Π i, π i) := ⟨λ a b i, a i ⇨ b i⟩
instance [Π i, has_hnot (π i)] : has_hnot (Π i, π i) := ⟨λ a i, ￢a i⟩

lemma himp_def [Π i, has_himp (π i)] (a b : Π i, π i) : (a ⇨ b) = λ i, a i ⇨ b i := rfl
lemma hnot_def [Π i, has_hnot (π i)] (a : Π i, π i) : ￢a = λ i, ￢a i := rfl

@[simp] lemma himp_apply [Π i, has_himp (π i)] (a b : Π i, π i) (i : ι) : (a ⇨ b) i = a i ⇨ b i :=
rfl
@[simp] lemma hnot_apply [Π i, has_hnot (π i)] (a : Π i, π i) (i : ι) : (￢a) i = ￢a i := rfl

end pi

/-- A generalized Heyting algebra is a lattice with an additional binary operation `⇨` called
Heyting implication such that `a ⇨` is right adjoint to `a ⊓`. -/
class generalized_heyting_algebra (α : Type*) extends lattice α, has_top α, has_himp α :=
(le_top : ∀ a : α, a ≤ ⊤)
(le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c)

/-- A generalized co-Heyting algebra is a lattice with an additional binary difference operation `\`
such that `\ a` is right adjoint to `⊔ a`. -/
class generalized_coheyting_algebra (α : Type*) extends lattice α, has_bot α, has_sdiff α :=
(bot_le : ∀ a : α, ⊥ ≤ a)
(sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c)

/-- A Heyting algebra is a bounded lattice with an additional binary operation `⇨` called Heyting
implication such that `a ⇨` is right adjoint to `a ⊓`. -/
class heyting_algebra (α : Type*) extends generalized_heyting_algebra α, has_bot α, has_compl α :=
(bot_le : ∀ a : α, ⊥ ≤ a)
(himp_bot (a : α) : a ⇨ ⊥ = aᶜ)

/-- A co-Heyting algebra is a bounded  lattice with an additional binary difference operation `\`
such that `\ a` is right adjoint to `⊔ a`. -/
class coheyting_algebra (α : Type*)
  extends generalized_coheyting_algebra α, has_top α, has_hnot α :=
(le_top : ∀ a : α, a ≤ ⊤)
(top_sdiff (a : α) : ⊤ \ a = ￢a)

/-- A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra. -/
class biheyting_algebra (α : Type*) extends heyting_algebra α, has_sdiff α, has_hnot α :=
(sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c)
(top_sdiff (a : α) : ⊤ \ a = ￢a)

@[priority 100] -- See note [lower instance priority]
instance generalized_heyting_algebra.to_order_top [generalized_heyting_algebra α] : order_top α :=
{ ..‹generalized_heyting_algebra α› }

@[priority 100] -- See note [lower instance priority]
instance generalized_coheyting_algebra.to_order_bot [generalized_coheyting_algebra α] :
  order_bot α :=
{ ..‹generalized_coheyting_algebra α› }

@[priority 100] -- See note [lower instance priority]
instance heyting_algebra.to_bounded_order [heyting_algebra α] : bounded_order α :=
{ ..‹heyting_algebra α› }

@[priority 100] -- See note [lower instance priority]
instance coheyting_algebra.to_bounded_order [coheyting_algebra α] : bounded_order α :=
{ ..‹coheyting_algebra α› }

@[priority 100] -- See note [lower instance priority]
instance biheyting_algebra.to_coheyting_algebra [biheyting_algebra α] : coheyting_algebra α :=
{ ..‹biheyting_algebra α› }

/-- Construct a Heyting algebra from the Heyting implication alone. -/
@[reducible] -- See note [reducible non instances]
def heyting_algebra.of_himp [distrib_lattice α] [bounded_order α] (himp : α → α → α)
  (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a ⊓ b ≤ c) : heyting_algebra α :=
{ himp := himp,
  compl := λ a, himp a ⊥,
  le_himp_iff := le_himp_iff,
  himp_bot := λ a, rfl,
  ..‹distrib_lattice α›, ..‹bounded_order α› }

/-- Construct a Heyting algebra from the Heyting implication alone. -/
@[reducible] -- See note [reducible non instances]
def heyting_algebra.of_compl [distrib_lattice α] [bounded_order α] (compl : α → α)
  (le_himp_iff : ∀ a b c, a ≤ compl b ⊔ c ↔ a ⊓ b ≤ c) : heyting_algebra α :=
{ himp := λ a, (⊔) (compl a),
  compl := compl,
  le_himp_iff := le_himp_iff,
  himp_bot := λ a, sup_bot_eq,
  ..‹distrib_lattice α›, ..‹bounded_order α› }

/-- Construct a co-Heyting algebra from the difference alone. -/
@[reducible] -- See note [reducible non instances]
def coheyting_algebra.of_sdiff [distrib_lattice α] [bounded_order α] (sdiff : α → α → α)
  (sdiff_le_iff : ∀ a b c, sdiff a b ≤ c ↔ a ≤ b ⊔ c) : coheyting_algebra α :=
{ sdiff := sdiff,
  hnot := λ a, sdiff ⊤ a,
  sdiff_le_iff := sdiff_le_iff,
  top_sdiff := λ a, rfl,
  ..‹distrib_lattice α›, ..‹bounded_order α› }

/-- Construct a co-Heyting algebra from the Heyting negation alone. -/
@[reducible] -- See note [reducible non instances]
def coheyting_algebra.of_hnot [distrib_lattice α] [bounded_order α] (hnot : α → α)
  (sdiff_le_iff : ∀ a b c, a ⊓ hnot b ≤ c ↔ a ≤ b ⊔ c) : coheyting_algebra α :=
{ sdiff := λ a b, (a ⊓ hnot b),
  hnot := hnot,
  sdiff_le_iff := sdiff_le_iff,
  top_sdiff := λ a, top_inf_eq,
  ..‹distrib_lattice α›, ..‹bounded_order α› }

section generalized_heyting_algebra
variables [generalized_heyting_algebra α] {a b c d : α}

-- `p → q → r ↔ p ∧ q → r`
@[simp] lemma le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c := generalized_heyting_algebra.le_himp_iff _ _ _

-- `p → q → r ↔ q → p → r`
lemma le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by rw [le_himp_iff, le_himp_iff, inf_comm]

-- `p → q → p`
lemma le_himp : a ≤ b ⇨ a := le_himp_iff.2 inf_le_left

-- `p → p → q ↔ p → q`
@[simp] lemma le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by rw [le_himp_iff, inf_idem]

-- `p → p`
@[simp] lemma himp_self (a : α) : a ⇨ a = ⊤ := top_le_iff.1 $ le_himp_iff.2 inf_le_right

-- `(p → q) ∧ p → q`
lemma himp_inf_le : (a ⇨ b) ⊓ a ≤ b := le_himp_iff.1 le_rfl

-- `p ∧ (p → q) → q`
lemma inf_himp_le (a b : α) : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm, ←le_himp_iff]

-- `p ∧ (p → q) ↔ p ∧ q`
@[simp] lemma inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
le_antisymm (le_inf inf_le_left $ by rw [inf_comm, ←le_himp_iff]) $ inf_le_inf_left _ le_himp

-- `(p → q) ∧ p ↔ q ∧ p`
@[simp] lemma himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]

@[simp] lemma himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by rw [←top_le_iff, le_himp_iff, top_inf_eq]

-- `p → true`
@[simp] lemma himp_top (a : α) : a ⇨ ⊤ = ⊤ := himp_eq_top_iff.2 le_top

-- `true → p ↔ p`
@[simp] lemma top_himp (a : α) : ⊤ ⇨ a = a :=
eq_of_forall_le_iff $ λ b, by rw [le_himp_iff, inf_top_eq]

-- `p → q → r ↔ p ∧ q → r`
lemma himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c :=
eq_of_forall_le_iff $ λ d, by simp_rw [le_himp_iff, inf_assoc]

-- `(q → r) → (p → q) → q → r`
@[simp] lemma himp_le_himp_himp (a b c : α) : b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c :=
begin
  rw [le_himp_iff, le_himp_iff, inf_assoc, himp_inf_self, ←inf_assoc, himp_inf_self, inf_assoc],
  exact inf_le_left,
end

-- `p → q → r ↔ q → p → r`
lemma himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by simp_rw [himp_himp, inf_comm]

lemma himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) :=
eq_of_forall_le_iff $ λ d, by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

lemma sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
eq_of_forall_le_iff $ λ d, by { rw [le_inf_iff, le_himp_comm, sup_le_iff], simp_rw le_himp_comm }

lemma himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b := le_himp_iff.2 $ himp_inf_le.trans h

lemma himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c :=
le_himp_iff.2 $ (inf_le_inf_left _ h).trans himp_inf_le

lemma himp_le_himp (hab : a ≤ b) (hcd : c ≤ d) : b ⇨ c ≤ a ⇨ d :=
(himp_le_himp_right hab).trans $ himp_le_himp_left hcd

@[priority 100] -- See note [lower instance priority]
instance generalized_heyting_algebra.to_distrib_lattice : distrib_lattice α :=
distrib_lattice.of_inf_sup_le $ λ a b c,
  by simp_rw [@inf_comm _ _ a, ←le_himp_iff, sup_le_iff, le_himp_iff, ←sup_le_iff]

instance : generalized_coheyting_algebra αᵒᵈ :=
{ sdiff := λ a b, to_dual (of_dual b ⇨ of_dual a),
  sdiff_le_iff := λ a b c, by { rw sup_comm, exact le_himp_iff },
  ..order_dual.lattice α, ..order_dual.order_bot α }

instance prod.generalized_heyting_algebra [generalized_heyting_algebra β] :
  generalized_heyting_algebra (α × β) :=
{ le_himp_iff := λ a b c, and_congr le_himp_iff le_himp_iff,
  ..prod.lattice α β, ..prod.order_top α β, ..prod.has_himp, ..prod.has_compl }

instance pi.generalized_heyting_algebra {α : ι → Type*} [Π i, generalized_heyting_algebra (α i)] :
  generalized_heyting_algebra (Π i, α i) :=
by { pi_instance, exact λ a b c, forall_congr (λ i, le_himp_iff) }

end generalized_heyting_algebra

section generalized_coheyting_algebra
variables [generalized_coheyting_algebra α] {a b c d : α}

@[simp] lemma sdiff_le_iff : a \ b ≤ c ↔ a ≤ b ⊔ c := generalized_coheyting_algebra.sdiff_le_iff _ _ _

lemma sdiff_le_comm : a \ b ≤ c ↔ a \ c ≤ b := by rw [sdiff_le_iff, sdiff_le_iff, sup_comm]

lemma sdiff_le : a \ b ≤ a := sdiff_le_iff.2 le_sup_right

lemma disjoint.disjoint_sdiff_left (h : disjoint a b) : disjoint (a \ c) b := h.mono_left sdiff_le
lemma disjoint.disjoint_sdiff_right (h : disjoint a b) : disjoint a (b \ c) := h.mono_right sdiff_le

@[simp] lemma sdiff_le_iff_left : a \ b ≤ b ↔ a ≤ b := by rw [sdiff_le_iff, sup_idem]

@[simp] lemma sdiff_self (a : α) : a \ a = ⊥ := le_bot_iff.1 $ sdiff_le_iff.2 le_sup_left

lemma le_sup_sdiff : a ≤ b ⊔ a \ b := sdiff_le_iff.1 le_rfl
lemma le_sdiff_sup : a ≤ a \ b ⊔ b := by rw [sup_comm, ←sdiff_le_iff]

@[simp] lemma sup_sdiff_self (a b : α) : a ⊔ b \ a = a ⊔ b :=
le_antisymm (sup_le_sup_left sdiff_le _) (sup_le le_sup_left le_sup_sdiff)

@[simp] lemma sdiff_sup_self (a b : α) : b \ a ⊔ a = b ⊔ a :=
by rw [sup_comm, sup_sdiff_self, sup_comm]

@[simp] lemma sdiff_eq_bot_iff : a \ b = ⊥ ↔ a ≤ b := by rw [←le_bot_iff, sdiff_le_iff, sup_bot_eq]

@[simp] lemma sdiff_bot (a : α) : a \ ⊥ = a :=
eq_of_forall_ge_iff $ λ b, by rw [sdiff_le_iff, bot_sup_eq]

@[simp] lemma bot_sdiff (a : α) : ⊥ \ a = ⊥ := sdiff_eq_bot_iff.2 bot_le

lemma sdiff_sdiff (a b c : α) : a \ b \ c = a \ (b ⊔ c) :=
eq_of_forall_ge_iff $ λ d, by simp_rw [sdiff_le_iff, sup_assoc]

@[simp] lemma sdiff_sdiff_le_sdiff : a \ b \ (a \ c) ≤ c \ b :=
begin
  rw [sdiff_le_iff, sdiff_le_iff, sup_left_comm, sup_sdiff_self, sup_left_comm, sdiff_sup_self,
    sup_left_comm],
  exact le_sup_left,
end

lemma sdiff_right_comm (a b c : α) : a \ b \ c = a \ c \ b := by simp_rw [sdiff_sdiff, sup_comm]

lemma sdiff_le_sdiff_right (h : a ≤ b) : a \ c ≤ b \ c := sdiff_le_iff.2 $ h.trans $ le_sup_sdiff

lemma sdiff_le_sdiff_left (h : a ≤ b) : c \ b ≤ c \ a :=
sdiff_le_iff.2 $ le_sup_sdiff.trans $ sup_le_sup_right h _

lemma sdiff_le_sdiff (hab : a ≤ b) (hcd : c ≤ d) : a \ d ≤ b \ c :=
(sdiff_le_sdiff_right hab).trans $ sdiff_le_sdiff_left hcd

lemma sup_sdiff_distrib (a b c : α) : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
eq_of_forall_ge_iff $ λ d, by simp_rw [sdiff_le_iff, sup_le_iff, sdiff_le_iff]

lemma sdiff_inf_distrib (a b c : α) : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
eq_of_forall_ge_iff $ λ d, by { rw [sup_le_iff, sdiff_le_comm, le_inf_iff], simp_rw sdiff_le_comm }

-- cf. `is_compl.inf_sup`
lemma sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c := sdiff_inf_distrib _ _ _

@[simp] lemma sdiff_inf_self_right (a b : α) : b \ (a ⊓ b) = b \ a :=
by rw [sdiff_inf, sdiff_self, sup_bot_eq]

@[simp] lemma sdiff_inf_self_left (a b : α) : a \ (a ⊓ b) = a \ b :=
by rw [inf_comm, sdiff_inf_self_right]

@[priority 100] -- See note [lower instance priority]
instance generalized_coheyting_algebra.to_distrib_lattice : distrib_lattice α :=
{ le_sup_inf := λ a b c, by simp_rw [←sdiff_le_iff, le_inf_iff, sdiff_le_iff, ←le_inf_iff],
  ..‹generalized_coheyting_algebra α› }

instance : generalized_heyting_algebra αᵒᵈ :=
{ himp := λ a b, to_dual (of_dual b \ of_dual a),
  le_himp_iff := λ a b c, by { rw inf_comm, exact sdiff_le_iff },
  ..order_dual.lattice α, ..order_dual.order_top α }

instance prod.generalized_coheyting_algebra [generalized_coheyting_algebra β] : generalized_coheyting_algebra (α × β) :=
{ sdiff_le_iff := λ a b c, and_congr sdiff_le_iff sdiff_le_iff,
  ..prod.lattice α β, ..prod.order_bot α β, ..prod.has_sdiff, ..prod.has_hnot }

instance pi.generalized_coheyting_algebra {α : ι → Type*}
  [Π i, generalized_coheyting_algebra (α i)] : generalized_coheyting_algebra (Π i, α i) :=
by { pi_instance, exact λ a b c, forall_congr (λ i, sdiff_le_iff) }

end generalized_coheyting_algebra

section heyting_algebra
variables [heyting_algebra α] {a b c : α}

@[simp] lemma himp_bot (a : α) : a ⇨ ⊥ = aᶜ := heyting_algebra.himp_bot _
@[simp] lemma bot_himp (a : α) : ⊥ ⇨ a = ⊤ := himp_eq_top_iff.2 bot_le

lemma compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by simp_rw [←himp_bot, sup_himp_distrib]

lemma compl_le_himp : aᶜ ≤ a ⇨ b := (himp_bot _).ge.trans $ himp_le_himp_left bot_le

lemma compl_sup_le_himp : aᶜ ⊔ b ≤ a ⇨ b := sup_le compl_le_himp le_himp

-- `p → ¬ p ↔ ¬ p`
@[simp] lemma himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [←himp_bot, himp_himp, inf_idem]

-- `p → ¬ q ↔ q → ¬ p`
lemma himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by simp_rw [←himp_bot, himp_left_comm]

lemma le_compl_iff_disjoint_right : a ≤ bᶜ ↔ disjoint a b :=
by rw [←himp_bot, le_himp_iff, disjoint]

lemma le_compl_iff_disjoint_left : a ≤ bᶜ ↔ disjoint b a :=
le_compl_iff_disjoint_right.trans disjoint.comm

lemma le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ :=
by rw [le_compl_iff_disjoint_right, le_compl_iff_disjoint_left]

alias le_compl_iff_disjoint_right ↔ _ disjoint.le_compl_right
alias le_compl_iff_disjoint_left ↔ _ disjoint.le_compl_left

lemma disjoint_compl_left (a : α) : disjoint aᶜ a := le_himp_iff.1 (himp_bot _).ge
lemma disjoint_compl_right (a : α) : disjoint a aᶜ := (disjoint_compl_left _).symm

@[simp] lemma inf_compl_self (a : α) : a ⊓ aᶜ = ⊥ := (disjoint_compl_right _).eq_bot
@[simp] lemma compl_inf_self (a : α) : aᶜ ⊓ a = ⊥ := (disjoint_compl_left _).eq_bot

@[simp] lemma compl_top : (⊤ : α)ᶜ = ⊥ :=
eq_of_forall_le_iff $ λ a, by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]

@[simp] lemma compl_bot : (⊥ : α)ᶜ = ⊤ := by rw [←himp_bot, himp_self]

lemma le_compl_compl : a ≤ aᶜᶜ := (disjoint_compl_right _).le_compl_right

lemma compl_anti : antitone (compl : α → α) := λ a b h, le_compl_comm.1 $ h.trans le_compl_compl

@[simp] lemma compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
(compl_anti le_compl_compl).antisymm le_compl_compl

@[simp] lemma disjoint_compl_compl_left_iff : disjoint aᶜᶜ b ↔ disjoint a b :=
by simp_rw [←le_compl_iff_disjoint_left, compl_compl_compl]

@[simp] lemma disjoint_compl_compl_right_iff : disjoint a bᶜᶜ ↔ disjoint a b :=
by simp_rw [←le_compl_iff_disjoint_right, compl_compl_compl]

lemma compl_sup_compl_le :  aᶜ ⊔ bᶜ ≤ (a ⊓ b)ᶜ :=
sup_le (compl_anti inf_le_left) $ compl_anti inf_le_right

lemma compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ :=
begin
  refine ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm _,
  rw [le_compl_iff_disjoint_right, disjoint_assoc, disjoint_compl_compl_left_iff,
    disjoint_left_comm, disjoint_compl_compl_left_iff, ←disjoint_assoc, inf_comm],
  exact disjoint_compl_right _,
end

lemma compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ :=
begin
  refine le_antisymm _ _,
  { rw [le_himp_iff, ←compl_compl_inf_distrib],
    exact compl_anti (compl_anti himp_inf_le) },
  { refine le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans _),
    rw [compl_sup_distrib, le_compl_iff_disjoint_right, disjoint_right_comm,
      ←le_compl_iff_disjoint_right],
    exact inf_himp_le _ _ }
end

instance : coheyting_algebra αᵒᵈ :=
{ hnot := to_dual ∘ compl ∘ of_dual,
  sdiff := λ a b, to_dual (of_dual b ⇨ of_dual a),
  sdiff_le_iff := λ a b c, by { rw sup_comm, exact le_himp_iff },
  top_sdiff := himp_bot,
  ..order_dual.lattice α, ..order_dual.bounded_order α }

@[simp] lemma of_dual_hnot (a : αᵒᵈ) : of_dual ￢a = (of_dual a)ᶜ := rfl
@[simp] lemma to_dual_compl (a : α) : to_dual aᶜ = ￢to_dual a := rfl

instance prod.heyting_algebra [heyting_algebra β] : heyting_algebra (α × β) :=
{ himp_bot := λ a, prod.ext (himp_bot a.1) (himp_bot a.2),
  ..prod.generalized_heyting_algebra, ..prod.bounded_order α β, ..prod.has_compl }

instance pi.heyting_algebra {α : ι → Type*} [Π i, heyting_algebra (α i)] :
  heyting_algebra (Π i, α i) :=
by { pi_instance, exact λ a b c, forall_congr (λ i, le_himp_iff) }

end heyting_algebra

section coheyting_algebra
variables [coheyting_algebra α] {a b c : α}

@[simp] lemma top_sdiff' (a : α) : ⊤ \ a = ￢a := coheyting_algebra.top_sdiff _
@[simp] lemma sdiff_top (a : α) : a \ ⊤ = ⊥ := sdiff_eq_bot_iff.2 le_top

lemma hnot_inf_distrib (a b : α) : ￢ (a ⊓ b) = ￢a ⊔ ￢b :=
by simp_rw [←top_sdiff', sdiff_inf_distrib]

lemma sdiff_le_hnot : a \ b ≤ ￢b := (sdiff_le_sdiff_right le_top).trans_eq $ top_sdiff' _

lemma sdiff_le_inf_hnot : a \ b ≤ a ⊓ ￢b := le_inf sdiff_le sdiff_le_hnot

@[priority 100] -- See note [lower instance priority]
instance coheyting_algebra.to_distrib_lattice : distrib_lattice α :=
{ le_sup_inf := λ a b c, by simp_rw [←sdiff_le_iff, le_inf_iff, sdiff_le_iff, ←le_inf_iff],
  ..‹coheyting_algebra α› }

@[simp] lemma hnot_sdiff (a : α) : ￢a \ a = ￢a := by rw [←top_sdiff', sdiff_sdiff, sup_idem]

lemma hnot_sdiff_comm (a b : α) : ￢a \ b = ￢b \ a := by simp_rw [←top_sdiff', sdiff_right_comm]

lemma hnot_le_iff_codisjoint_right : ￢a ≤ b ↔ codisjoint a b :=
by rw [←top_sdiff', sdiff_le_iff, codisjoint]

lemma hnot_le_iff_codisjoint_left : ￢a ≤ b ↔ codisjoint b a :=
hnot_le_iff_codisjoint_right.trans codisjoint.comm

lemma hnot_le_comm : ￢a ≤ b ↔ ￢b ≤ a :=
by rw [hnot_le_iff_codisjoint_right, hnot_le_iff_codisjoint_left]

alias hnot_le_iff_codisjoint_right ↔ _ codisjoint.hnot_le_right
alias hnot_le_iff_codisjoint_left ↔ _ codisjoint.hnot_le_left

lemma codisjoint_hnot_right (a : α) : codisjoint a (￢a) := sdiff_le_iff.1 (top_sdiff' _).le
lemma codisjoint_hnot_left (a : α) : codisjoint (￢a) a := (codisjoint_hnot_right _).symm

@[simp] lemma sup_hnot_self (a : α) : a ⊔ ￢a = ⊤ := (codisjoint_hnot_right _).eq_top
@[simp] lemma hnot_sup_self (a : α) : ￢a ⊔ a = ⊤ := (codisjoint_hnot_left _).eq_top

@[simp] lemma hnot_bot : ￢ (⊥ : α) = ⊤ :=
eq_of_forall_ge_iff $ λ a, by rw [hnot_le_iff_codisjoint_left, codisjoint_bot, top_le_iff]

@[simp] lemma hnot_top : ￢ (⊤ : α) = ⊥ := by rw [←top_sdiff', sdiff_self]

lemma hnot_hnot_le : ￢￢a ≤ a := (codisjoint_hnot_right _).hnot_le_left

lemma hnot_anti : antitone (hnot : α → α) := λ a b h, hnot_le_comm.1 $ hnot_hnot_le.trans h

@[simp] lemma hnot_hnot_hnot (a : α) : ￢￢￢a = ￢a := hnot_hnot_le.antisymm $ hnot_anti hnot_hnot_le

@[simp] lemma codisjoint_hnot_hnot_left_iff : codisjoint (￢￢a) b ↔ codisjoint a b :=
by simp_rw [←hnot_le_iff_codisjoint_right, hnot_hnot_hnot]

@[simp] lemma codisjoint_hnot_hnot_right_iff : codisjoint a (￢￢b) ↔ codisjoint a b :=
by simp_rw [←hnot_le_iff_codisjoint_left, hnot_hnot_hnot]

lemma le_hnot_inf_hnot : ￢ (a ⊔ b) ≤ ￢a ⊓ ￢b :=
le_inf (hnot_anti le_sup_left) $ hnot_anti le_sup_right

lemma hnot_hnot_sup_distrib (a b : α) : ￢￢(a ⊔ b) = ￢￢a ⊔ ￢￢b :=
begin
  refine ((hnot_inf_distrib _ _).ge.trans $ hnot_anti le_hnot_inf_hnot).antisymm' _,
  rw [hnot_le_iff_codisjoint_left, codisjoint_assoc, codisjoint_hnot_hnot_left_iff,
    codisjoint_left_comm, codisjoint_hnot_hnot_left_iff, ←codisjoint_assoc, sup_comm],
  exact codisjoint_hnot_right _,
end

lemma hnot_hnot_sdiff_distrib (a b : α) : ￢￢(a \ b) = ￢￢a \ ￢￢b :=
begin
  refine le_antisymm _ _,
  { refine hnot_le_comm.1 ((hnot_anti sdiff_le_inf_hnot).trans' _),
    rw [hnot_inf_distrib, hnot_le_iff_codisjoint_right, codisjoint_left_comm,
      ←hnot_le_iff_codisjoint_right],
    exact le_sdiff_sup },
  { rw [sdiff_le_iff, ←hnot_hnot_sup_distrib],
    exact hnot_anti (hnot_anti le_sup_sdiff) }
end

instance : heyting_algebra αᵒᵈ :=
{ compl := to_dual ∘ hnot ∘ of_dual,
  himp := λ a b, to_dual (of_dual b \ of_dual a),
  le_himp_iff := λ a b c, by { rw inf_comm, exact sdiff_le_iff },
  himp_bot := top_sdiff',
  ..order_dual.lattice α, ..order_dual.bounded_order α }

@[simp] lemma of_dual_compl (a : αᵒᵈ) : of_dual aᶜ = ￢of_dual a := rfl
@[simp] lemma of_dual_himp (a b : αᵒᵈ) : of_dual (a ⇨ b) = of_dual b \ of_dual a := rfl
@[simp] lemma to_dual_hnot (a : α) : to_dual ￢a = (to_dual a)ᶜ := rfl
@[simp] lemma to_dual_sdiff (a b : α) : to_dual (a \ b) = to_dual b ⇨ to_dual a := rfl

instance prod.coheyting_algebra [coheyting_algebra β] : coheyting_algebra (α × β) :=
{ sdiff_le_iff := λ a b c, and_congr sdiff_le_iff sdiff_le_iff,
  top_sdiff := λ a, prod.ext (top_sdiff' a.1) (top_sdiff' a.2),
  ..prod.lattice α β, ..prod.bounded_order α β, ..prod.has_sdiff, ..prod.has_hnot }

instance pi.coheyting_algebra {α : ι → Type*} [Π i, coheyting_algebra (α i)] :
  coheyting_algebra (Π i, α i) :=
by { pi_instance, exact λ a b c, forall_congr (λ i, sdiff_le_iff) }

end coheyting_algebra

section biheyting_algebra
variables [biheyting_algebra α] {a : α}

lemma compl_le_hnot : aᶜ ≤ ￢a := (disjoint_compl_left a).le_of_codisjoint $ codisjoint_hnot_right _

end biheyting_algebra

/-- Propositions form a Heyting algebra with implication as Heyting implication and negation as
complement. -/
instance Prop.heyting_algebra : heyting_algebra Prop :=
{ himp := (→),
  le_himp_iff := λ p q r, and_imp.symm,
  himp_bot := λ p, rfl,
  ..Prop.has_compl, ..Prop.distrib_lattice, ..Prop.bounded_order }

@[simp] lemma himp_iff_imp (p q : Prop) : p ⇨ q ↔ p → q := iff.rfl
@[simp] lemma compl_iff_not (p : Prop) : pᶜ ↔ ¬ p := iff.rfl

/-- A bounded linear order is a bi-Heyting algebra by setting
* `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = b` otherwise.
* `a \ b = ⊥` if `a ≤ b` and `a \ b = a` otherwise. -/
@[reducible] -- See note [reducible non instances]
def linear_order.to_biheyting_algebra [linear_order α] [bounded_order α] : biheyting_algebra α :=
{ himp := λ a b, if a ≤ b then ⊤ else b,
  compl := λ a, if a = ⊥ then ⊤ else ⊥,
  le_himp_iff := λ a b c, begin
    change _ ≤ ite _ _ _ ↔ _,
    split_ifs,
    { exact iff_of_true le_top (inf_le_of_right_le h) },
    { rw [inf_le_iff, or_iff_left h] }
  end,
  himp_bot := λ a, if_congr le_bot_iff rfl rfl,
  sdiff := λ a b, if a ≤ b then ⊥ else a,
  hnot := λ a, if a = ⊤ then ⊥ else ⊤,
  sdiff_le_iff := λ a b c, begin
    change ite _ _ _ ≤ _ ↔ _,
    split_ifs,
    { exact iff_of_true bot_le (le_sup_of_le_left h) },
    { rw [le_sup_iff, or_iff_right h] }
  end,
  top_sdiff := λ a, if_congr top_le_iff rfl rfl,
  ..linear_order.to_lattice, ..‹bounded_order α› }

namespace punit
variables (a b : punit.{u+1})

instance : biheyting_algebra punit :=
by refine_struct
{ top := star,
  bot := star,
  sup := λ _ _, star,
  inf := λ _ _, star,
  compl := λ _, star,
  sdiff := λ _ _, star,
  hnot := λ _, star,
  himp := λ _ _, star, ..punit.linear_order };
    intros; trivial <|> exact subsingleton.elim _ _

@[simp] lemma top_eq : (⊤ : punit) = star := rfl
@[simp] lemma bot_eq : (⊥ : punit) = star := rfl
@[simp] lemma sup_eq : a ⊔ b = star := rfl
@[simp] lemma inf_eq : a ⊓ b = star := rfl
@[simp] lemma compl_eq : aᶜ = star := rfl
@[simp] lemma sdiff_eq : a \ b = star := rfl
@[simp] lemma hnot_eq : ￢a = star := rfl
@[simp] lemma himp_eq : a ⇨ b = star := rfl

end punit
