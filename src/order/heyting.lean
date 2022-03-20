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

@[reducible] -- See note [reducible non-instances]
def distrib_lattice.of_inf_sup_le [lattice α]
  (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)) : distrib_lattice α :=
{ ..‹lattice α›,
  ..@order_dual.distrib_lattice (order_dual α)
    { le_sup_inf := λ a b c, inf_sup_le _ _ _, ..order_dual.lattice _ } }

section disjoint
variables [semilattice_inf α] [order_bot α] {a b c : α}

lemma disjoint_left_comm : disjoint a (b ⊓ c) ↔ disjoint b (a ⊓ c) :=
by simp_rw [disjoint, inf_left_comm]

lemma disjoint_right_comm : disjoint (a ⊓ b) c ↔ disjoint (a ⊓ c) b :=
by simp_rw [disjoint, inf_right_comm]

end disjoint

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
prefix `￢ `:51 := hnot

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

lemma himp_def [Π i, has_himp (π i)] (a b : Π i, π i) : (a ⇨ b) = λ i, a i ⇨ b i := rfl
lemma hnot_def [Π i, has_hnot (π i)] (a : Π i, π i) : ￢ a = λ i, ￢ a i := rfl
lemma sdiff_def [Π i, has_sdiff (π i)] (a b : Π i, π i) : a \ b = λ i, a i \ b i := rfl
lemma compl_def [Π i, has_compl (π i)] (a : Π i, π i) : aᶜ = λ i, (a i)ᶜ := rfl

@[simp] lemma himp_apply [Π i, has_himp (π i)] (a b : Π i, π i) (i : ι) : (a ⇨ b) i = a i ⇨ b i :=
rfl
@[simp] lemma hnot_apply [Π i, has_hnot (π i)] (a : Π i, π i) (i : ι) : (￢ a) i = ￢ a i := rfl
@[simp] lemma sdiff_apply [Π i, has_sdiff (π i)] (a b : Π i, π i) (i : ι) : (a \ b) i = a i \ b i :=
rfl
@[simp] lemma compl_apply [Π i, has_compl (π i)] (a : Π i, π i) (i : ι) : aᶜ i = (a i)ᶜ := rfl

end pi

/-- A Heyting algebra is a lattice with an additional binary operation `⇨` called Heyting
implication such that `a ⇨` is right adjoint to `a ⊓`. -/
class heyting_algebra (α : Type*) extends lattice α, bounded_order α, has_himp α, has_compl α :=
(le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c)
(himp_bot (a : α) : a ⇨ ⊥ = aᶜ)

/-- A co-Heyting algebra is a lattice with an additional binary difference operation `\` such that
`\ a` is right adjoint to `⊔ a`. -/
class coheyting_algebra (α : Type*) extends lattice α, bounded_order α, has_hnot α, has_sdiff α :=
(sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c)
(top_sdiff (a : α) : ⊤ \ a = ￢a)

/-- A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra. -/
class biheyting_algebra (α : Type*) extends heyting_algebra α, has_sdiff α, has_hnot α :=
(sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c)
(top_sdiff (a : α) : ⊤ \ a = ￢a)

@[priority 100] -- See note [lower instance priority]
instance biheyting_algebra.to_coheyting_algebra [biheyting_algebra α] : coheyting_algebra α :=
{ ..‹biheyting_algebra α› }

/-- Constructs a Heyting algebra from the Heyting implication alone. -/
@[reducible] -- see note [reducible non instances]
def heyting_algebra.of_himp [distrib_lattice α] [bounded_order α] (himp : α → α → α)
  (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a ⊓ b ≤ c) : heyting_algebra α :=
{ himp := himp,
  compl := λ a, himp a ⊥,
  le_himp_iff := le_himp_iff,
  himp_bot := λ a, rfl }

/-- Constructs a Heyting algebra from the Heyting implication alone. -/
@[reducible] -- see note [reducible non instances]
def heyting_algebra.of_compl [distrib_lattice α] [bounded_order α] (compl : α → α)
  (le_himp_iff : ∀ a b c, a ≤ compl b ⊔ c ↔ a ⊓ b ≤ c) : heyting_algebra α :=
{ himp := λ a, (⊔) (compl a),
  compl := compl,
  le_himp_iff := le_himp_iff,
  himp_bot := λ a, sup_bot_eq,
  ..‹distrib_lattice α›, .. ‹bounded_order α› }

/-- Constructs a co-Heyting algebra from the difference alone. -/
@[reducible] -- see note [reducible non instances]
def coheyting_algebra.of_sdiff [distrib_lattice α] [bounded_order α] (sdiff : α → α → α)
  (sdiff_le_iff : ∀ a b c, sdiff a b ≤ c ↔ a ≤ b ⊔ c) : coheyting_algebra α :=
{ sdiff := sdiff,
  hnot := λ a, sdiff ⊤ a,
  sdiff_le_iff := sdiff_le_iff,
  top_sdiff := λ a, rfl }

/-- Constructs a co-Heyting algebra from the Heyting negation alone. -/
@[reducible] -- see note [reducible non instances]
def heyting_algebra.of_hnot [distrib_lattice α] [bounded_order α] (hnot : α → α)
  (sdiff_le_iff : ∀ a b c, a ⊓ hnot b ≤ c ↔ a ≤ b ⊔ c) : coheyting_algebra α :=
{ sdiff := λ a b, (a ⊓ hnot b),
  hnot := hnot,
  sdiff_le_iff := sdiff_le_iff,
  top_sdiff := λ a, top_inf_eq,
  ..‹distrib_lattice α›, .. ‹bounded_order α› }

section heyting_algebra
variables [heyting_algebra α] {a b c : α}

-- `p → q → r ↔ p ∧ q → r`
@[simp] lemma le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c := heyting_algebra.le_himp_iff _ _ _

-- lemma himp_sup_gc (a : α) : galois_connection ((⇨) a) (⊓ b) :=

-- `p → false ↔ ¬ p`
@[simp] lemma himp_bot (a : α) : a ⇨ ⊥ = aᶜ := heyting_algebra.himp_bot _

-- `p → q → r ↔ q → p → r`
lemma le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by rw [le_himp_iff, le_himp_iff, inf_comm]

-- `p → q → p`
lemma le_himp (a b : α) : a ≤ b ⇨ a := le_himp_iff.2 inf_le_left

-- `p → p → q ↔ p → q`
@[simp] lemma le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by rw [le_himp_iff, inf_idem]

-- `p → p`
@[simp] lemma himp_self (a : α) : a ⇨ a = ⊤ := top_le_iff.1 $ le_himp_iff.2 inf_le_right

-- `(p → q) ∧ p → q`
lemma himp_inf_le (a b : α) : (a ⇨ b) ⊓ a ≤ b := le_himp_iff.1 le_rfl

-- `p ∧ (p → q) → q`
lemma inf_himp_le (a b : α) : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm, ←le_himp_iff]

-- `p ∧ (p → q) ↔ p ∧ q`
@[simp] lemma inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
le_antisymm (le_inf inf_le_left $ by rw [inf_comm, ←le_himp_iff]) $ inf_le_inf le_rfl $ le_himp _ _

-- `(p → q) ∧ p ↔ q ∧ p`
@[simp] lemma himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]

-- example (p q r : Prop) : p → ¬ p ↔ ¬ p := by library_search

@[simp] lemma himp_eq_top : a ⇨ b = ⊤ ↔ a ≤ b := by rw [←top_le_iff, le_himp_iff, top_inf_eq]

-- `p → true`
@[simp] lemma himp_top (a : α) : a ⇨ ⊤ = ⊤ := himp_eq_top.2 le_top

-- `true → p ↔ p`
@[simp] lemma top_himp (a : α) : ⊤ ⇨ a = a :=
eq_of_forall_le_iff $ λ b, by rw [le_himp_iff, inf_top_eq]

-- `false → p`
@[simp] lemma bot_himp (a : α) : ⊥ ⇨ a = ⊤ := himp_eq_top.2 bot_le

-- `p → q → r ↔ p ∧ q → r`
lemma himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c :=
eq_of_forall_le_iff $ λ d, by simp_rw [le_himp_iff, inf_assoc]

-- `p → q → r ↔ p ∧ q → r`
@[simp] lemma himp_himp_le (a b c : α) : a ⇨ b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c :=
begin
  simp_rw le_himp_iff,
  -- rw ←inf_right_idem,
end

-- `p → q → r ↔ p ∧ q → r`
@[simp] lemma himp_himp_le (a b c : α) : a ⇨ b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c :=
begin

  simp_rw le_himp_iff,
end

-- `p → q → r ↔ q → p → r`
lemma himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by simp_rw [himp_himp, inf_comm]

lemma himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) :=
eq_of_forall_le_iff $ λ d, by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

lemma sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
eq_of_forall_le_iff $ λ d, by { rw [le_inf_iff, le_himp_comm, sup_le_iff], simp_rw le_himp_comm }

lemma himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b := le_himp_iff.2 $ (himp_inf_le _ _).trans h

lemma himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c :=
le_himp_iff.2 $ (inf_le_inf_left _ h).trans $ himp_inf_le _ _

lemma compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by simp_rw [←himp_bot, sup_himp_distrib]

lemma compl_le_himp (a b : α) : aᶜ ≤ a ⇨ b := (himp_bot _).ge.trans $ himp_le_himp_left bot_le

lemma compl_sup_le_himp (a b : α) : aᶜ ⊔ b ≤ a ⇨ b := sup_le (compl_le_himp _ _) $ le_himp _ _

instance heyting_algebra.to_distrib_lattice : distrib_lattice α :=
distrib_lattice.of_inf_sup_le $ λ a b c,
  by simp_rw [@inf_comm _ _ a, ←le_himp_iff, sup_le_iff, le_himp_iff, ←sup_le_iff]

-- `p → ¬ p ↔ ¬ p`
@[simp] lemma himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [←himp_bot, himp_himp, inf_idem]

-- `p → ¬ q ↔ ¬ q → p`
lemma himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by simp_rw [←himp_bot, himp_left_comm]

@[simp] lemma le_compl_iff : a ≤ bᶜ ↔ disjoint a b := by rw [←himp_bot, le_himp_iff, disjoint]
lemma le_compl_iff' : a ≤ bᶜ ↔ disjoint b a := le_compl_iff.trans disjoint.comm
lemma le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ := by simp_rw [le_compl_iff, disjoint.comm]

lemma disjoint_compl_right (a : α) : disjoint aᶜ a := le_himp_iff.1 (himp_bot _).ge
lemma disjoint_compl_left (a : α) : disjoint a aᶜ := (disjoint_compl_right _).symm

@[simp] lemma inf_compl_self (a : α) : a ⊓ aᶜ = ⊥ := (disjoint_compl_left _).eq_bot
@[simp] lemma compl_inf_self (a : α) : aᶜ ⊓ a = ⊥ := (disjoint_compl_right _).eq_bot

@[simp] lemma compl_top : (⊤ : α)ᶜ = ⊥ :=
eq_of_forall_le_iff $ λ a, by rw [le_compl_iff, disjoint_top, le_bot_iff]

@[simp] lemma compl_bot : (⊥ : α)ᶜ = ⊤ := by rw [←himp_bot, himp_self]

lemma le_compl_compl (a : α) : a ≤ aᶜᶜ := le_compl_iff.2 $ disjoint_compl_left _

lemma compl_anti : antitone (compl : α → α) := λ a b h, le_compl_comm.1 $ h.trans $ le_compl_compl _

@[simp] lemma compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
(compl_anti $ le_compl_compl _).antisymm $ le_compl_compl _

@[simp] lemma disjoint_compl_compl_left_iff : disjoint aᶜᶜ b ↔ disjoint a b :=
by simp_rw [←le_compl_iff', compl_compl_compl]

@[simp] lemma disjoint_compl_compl_right_iff : disjoint a bᶜᶜ ↔ disjoint a b :=
by simp_rw [←le_compl_iff, compl_compl_compl]

lemma compl_sup_compl_le (a b : α) :  aᶜ ⊔ bᶜ ≤ (a ⊓ b)ᶜ :=
sup_le (le_compl_iff.2 $ (disjoint_compl_right _).mono_right inf_le_left) $
  le_compl_iff.2 $ (disjoint_compl_right _).mono_right inf_le_right

lemma compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ :=
begin
  refine ((compl_anti $ compl_sup_compl_le _ _).trans (compl_sup_distrib _ _).le).antisymm _,
  rw [le_compl_iff, disjoint_assoc, disjoint_compl_compl_left_iff, disjoint_left_comm,
    disjoint_compl_compl_left_iff, ←disjoint_assoc, inf_comm],
  exact disjoint_compl_left _,
end

lemma compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ :=
begin
  refine le_antisymm _ _,
  { rw [le_himp_iff, ←compl_compl_inf_distrib],
    exact compl_anti (compl_anti $ himp_inf_le _ _) },
  { refine le_compl_comm.1 ((compl_anti $ compl_sup_le_himp _ _).trans _),
    rw [compl_sup_distrib, le_compl_iff, disjoint_right_comm, ←le_compl_iff],
    exact inf_himp_le _ _ }
end

instance : coheyting_algebra (order_dual α) :=
{ hnot := to_dual ∘ compl ∘ of_dual,
  sdiff := λ a b, to_dual (of_dual b ⇨ of_dual a),
  sdiff_le_iff := λ a b c, by { rw sup_comm, exact le_himp_iff },
  top_sdiff := himp_bot,
  ..order_dual.lattice α, ..order_dual.bounded_order α }

@[simp] lemma compl_of_dual (a : order_dual α) : (of_dual a)ᶜ = of_dual (￢ a) := rfl

@[simp] lemma hnot_to_dual (a : α) : ￢ to_dual a = to_dual (aᶜ) := rfl

instance prod.heyting_algebra [heyting_algebra β] : heyting_algebra (α × β) :=
{ le_himp_iff := λ a b c, and_congr le_himp_iff le_himp_iff,
  himp_bot := λ a, prod.ext (himp_bot a.1) (himp_bot a.2),
  ..prod.lattice α β, ..prod.bounded_order α β, ..prod.has_himp, ..prod.has_compl }

instance pi.heyting_algebra : heyting_algebra (ι → α) :=
by { pi_instance, exact λ a b c, forall_congr (λ i, le_himp_iff) }

end heyting_algebra

/-- Propositions form a Heyting algebra with implication as Heyting implication and negation as
complement. -/
instance : heyting_algebra Prop :=
{ himp := (→),
  compl := not,
  le_himp_iff := λ p q r, and_imp.symm,
  himp_bot := λ p, rfl,
  ..Prop.distrib_lattice }

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
