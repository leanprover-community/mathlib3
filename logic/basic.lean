/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Theorems that require decidability hypotheses are in the namespace "decidable".
Classical versions are in the namespace "classical".

Note: in the presence of automation, this whole file may be unnecessary. On the other hand,
maybe it is useful for writing automation.
-/

/-
    miscellany

    TODO: move elsewhere
-/

section miscellany

variables {α : Type*} {β : Type*}

theorem eq_iff_le_and_le [partial_order α] {a b : α} : a = b ↔ (a ≤ b ∧ b ≤ a) :=
⟨assume eq, eq ▸ ⟨le_refl a, le_refl a⟩, assume ⟨ab, ba⟩, le_antisymm ab ba⟩

@[simp] theorem prod.mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} :
  (a₁, b₁) = (a₂, b₂) ↔ (a₁ = a₂ ∧ b₁ = b₂) :=
⟨prod.mk.inj, by cc⟩

@[simp] theorem prod.forall {p : α × β → Prop} :
  (∀ x, p x) ↔ (∀ a b, p (a, b)) :=
⟨assume h a b, h (a, b), assume h ⟨a, b⟩, h a b⟩

@[simp] theorem prod.exists {p : α × β → Prop} :
  (∃ x, p x) ↔ (∃ a b, p (a, b)) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

@[simp] theorem set_of_subset_set_of {p q : α → Prop} : {a | p a} ⊆ {a | q a} = (∀a, p a → q a) := rfl

@[simp] theorem sigma.mk.inj_iff {β : α → Type*} {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
⟨sigma.mk.inj, λ ⟨h₁, h₂⟩, by congr; assumption⟩

@[simp] theorem sigma.forall {β : α → Type*} {p : (Σ a, β a) → Prop} :
  (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem sigma.exists {β : α → Type*} {p : (Σ a, β a) → Prop} :
  (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

@[simp] theorem subtype.forall {β : α → Prop} {p : {a // β a} → Prop} :
  (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem subtype.exists {β : α → Prop} {p : {a // β a} → Prop} :
  (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

end miscellany

/-
    propositional connectives
-/

@[simp] theorem false_neq_true : false ≠ true :=
begin intro h, rw [h], trivial end

section propositional
variables {a b c d : Prop}

/- implies -/

@[simp] theorem imp_self : (a → a) ↔ true := iff_true_intro id

theorem imp_intro {α β} (h : α) (h₂ : β) : α := h

theorem imp_false : (a → false) ↔ ¬ a := iff.rfl

theorem imp_and_distrib {α} : (α → b ∧ c) ↔ (α → b) ∧ (α → c) :=
⟨λ h, ⟨λ ha, (h ha).left, λ ha, (h ha).right⟩,
 λ h ha, ⟨h.left ha, h.right ha⟩⟩

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
iff.intro (λ h ha hb, h ⟨ha, hb⟩) (λ h ⟨ha, hb⟩, h ha hb)

theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
iff_iff_implies_and_implies _ _

theorem iff_def' : (a ↔ b) ↔ (b → a) ∧ (a → b) :=
iff_def.trans and.comm

@[simp] theorem imp_true_iff {α : Sort*} : (α → true) ↔ true :=
iff_true_intro $ λ_, trivial

@[simp] theorem imp_iff_right (ha : a) : (a → b) ↔ b :=
⟨λf, f ha, imp_intro⟩

/- not -/

theorem not.elim {α : Sort*} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

@[reducible] theorem not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

theorem not_not_of_not_imp : ¬(a → b) → ¬¬a :=
mt not.elim

theorem not_of_not_imp {α} : ¬(α → b) → ¬b :=
mt imp_intro

theorem dec_em (p : Prop) [decidable p] : p ∨ ¬p := decidable.em p

theorem by_contradiction {p} [decidable p] : (¬p → false) → p :=
decidable.by_contradiction

@[simp] theorem not_not [decidable a] : ¬¬a ↔ a :=
iff.intro by_contradiction not_not_intro

theorem of_not_not [decidable a] : ¬¬a → a :=
by_contradiction

theorem of_not_imp [decidable a] (h : ¬ (a → b)) : a :=
by_contradiction (not_not_of_not_imp h)

theorem not.imp_symm [decidable a] (h : ¬a → b) (hb : ¬b) : a :=
by_contradiction $ hb ∘ h

theorem not_imp_comm [decidable a] [decidable b] : (¬a → b) ↔ (¬b → a) :=
⟨not.imp_symm, not.imp_symm⟩

theorem imp.swap : (a → b → c) ↔ (b → a → c) :=
⟨function.swap, function.swap⟩

theorem imp_not_comm : (a → ¬b) ↔ (b → ¬a) :=
imp.swap

/- and -/

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
mt and.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) :=
mt and.right

theorem and.imp_left (h : a → b) : a ∧ c → b ∧ c :=
and.imp h id

theorem and.imp_right (h : a → b) : c ∧ a → c ∧ b :=
and.imp id h

theorem and_not_self_iff (a : Prop) : a ∧ ¬ a ↔ false :=
iff.intro (assume h, (h.right) (h.left)) (assume h, h.elim)

theorem not_and_self_iff (a : Prop) : ¬ a ∧ a ↔ false :=
iff.intro (assume ⟨hna, ha⟩, hna ha) false.elim

theorem and_iff_left_of_imp {a b : Prop} (h : a → b) : (a ∧ b) ↔ a :=
iff.intro and.left (λ ha, ⟨ha, h ha⟩)

theorem and_iff_right_of_imp {a b : Prop} (h : b → a) : (a ∧ b) ↔ b :=
iff.intro and.right (λ hb, ⟨h hb, hb⟩)

/- or -/

theorem or_of_or_of_imp_of_imp (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d :=
or.imp h₂ h₃ h₁

theorem or_of_or_of_imp_left (h₁ : a ∨ c) (h : a → b) : b ∨ c :=
or.imp_left h h₁

theorem or_of_or_of_imp_right (h₁ : c ∨ a) (h : a → b) : c ∨ b :=
or.imp_right h h₁

theorem or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
or.elim h ha (assume h₂, or.elim h₂ hb hc)

theorem or_imp_distrib : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
⟨assume h, ⟨assume ha, h (or.inl ha), assume hb, h (or.inr hb)⟩,
  assume ⟨ha, hb⟩, or.rec ha hb⟩

theorem or_iff_not_imp_left [decidable a] : a ∨ b ↔ (¬ a → b) :=
⟨or.resolve_left, λ h, dite _ or.inl (or.inr ∘ h)⟩

theorem or_iff_not_imp_right [decidable b] : a ∨ b ↔ (¬ b → a) :=
or.comm.trans or_iff_not_imp_left

theorem not_imp_not [decidable a] : (¬ a → ¬ b) ↔ (b → a) :=
⟨assume h hb, by_contradiction $ assume na, h na hb, mt⟩

/- distributivity -/

theorem and_or_distrib_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
⟨λ ⟨ha, hbc⟩, hbc.imp (and.intro ha) (and.intro ha),
 or.rec (and.imp_right or.inl) (and.imp_right or.inr)⟩

theorem or_and_distrib_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
(and.comm.trans and_or_distrib_left).trans (or_congr and.comm and.comm)

theorem or_and_distrib_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
⟨or.rec (λha, and.intro (or.inl ha) (or.inl ha)) (and.imp or.inr or.inr),
 and.rec $ or.rec (imp_intro ∘ or.inl) (or.imp_right ∘ and.intro)⟩

theorem and_or_distrib_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
(or.comm.trans or_and_distrib_left).trans (and_congr or.comm or.comm)

/- iff -/

theorem iff_of_true (ha : a) (hb : b) : a ↔ b :=
⟨λ_, hb, λ _, ha⟩

theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b :=
⟨ha.elim, hb.elim⟩

theorem iff_true_left (ha : a) : (a ↔ b) ↔ b :=
⟨λ h, h.1 ha, iff_of_true ha⟩

theorem iff_true_right (ha : a) : (b ↔ a) ↔ b :=
iff.comm.trans (iff_true_left ha)

theorem iff_false_left (ha : ¬a) : (a ↔ b) ↔ ¬b :=
⟨λ h, mt h.2 ha, iff_of_false ha⟩

theorem iff_false_right (ha : ¬a) : (b ↔ a) ↔ ¬b :=
iff.comm.trans (iff_false_left ha)

theorem not_or_of_imp [decidable a] (h : a → b) : ¬ a ∨ b :=
if ha : a then or.inr (h ha) else or.inl ha

theorem imp_iff_not_or [decidable a] : (a → b) ↔ (¬ a ∨ b) :=
⟨not_or_of_imp, or.neg_resolve_left⟩

theorem not_imp_of_and_not (h : a ∧ ¬ b) : ¬ (a → b) :=
assume h₁, and.right h (h₁ (and.left h))

@[simp] theorem not_imp [decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
⟨λ h, ⟨of_not_imp h, not_of_not_imp h⟩, not_imp_of_and_not⟩

theorem peirce (a b : Prop) [decidable a] : ((a → b) → a) → a :=
if ha : a then λ h, ha else λ h, h (λ h', absurd h' ha)

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a := H _ id

theorem not_iff_not [decidable a] [decidable b] : (¬ a ↔ ¬ b) ↔ (a ↔ b) :=
by rw [@iff_def (¬ a), @iff_def' a]; exact and_congr not_imp_not not_imp_not

theorem not_iff_comm [decidable a] [decidable b] : (¬ a ↔ b) ↔ (¬ b ↔ a) :=
by rw [@iff_def (¬ a), @iff_def (¬ b)]; exact and_congr not_imp_comm imp_not_comm

theorem iff_not_comm [decidable a] [decidable b] : (a ↔ ¬ b) ↔ (b ↔ ¬ a) :=
by rw [@iff_def a, @iff_def b]; exact and_congr imp_not_comm not_imp_comm

@[simp] theorem not_and_not_right [decidable a] [decidable b] : ¬(a ∧ ¬b) ↔ (a → b) :=
not_iff_comm.1 not_imp

def decidable_of_iff (a : Prop) (h : a ↔ b) [D : decidable a] : decidable b :=
decidable_of_decidable_of_iff D h

def decidable_of_iff' (b : Prop) (h : a ↔ b) [D : decidable b] : decidable a :=
decidable_of_decidable_of_iff D h.symm

/- de morgan's laws -/

theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
λ ⟨ha, hb⟩, or.elim h (absurd ha) (absurd hb)

theorem not_and_distrib [decidable a] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
⟨λ h, if ha : a then or.inr (λ hb, h ⟨ha, hb⟩) else or.inl ha, not_and_of_not_or_not⟩

theorem not_and_distrib' [decidable b] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
⟨λ h, if hb : b then or.inl (λ ha, h ⟨ha, hb⟩) else or.inr hb, not_and_of_not_or_not⟩

@[simp] theorem not_and : ¬ (a ∧ b) ↔ (a → ¬ b) := and_imp

theorem not_and' : ¬ (a ∧ b) ↔ b → ¬a :=
not_and.trans imp_not_comm

theorem not_or_distrib : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
⟨λ h, ⟨λ ha, h (or.inl ha), λ hb, h (or.inr hb)⟩,
 λ ⟨h₁, h₂⟩ h, or.elim h h₁ h₂⟩

theorem or_iff_not_and_not [decidable a] [decidable b] : a ∨ b ↔ ¬ (¬a ∧ ¬b) :=
by rw [← not_or_distrib, not_not]

theorem and_iff_not_or_not [decidable a] [decidable b] : a ∧ b ↔ ¬ (¬ a ∨ ¬ b) :=
by rw [← not_and_distrib, not_not]

end propositional

/- equality -/

section equality
variables {α : Sort*} {a b : α}

@[simp] theorem heq_iff_eq : a == b ↔ a = b :=
⟨eq_of_heq, heq_of_eq⟩

end equality

/-
  quantifiers
-/

section quantifiers
variables {α : Sort*} {p q : α → Prop} {b : Prop}

theorem forall_swap {α β} {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y :=
⟨function.swap, function.swap⟩

theorem exists_swap {α β} {p : α → β → Prop} : (∃ x y, p x y) ↔ ∃ y x, p x y :=
⟨λ ⟨x, y, h⟩, ⟨y, x, h⟩, λ ⟨y, x, h⟩, ⟨x, y, h⟩⟩

theorem forall_of_forall (h : ∀ x, p x → q x) (h₁ : ∀ x, p x) : ∀ x, q x :=
assume x, h x (h₁ x)

theorem exists_of_exists (h : ∀ x, p x → q x) (h₁ : ∃ x, p x) : ∃ x, q x :=
match h₁ with ⟨x, hpx⟩ := ⟨x, h x hpx⟩ end

@[simp] theorem exists_imp_distrib : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
⟨λ h x hpx, h ⟨x, hpx⟩, λ h ⟨x, hpx⟩, h x hpx⟩

--theorem forall_not_of_not_exists (h : ¬ ∃ x, p x) : ∀ x, ¬ p x :=
--forall_imp_of_exists_imp h

theorem not_exists_of_forall_not (h : ∀ x, ¬ p x) : ¬ ∃ x, p x :=
exists_imp_distrib.2 h

@[simp] theorem not_exists : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
exists_imp_distrib

theorem not_forall_of_exists_not : (∃ x, ¬ p x) → ¬ ∀ x, p x
| ⟨x, hn⟩ h := hn (h x)

theorem not_forall {p : α → Prop}
    [decidable (∃ x, ¬ p x)] [∀ x, decidable (p x)] :
  (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
⟨not.imp_symm $ λ nx x, nx.imp_symm $ λ h, ⟨x, h⟩,
 not_forall_of_exists_not⟩

@[simp] theorem not_forall_not [decidable (∃ x, p x)] :
  (¬ ∀ x, ¬ p x) ↔ ∃ x, p x :=
by have := decidable_of_iff (¬ ∃ x, p x) not_exists;
   exact not_iff_comm.1 not_exists

@[simp] theorem not_exists_not [∀ x, decidable (p x)] :
  (¬ ∃ x, ¬ p x) ↔ ∀ x, p x :=
by simp

@[simp] theorem forall_true_iff : (α → true) ↔ true :=
iff_true_intro (λ _, trivial)

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
theorem forall_true_iff' (h : ∀ a, p a ↔ true) : (∀ a, p a) ↔ true :=
iff_true_intro (λ _, of_iff_true (h _))

@[simp] theorem forall_2_true_iff {β : α → Sort*} : (∀ a, β a → true) ↔ true :=
forall_true_iff' $ λ _, forall_true_iff

@[simp] theorem forall_3_true_iff {β : α → Sort*} {γ : Π a, β a → Sort*} :
  (∀ a (b : β a), γ a b → true) ↔ true :=
forall_true_iff' $ λ _, forall_2_true_iff

@[simp] theorem forall_const (α : Sort*) [inhabited α] : (α → b) ↔ b :=
⟨λ h, h (arbitrary α), λ hb x, hb⟩

@[simp] theorem exists_const (α : Sort*) [inhabited α] : (∃ x : α, b) ↔ b :=
⟨λ ⟨x, h⟩, h, λ h, ⟨arbitrary α, h⟩⟩

theorem forall_and_distrib : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
⟨λ h, ⟨λ x, (h x).left, λ x, (h x).right⟩, λ ⟨h₁, h₂⟩ x, ⟨h₁ x, h₂ x⟩⟩

theorem exists_or_distrib : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
⟨λ ⟨x, hpq⟩, hpq.elim (λ hpx, or.inl ⟨x, hpx⟩) (λ hqx, or.inr ⟨x, hqx⟩),
 λ hepq, hepq.elim (λ ⟨x, hpx⟩, ⟨x, or.inl hpx⟩) (λ ⟨x, hqx⟩, ⟨x, or.inr hqx⟩)⟩

@[simp] theorem exists_and_distrib_left {q : Prop} {p : α → Prop} :
  (∃x, q ∧ p x) ↔ q ∧ (∃x, p x) :=
⟨λ ⟨x, hq, hp⟩, ⟨hq, x, hp⟩, λ ⟨hq, x, hp⟩, ⟨x, hq, hp⟩⟩

@[simp] theorem exists_and_distrib_right {q : Prop} {p : α → Prop} :
  (∃x, p x ∧ q) ↔ (∃x, p x) ∧ q :=
by simp

@[simp] theorem forall_eq {a' : α} : (∀a, a = a' → p a) ↔ p a' :=
⟨λ h, h a' rfl, λ h a e, e.symm ▸ h⟩

@[simp] theorem exists_eq {a' : α} : (∃ a, a = a' ∧ p a) ↔ p a' :=
⟨λ ⟨a, e, h⟩, e ▸ h, λ h, ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right {a' : α} : (∃ a, p a ∧ a = a') ↔ p a' :=
(exists_congr $ by exact λ a, and.comm).trans exists_eq

@[simp] theorem forall_eq' {a' : α} : (∀a, a' = a → p a) ↔ p a' :=
by simp [@eq_comm _ a']

@[simp] theorem exists_eq' {a' : α} : (∃ a, a' = a ∧ p a) ↔ p a' :=
by simp [@eq_comm _ a']

@[simp] theorem exists_eq_right' {a' : α} : (∃ a, p a ∧ a' = a) ↔ p a' :=
by simp [@eq_comm _ a']

theorem forall_or_of_or_forall (h : b ∨ ∀x, p x) (x) : b ∨ p x :=
h.imp_right $ λ h₂, h₂ x

theorem forall_or_distrib_left {q : Prop} {p : α → Prop} [decidable q] :
  (∀x, q ∨ p x) ↔ q ∨ (∀x, p x) :=
⟨λ h, if hq : q then or.inl hq else or.inr $ λ x, (h x).resolve_left hq,
  forall_or_of_or_forall⟩

@[simp] theorem exists_prop {p q : Prop} : (∃ h : p, q) ↔ p ∧ q :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨h₁, h₂⟩⟩

@[simp] theorem exists_false : ¬ (∃a:α, false) := assume ⟨a, h⟩, h

end quantifiers

/- classical versions -/

namespace classical
variables {α : Sort*} {p : α → Prop}

local attribute [instance] prop_decidable

theorem not_forall : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := not_forall

theorem forall_or_distrib_left {q : Prop} {p : α → Prop} :
  (∀x, q ∨ p x) ↔ q ∨ (∀x, p x) :=
forall_or_distrib_left

theorem cases {p : Prop → Prop} (h1 : p true) (h2 : p false) : ∀a, p a :=
assume a, cases_on a h1 h2

theorem or_not {p : Prop} : p ∨ ¬ p :=
by_cases or.inl or.inr

/- use shortened names to avoid conflict when classical namespace is open -/
noncomputable theorem dec (p : Prop) : decidable p := by apply_instance
noncomputable theorem dec_pred (p : α → Prop) : decidable_pred p := by apply_instance
noncomputable theorem dec_rel (p : α → α → Prop) : decidable_rel p := by apply_instance
noncomputable theorem dec_eq (α : Sort*) : decidable_eq α := by apply_instance

end classical

/-
   bounded quantifiers
-/

section bounded_quantifiers
variables {α : Sort*} {r p q : α → Prop} {P Q : ∀ x, p x → Prop} {b : Prop}

theorem bex_def : (∃ x (h : p x), q x) ↔ ∃ x, p x ∧ q x :=
⟨λ ⟨x, px, qx⟩, ⟨x, px, qx⟩, λ ⟨x, px, qx⟩, ⟨x, px, qx⟩⟩

theorem bex.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
| ⟨a, h₁, h₂⟩ h' := h' a h₁ h₂

theorem bex.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ x (h : p x), P x h :=
⟨a, h₁, h₂⟩

theorem ball_congr (H : ∀ x h, P x h ↔ Q x h) :
  (∀ x h, P x h) ↔ (∀ x h, Q x h) :=
forall_congr $ λ x, forall_congr (H x)

theorem bex_congr (H : ∀ x h, P x h ↔ Q x h) :
  (∃ x h, P x h) ↔ (∃ x h, Q x h) :=
exists_congr $ λ x, exists_congr (H x)

theorem ball.imp_right (H : ∀ x h, (P x h → Q x h))
  (h₁ : ∀ x h, P x h) (x h) : Q x h :=
H _ _ $ h₁ _ _

theorem bex.imp_right (H : ∀ x h, (P x h → Q x h)) :
  (∃ x h, P x h) → ∃ x h, Q x h
| ⟨x, h, h'⟩ := ⟨_, _, H _ _ h'⟩

theorem ball.imp_left (H : ∀ x, p x → q x)
  (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
h₁ _ $ H _ h

theorem bex.imp_left (H : ∀ x, p x → q x) :
  (∃ x (_ : p x), r x) → ∃ x (_ : q x), r x
| ⟨x, hp, hr⟩ := ⟨x, H _ hp, hr⟩

theorem ball_of_forall (h : ∀ x, p x) (x) (_ : q x) : p x :=
h x

theorem forall_of_ball (H : ∀ x, p x) (h : ∀ x, p x → q x) (x) : q x :=
h x $ H x

theorem bex_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ x (_ : p x), q x
| ⟨x, hq⟩ := ⟨x, H x, hq⟩

theorem exists_of_bex : (∃ x (_ : p x), q x) → ∃ x, q x
| ⟨x, _, hq⟩ := ⟨x, hq⟩

@[simp] theorem bex_imp_distrib : ((∃ x h, P x h) → b) ↔ (∀ x h, P x h → b) :=
by simp

theorem not_bex : (¬ ∃ x h, P x h) ↔ ∀ x h, ¬ P x h :=
bex_imp_distrib

theorem not_ball_of_bex_not : (∃ x h, ¬ P x h) → ¬ ∀ x h, P x h
| ⟨x, h, hp⟩ al := hp $ al x h

theorem not_ball [decidable (∃ x h, ¬ P x h)] [∀ x h, decidable (P x h)] :
  (¬ ∀ x h, P x h) ↔ (∃ x h, ¬ P x h) :=
⟨not.imp_symm $ λ nx x h, nx.imp_symm $ λ h', ⟨x, h, h'⟩,
 not_ball_of_bex_not⟩

theorem ball_true_iff (p : α → Prop) : (∀ x, p x → true) ↔ true :=
iff_true_intro (λ h hrx, trivial)

theorem ball_and_distrib : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ (∀ x h, Q x h) :=
iff.trans (forall_congr $ λ x, forall_and_distrib) forall_and_distrib

theorem bex_or_distrib : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ (∃ x h, Q x h) :=
iff.trans (exists_congr $ λ x, exists_or_distrib) exists_or_distrib

end bounded_quantifiers

namespace classical
local attribute [instance] prop_decidable

theorem not_ball {α : Sort*} {p : α → Prop} {P : Π (x : α), p x → Prop} :
  (¬ ∀ x h, P x h) ↔ (∃ x h, ¬ P x h) := _root_.not_ball

end classical
