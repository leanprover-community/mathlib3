/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.option.basic
import logic.nontrivial
import order.lattice
import order.max
import tactic.pi_instances

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `has_<top/bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `order_<top/bot> α`: Order with a top/bottom element.
* `bounded_order α`: Order with a top and bottom element.
* `with_<top/bot> α`: Equips `option α` with the order on `α` plus `none` as the top/bottom element.
* `is_compl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non distributive lattice, an element can have several complements.
* `is_complemented α`: Typeclass stating that any element of a lattice has a complement.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[distrib_lattice α] [order_bot α]`
  It captures the properties of `disjoint` that are common to `generalized_boolean_algebra` and
  `distrib_lattice` when `order_bot`.
* Bounded and distributive lattice. Notated by `[distrib_lattice α] [bounded_order α]`.
  Typical examples include `Prop` and `set α`.

## Implementation notes

We didn't prove things about `[distrib_lattice α] [order_top α]` because the dual notion of
`disjoint` isn't really used anywhere.
-/

/-! ### Top, bottom element -/

set_option old_structure_cmd true

universes u v

variables {α : Type u} {β : Type v}

/-- Typeclass for the `⊤` (`\top`) notation -/
@[notation_class] class has_top (α : Type u) := (top : α)
/-- Typeclass for the `⊥` (`\bot`) notation -/
@[notation_class] class has_bot (α : Type u) := (bot : α)

notation `⊤` := has_top.top
notation `⊥` := has_bot.bot

@[priority 100] instance has_top_nonempty (α : Type u) [has_top α] : nonempty α := ⟨⊤⟩
@[priority 100] instance has_bot_nonempty (α : Type u) [has_bot α] : nonempty α := ⟨⊥⟩

attribute [pattern] has_bot.bot has_top.top

/-- An order is an `order_top` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest element constraint. -/
@[ancestor has_top]
class order_top (α : Type u) [has_le α] extends has_top α :=
(le_top : ∀ a : α, a ≤ ⊤)

section order_top
section has_le
variables [has_le α] [order_top α] {a : α}

@[simp] lemma le_top : a ≤ ⊤ := order_top.le_top a
@[simp] lemma is_top_top : is_top (⊤ : α) := λ _, le_top

end has_le

section preorder
variables [preorder α] [order_top α] {a b : α}

@[simp] lemma is_max_top : is_max (⊤ : α) := is_top_top.is_max
@[simp] lemma not_top_lt : ¬ ⊤ < a := is_max_top.not_lt

lemma ne_top_of_lt (h : a < b) : a ≠ ⊤ := (h.trans_le le_top).ne

alias ne_top_of_lt ← has_lt.lt.ne_top

end preorder

variables [partial_order α] [order_top α] [preorder β] {f : α → β} {a b : α}

@[simp] lemma is_max_iff_eq_top : is_max a ↔ a = ⊤ :=
⟨λ h, h.eq_of_le le_top, λ h b _, h.symm ▸ le_top⟩

@[simp] lemma is_top_iff_eq_top : is_top a ↔ a = ⊤ :=
⟨λ h, h.is_max.eq_of_le le_top, λ h b, h.symm ▸ le_top⟩

lemma not_is_max_iff_ne_top : ¬ is_max a ↔ a ≠ ⊤ := is_max_iff_eq_top.not
lemma not_is_top_iff_ne_top : ¬ is_top a ↔ a ≠ ⊤ := is_top_iff_eq_top.not

alias is_max_iff_eq_top ↔ is_max.eq_top _
alias is_top_iff_eq_top ↔ is_top.eq_top _

@[simp] lemma top_le_iff : ⊤ ≤ a ↔ a = ⊤ := le_top.le_iff_eq.trans eq_comm
lemma top_unique (h : ⊤ ≤ a) : a = ⊤ := le_top.antisymm h
lemma eq_top_iff : a = ⊤ ↔ ⊤ ≤ a := top_le_iff.symm
lemma eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ := top_unique $ h₂ ▸ h
lemma lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ := le_top.lt_iff_ne
@[simp] lemma not_lt_top_iff : ¬ a < ⊤ ↔ a = ⊤ := lt_top_iff_ne_top.not_left
lemma eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ := le_top.eq_or_lt
lemma ne.lt_top (h : a ≠ ⊤) : a < ⊤ := lt_top_iff_ne_top.mpr h
lemma ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ := h.symm.lt_top
lemma ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ := (hab.trans_lt hb.lt_top).ne

lemma strict_mono.apply_eq_top_iff (hf : strict_mono f) : f a = f ⊤ ↔ a = ⊤ :=
⟨λ h, not_lt_top_iff.1 $ λ ha, (hf ha).ne h, congr_arg _⟩

lemma strict_anti.apply_eq_top_iff (hf : strict_anti f) : f a = f ⊤ ↔ a = ⊤ :=
⟨λ h, not_lt_top_iff.1 $ λ ha, (hf ha).ne' h, congr_arg _⟩

variables [nontrivial α]

lemma not_is_min_top : ¬ is_min (⊤ : α) :=
λ h, let ⟨a, ha⟩ := exists_ne (⊤ : α) in ha $ top_le_iff.1 $ h le_top

end order_top

lemma strict_mono.maximal_preimage_top [linear_order α] [preorder β] [order_top β]
  {f : α → β} (H : strict_mono f) {a} (h_top : f a = ⊤) (x : α) :
  x ≤ a :=
H.maximal_of_maximal_image (λ p, by { rw h_top, exact le_top }) x

theorem order_top.ext_top {α} {hA : partial_order α} (A : order_top α)
  {hB : partial_order α} (B : order_top α)
  (H : ∀ x y : α, (by haveI := hA; exact x ≤ y) ↔ x ≤ y) :
  (by haveI := A; exact ⊤ : α) = ⊤ :=
top_unique $ by rw ← H; apply le_top

theorem order_top.ext {α} [partial_order α] {A B : order_top α} : A = B :=
begin
  have tt := order_top.ext_top A B (λ _ _, iff.rfl),
  casesI A with _ ha, casesI B with _ hb,
  congr,
  exact le_antisymm (hb _) (ha _)
end

/-- An order is an `order_bot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
@[ancestor has_bot]
class order_bot (α : Type u) [has_le α] extends has_bot α :=
(bot_le : ∀ a : α, ⊥ ≤ a)

section order_bot
section has_le
variables [has_le α] [order_bot α] {a : α}

@[simp] lemma bot_le : ⊥ ≤ a := order_bot.bot_le a
@[simp] lemma is_bot_bot : is_bot (⊥ : α) := λ _, bot_le

end has_le

section preorder
variables [preorder α] [order_bot α] {a b : α}

@[simp] lemma is_min_bot : is_min (⊥ : α) := is_bot_bot.is_min
@[simp] lemma not_lt_bot : ¬ a < ⊥ := is_min_bot.not_lt

lemma ne_bot_of_gt (h : a < b) : b ≠ ⊥ := (bot_le.trans_lt h).ne'

alias ne_bot_of_gt ← has_lt.lt.ne_bot

end preorder

variables [partial_order α] [order_bot α] [preorder β] {f : α → β} {a b : α}

@[simp] lemma is_min_iff_eq_bot : is_min a ↔ a = ⊥ :=
⟨λ h, h.eq_of_ge bot_le, λ h b _, h.symm ▸ bot_le⟩

@[simp] lemma is_bot_iff_eq_bot : is_bot a ↔ a = ⊥ :=
⟨λ h, h.is_min.eq_of_ge bot_le, λ h b, h.symm ▸ bot_le⟩

lemma not_is_min_iff_ne_bot : ¬ is_min a ↔ a ≠ ⊥ := is_min_iff_eq_bot.not
lemma not_is_bot_iff_ne_bot : ¬ is_bot a ↔ a ≠ ⊥ := is_bot_iff_eq_bot.not

alias is_min_iff_eq_bot ↔ is_min.eq_bot _
alias is_bot_iff_eq_bot ↔ is_bot.eq_bot _

@[simp] lemma le_bot_iff : a ≤ ⊥ ↔ a = ⊥ := bot_le.le_iff_eq
lemma bot_unique (h : a ≤ ⊥) : a = ⊥ := h.antisymm bot_le
lemma eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ := le_bot_iff.symm
lemma eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ := bot_unique $ h₂ ▸ h
lemma bot_lt_iff_ne_bot : ⊥ < a ↔ a ≠ ⊥ := bot_le.lt_iff_ne.trans ne_comm
@[simp] lemma not_bot_lt_iff : ¬ ⊥ < a ↔ a = ⊥ := bot_lt_iff_ne_bot.not_left
lemma eq_bot_or_bot_lt (a : α) : a = ⊥ ∨ ⊥ < a := bot_le.eq_or_gt
lemma eq_bot_of_minimal (h : ∀ b, ¬ b < a) : a = ⊥ := (eq_bot_or_bot_lt a).resolve_right (h ⊥)
lemma ne.bot_lt (h : a ≠ ⊥) : ⊥ < a := bot_lt_iff_ne_bot.mpr h
lemma ne.bot_lt' (h : ⊥ ≠ a) : ⊥ < a := h.symm.bot_lt
lemma ne_bot_of_le_ne_bot (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ := (hb.bot_lt.trans_le hab).ne'

lemma strict_mono.apply_eq_bot_iff (hf : strict_mono f) : f a = f ⊥ ↔ a = ⊥ :=
⟨λ h, not_bot_lt_iff.1 $ λ ha, (hf ha).ne' h, congr_arg _⟩

lemma strict_anti.apply_eq_bot_iff (hf : strict_anti f) : f a = f ⊥ ↔ a = ⊥ :=
⟨λ h, not_bot_lt_iff.1 $ λ ha, (hf ha).ne h, congr_arg _⟩

variables [nontrivial α]

lemma not_is_max_bot : ¬ is_max (⊥ : α) :=
λ h, let ⟨a, ha⟩ := exists_ne (⊥ : α) in ha $ le_bot_iff.1 $ h bot_le

end order_bot

lemma strict_mono.minimal_preimage_bot [linear_order α] [partial_order β] [order_bot β]
  {f : α → β} (H : strict_mono f) {a} (h_bot : f a = ⊥) (x : α) :
  a ≤ x :=
H.minimal_of_minimal_image (λ p, by { rw h_bot, exact bot_le }) x

theorem order_bot.ext_bot {α} {hA : partial_order α} (A : order_bot α)
  {hB : partial_order α} (B : order_bot α)
  (H : ∀ x y : α, (by haveI := hA; exact x ≤ y) ↔ x ≤ y) :
  (by haveI := A; exact ⊥ : α) = ⊥ :=
bot_unique $ by rw ← H; apply bot_le

theorem order_bot.ext {α} [partial_order α] {A B : order_bot α} : A = B :=
begin
  have tt := order_bot.ext_bot A B (λ _ _, iff.rfl),
  casesI A with a ha, casesI B with b hb,
  congr,
  exact le_antisymm (ha _) (hb _)
end

section semilattice_sup_top
variables [semilattice_sup α] [order_top α] {a : α}

@[simp] theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
sup_of_le_left le_top

@[simp] theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
sup_of_le_right le_top

end semilattice_sup_top

section semilattice_sup_bot
variables [semilattice_sup α] [order_bot α] {a b : α}

@[simp] theorem bot_sup_eq : ⊥ ⊔ a = a :=
sup_of_le_right bot_le

@[simp] theorem sup_bot_eq : a ⊔ ⊥ = a :=
sup_of_le_left bot_le

@[simp] theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ (a = ⊥ ∧ b = ⊥) :=
by rw [eq_bot_iff, sup_le_iff]; simp

end semilattice_sup_bot

section semilattice_inf_top
variables [semilattice_inf α] [order_top α] {a b : α}

@[simp] theorem top_inf_eq : ⊤ ⊓ a = a :=
inf_of_le_right le_top

@[simp] theorem inf_top_eq : a ⊓ ⊤ = a :=
inf_of_le_left le_top

@[simp] theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ (a = ⊤ ∧ b = ⊤) :=
by rw [eq_top_iff, le_inf_iff]; simp

end semilattice_inf_top

section semilattice_inf_bot
variables [semilattice_inf α] [order_bot α] {a : α}

@[simp] theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
inf_of_le_left bot_le

@[simp] theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
inf_of_le_right bot_le

end semilattice_inf_bot

/-! ### Bounded order -/

/-- A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively. -/
@[ancestor order_top order_bot]
class bounded_order (α : Type u) [has_le α] extends order_top α, order_bot α.

theorem bounded_order.ext {α} [partial_order α] {A B : bounded_order α} : A = B :=
begin
  have ht : @bounded_order.to_order_top α _ A = @bounded_order.to_order_top α _ B := order_top.ext,
  have hb : @bounded_order.to_order_bot α _ A = @bounded_order.to_order_bot α _ B := order_bot.ext,
  casesI A,
  casesI B,
  injection ht with h,
  injection hb with h',
  convert rfl,
  { exact h.symm },
  { exact h'.symm }
end

/-- Propositions form a distributive lattice. -/
instance Prop.distrib_lattice : distrib_lattice Prop :=
{ le           := λ a b, a → b,
  le_refl      := λ _, id,
  le_trans     := λ a b c f g, g ∘ f,
  le_antisymm  := λ a b Hab Hba, propext ⟨Hab, Hba⟩,

  sup          := or,
  le_sup_left  := @or.inl,
  le_sup_right := @or.inr,
  sup_le       := λ a b c, or.rec,

  inf          := and,
  inf_le_left  := @and.left,
  inf_le_right := @and.right,
  le_inf       := λ a b c Hab Hac Ha, and.intro (Hab Ha) (Hac Ha),
  le_sup_inf   := λ a b c H, or_iff_not_imp_left.2 $
    λ Ha, ⟨H.1.resolve_left Ha, H.2.resolve_left Ha⟩ }

/-- Propositions form a bounded order. -/
instance Prop.bounded_order : bounded_order Prop :=
{ top          := true,
  le_top       := λ a Ha, true.intro,
  bot          := false,
  bot_le       := @false.elim }

instance Prop.le_is_total : is_total Prop (≤) :=
⟨λ p q, by { change (p → q) ∨ (q → p), tauto! }⟩

noncomputable instance Prop.linear_order : linear_order Prop :=
by classical; exact lattice.to_linear_order Prop

@[simp] lemma le_Prop_eq : ((≤) : Prop → Prop → Prop) = (→) := rfl
@[simp] lemma sup_Prop_eq : (⊔) = (∨) := rfl
@[simp] lemma inf_Prop_eq : (⊓) = (∧) := rfl

section logic
/-!
#### In this section we prove some properties about monotone and antitone operations on `Prop`
-/
section preorder

variable [preorder α]

theorem monotone_and {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λ x, p x ∧ q x) :=
λ a b h, and.imp (m_p h) (m_q h)
-- Note: by finish [monotone] doesn't work

theorem monotone_or {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λ x, p x ∨ q x) :=
λ a b h, or.imp (m_p h) (m_q h)

lemma monotone_le {x : α}: monotone ((≤) x) :=
λ y z h' h, h.trans h'

lemma monotone_lt {x : α}: monotone ((<) x) :=
λ y z h' h, h.trans_le h'

lemma antitone_le {x : α}: antitone (≤ x) :=
λ y z h' h, h'.trans h

lemma antitone_lt {x : α}: antitone (< x) :=
λ y z h' h, h'.trans_lt h

lemma monotone.forall {P : β → α → Prop} (hP : ∀ x, monotone (P x)) :
  monotone (λ y, ∀ x, P x y) :=
λ y y' hy h x, hP x hy $ h x

lemma antitone.forall {P : β → α → Prop} (hP : ∀ x, antitone (P x)) :
  antitone (λ y, ∀ x, P x y) :=
λ y y' hy h x, hP x hy (h x)

lemma monotone.ball {P : β → α → Prop} {s : set β} (hP : ∀ x ∈ s, monotone (P x)) :
  monotone (λ y, ∀ x ∈ s, P x y) :=
λ y y' hy h x hx, hP x hx hy (h x hx)

lemma antitone.ball {P : β → α → Prop} {s : set β} (hP : ∀ x ∈ s, antitone (P x)) :
  antitone (λ y, ∀ x ∈ s, P x y) :=
λ y y' hy h x hx, hP x hx hy (h x hx)

end preorder

section semilattice_sup
variables [semilattice_sup α]

lemma exists_ge_and_iff_exists {P : α → Prop} {x₀ : α} (hP : monotone P) :
  (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
⟨λ h, h.imp $ λ x h, h.2, λ ⟨x, hx⟩, ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α]

lemma exists_le_and_iff_exists {P : α → Prop} {x₀ : α} (hP : antitone P) :
  (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
exists_ge_and_iff_exists hP.dual_left

end semilattice_inf
end logic

/-! ### Function lattices -/

namespace pi
variables {ι : Type*} {α' : ι → Type*}

instance [Π i, has_bot (α' i)] : has_bot (Π i, α' i) := ⟨λ i, ⊥⟩

@[simp] lemma bot_apply [Π i, has_bot (α' i)] (i : ι) : (⊥ : Π i, α' i) i = ⊥ := rfl

lemma bot_def [Π i, has_bot (α' i)] : (⊥ : Π i, α' i) = λ i, ⊥ := rfl

instance [Π i, has_top (α' i)] : has_top (Π i, α' i) := ⟨λ i, ⊤⟩

@[simp] lemma top_apply [Π i, has_top (α' i)] (i : ι) : (⊤ : Π i, α' i) i = ⊤ := rfl

lemma top_def [Π i, has_top (α' i)] : (⊤ : Π i, α' i) = λ i, ⊤ := rfl

instance [Π i, has_le (α' i)] [Π i, order_top (α' i)] : order_top (Π i, α' i) :=
{ le_top := λ _ _, le_top, ..pi.has_top }

instance [Π i, has_le (α' i)] [Π i, order_bot (α' i)] : order_bot (Π i, α' i) :=
{ bot_le := λ _ _, bot_le, ..pi.has_bot }

instance [Π i, has_le (α' i)] [Π i, bounded_order (α' i)] :
  bounded_order (Π i, α' i) :=
{ ..pi.order_top, ..pi.order_bot }

end pi

section subsingleton

variables [partial_order α] [bounded_order α]

lemma eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) :
  x = (⊥ : α) :=
eq_bot_mono le_top (eq.symm hα)

lemma eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) :
  x = (⊤ : α) :=
eq_top_mono bot_le hα

lemma subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) :
  subsingleton α :=
⟨λ a b, le_antisymm (le_trans le_top $ le_trans h bot_le) (le_trans le_top $ le_trans h bot_le)⟩

lemma subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) :
  subsingleton α :=
subsingleton_of_top_le_bot (ge_of_eq hα)

lemma subsingleton_iff_bot_eq_top :
  (⊥ : α) = (⊤ : α) ↔ subsingleton α :=
⟨subsingleton_of_bot_eq_top, λ h, by exactI subsingleton.elim ⊥ ⊤⟩

end subsingleton

section lift

/-- Pullback an `order_top`. -/
@[reducible] -- See note [reducible non-instances]
def order_top.lift [has_le α] [has_top α] [has_le β] [order_top β] (f : α → β)
  (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) :
  order_top α :=
⟨⊤, λ a, map_le _ _ $ by { rw map_top, exact le_top }⟩

/-- Pullback an `order_bot`. -/
@[reducible] -- See note [reducible non-instances]
def order_bot.lift [has_le α] [has_bot α] [has_le β] [order_bot β] (f : α → β)
  (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_bot : f ⊥ = ⊥) :
  order_bot α :=
⟨⊥, λ a, map_le _ _ $ by { rw map_bot, exact bot_le }⟩

/-- Pullback a `bounded_order`. -/
@[reducible] -- See note [reducible non-instances]
def bounded_order.lift [has_le α] [has_top α] [has_bot α] [has_le β] [bounded_order β] (f : α → β)
  (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
  bounded_order α :=
{ ..order_top.lift f map_le map_top, ..order_bot.lift f map_le map_bot }

end lift

/-! ### `with_bot`, `with_top` -/

/-- Attach `⊥` to a type. -/
def with_bot (α : Type*) := option α

namespace with_bot
variables {a b : α}

meta instance [has_to_format α] : has_to_format (with_bot α) :=
{ to_format := λ x,
  match x with
  | none := "⊥"
  | (some x) := to_fmt x
  end }

instance [has_repr α] : has_repr (with_bot α) :=
⟨λ o, match o with | none := "⊥" | (some a) := "↑" ++ repr a end⟩

instance : has_coe_t α (with_bot α) := ⟨some⟩
instance : has_bot (with_bot α) := ⟨none⟩

instance : inhabited (with_bot α) := ⟨⊥⟩

lemma none_eq_bot : (none : with_bot α) = (⊥ : with_bot α) := rfl
lemma some_eq_coe (a : α) : (some a : with_bot α) = (↑a : with_bot α) := rfl

@[simp] lemma bot_ne_coe : ⊥ ≠ (a : with_bot α) .
@[simp] lemma coe_ne_bot : (a : with_bot α) ≠ ⊥ .

/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_eliminator]
def rec_bot_coe {C : with_bot α → Sort*} (h₁ : C ⊥) (h₂ : Π (a : α), C a) :
  Π (n : with_bot α), C n :=
option.rec h₁ h₂

@[norm_cast] lemma coe_eq_coe : (a : with_bot α) = b ↔ a = b := option.some_inj

-- the `by exact` here forces the type of the equality to be `@eq (with_bot α)`
@[simp] lemma map_bot (f : α → β) :
  (by exact option.map f (⊥ : with_bot α)) = (⊥ : with_bot β) := rfl
lemma map_coe (f : α → β) (a : α) :
  (by exact option.map f (a : with_bot α)) = (f a : with_bot β) := rfl

lemma ne_bot_iff_exists {x : with_bot α} : x ≠ ⊥ ↔ ∃ (a : α), ↑a = x := option.ne_none_iff_exists

/-- Deconstruct a `x : with_bot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : Π (x : with_bot α), x ≠ ⊥ → α
| ⊥        h := absurd rfl h
| (some x) h := x

@[simp] lemma coe_unbot (x : with_bot α) (h : x ≠ ⊥) : (x.unbot h : with_bot α) = x :=
by { cases x, simpa using h, refl, }

@[simp] lemma unbot_coe (x : α) (h : (x : with_bot α) ≠ ⊥ := coe_ne_bot) :
  (x : with_bot α).unbot h = x := rfl

instance : can_lift (with_bot α) α :=
{ coe := coe,
  cond := λ r, r ≠ ⊥,
  prf := λ x h, ⟨x.unbot h, coe_unbot _ _⟩ }

section has_le
variables [has_le α]

@[priority 10]
instance : has_le (with_bot α) := ⟨λ o₁ o₂ : option α, ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b⟩

@[simp] lemma some_le_some : @has_le.le (with_bot α) _ (some a) (some b) ↔ a ≤ b := by simp [(≤)]
@[simp, norm_cast] lemma coe_le_coe : (a : with_bot α) ≤ b ↔ a ≤ b := some_le_some

@[simp] lemma none_le {a : with_bot α} : @has_le.le (with_bot α) _ none a :=
λ b h, option.no_confusion h

instance : order_bot (with_bot α) := { bot_le := λ a, none_le, ..with_bot.has_bot }

instance [order_top α] : order_top (with_bot α) :=
{ top := some ⊤,
  le_top := λ o a ha, by cases ha; exact ⟨_, rfl, le_top⟩ }

instance [order_top α] : bounded_order (with_bot α) :=
{ ..with_bot.order_top, ..with_bot.order_bot }

lemma not_coe_le_bot (a : α) : ¬ (a : with_bot α) ≤ ⊥ :=
λ h, let ⟨b, hb, _⟩ := h _ rfl in option.not_mem_none _ hb

lemma coe_le : ∀ {o : option α}, b ∈ o → ((a : with_bot α) ≤ o ↔ a ≤ b) | _ rfl := coe_le_coe

lemma coe_le_iff : ∀ {x : with_bot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
| (some a) := by simp [some_eq_coe, coe_eq_coe]
| none     := iff_of_false (not_coe_le_bot _) $ by simp [none_eq_bot]

lemma le_coe_iff : ∀ {x : with_bot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
| (some b) := by simp [some_eq_coe, coe_eq_coe]
| none     := by simp [none_eq_bot]

protected lemma _root_.is_max.with_bot (h : is_max a) : is_max (a : with_bot α)
| none _ := bot_le
| (some b) hb := some_le_some.2 $ h $ some_le_some.1 hb

end has_le

section has_lt
variables [has_lt α]

@[priority 10]
instance : has_lt (with_bot α) := ⟨λ o₁ o₂ : option α, ∃ b ∈ o₂, ∀ a ∈ o₁, a < b⟩

@[simp] lemma some_lt_some : @has_lt.lt (with_bot α) _ (some a) (some b) ↔ a < b := by simp [(<)]
@[simp, norm_cast] lemma coe_lt_coe : (a : with_bot α) < b ↔ a < b := some_lt_some

@[simp] lemma none_lt_some (a : α) : @has_lt.lt (with_bot α) _ none (some a) :=
⟨a, rfl, λ b hb, (option.not_mem_none _ hb).elim⟩
lemma bot_lt_coe (a : α) : (⊥ : with_bot α) < a := none_lt_some a

@[simp] lemma not_lt_none (a : with_bot α) : ¬ @has_lt.lt (with_bot α) _ a none :=
λ ⟨_, h, _⟩, option.not_mem_none _ h

lemma lt_iff_exists_coe : ∀ {a b : with_bot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
| a (some b) := by simp [some_eq_coe, coe_eq_coe]
| a none     := iff_of_false (not_lt_none _) $ by simp [none_eq_bot]

lemma lt_coe_iff : ∀ {x : with_bot α}, x < b ↔ ∀ a, x = ↑a → a < b
| (some b) := by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
| none     := by simp [none_eq_bot, bot_lt_coe]

end has_lt

instance [preorder α] : preorder (with_bot α) :=
{ le          := (≤),
  lt          := (<),
  lt_iff_le_not_le := by { intros, cases a; cases b; simp [lt_iff_le_not_le]; simp [(<), (≤)] },
  le_refl     := λ o a ha, ⟨a, ha, le_rfl⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ a ha,
    let ⟨b, hb, ab⟩ := h₁ a ha, ⟨c, hc, bc⟩ := h₂ b hb in
    ⟨c, hc, le_trans ab bc⟩ }

instance [partial_order α] : partial_order (with_bot α) :=
{ le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₁ with a,
    { cases o₂ with b, {refl},
      rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩,
      rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end,
  .. with_bot.preorder }

lemma le_coe_get_or_else [preorder α] : ∀ (a : with_bot α) (b : α), a ≤ a.get_or_else b
| (some a) b := le_refl a
| none     b := λ _ h, option.no_confusion h

@[simp] lemma get_or_else_bot (a : α) : option.get_or_else (⊥ : with_bot α) a = a := rfl

lemma get_or_else_bot_le_iff [has_le α] [order_bot α] {a : with_bot α} {b : α} :
  a.get_or_else ⊥ ≤ b ↔ a ≤ b :=
by cases a; simp [none_eq_bot, some_eq_coe]

lemma get_or_else_bot_lt_iff [partial_order α] [order_bot α] {a : with_bot α} {b : α}
  (ha : a ≠ ⊥) :
  a.get_or_else ⊥ < b ↔ a < b :=
begin
  obtain ⟨a, rfl⟩ := ne_bot_iff_exists.mp ha,
  simp only [lt_iff_le_and_ne, get_or_else_bot_le_iff, and.congr_right_iff],
  intro h,
  apply iff.not,
  simp only [with_bot.coe_eq_coe, option.get_or_else_coe, iff_self],
end

instance [semilattice_sup α] : semilattice_sup (with_bot α) :=
{ sup          := option.lift_or_get (⊔),
  le_sup_left  := λ o₁ o₂ a ha,
    by cases ha; cases o₂; simp [option.lift_or_get],
  le_sup_right := λ o₁ o₂ a ha,
    by cases ha; cases o₁; simp [option.lift_or_get],
  sup_le       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases o₁ with b; cases o₂ with c; cases ha,
    { exact h₂ a rfl },
    { exact h₁ a rfl },
    { rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩,
      simp at h₂,
      exact ⟨d, rfl, sup_le h₁' h₂⟩ }
  end,
  ..with_bot.order_bot,
  ..with_bot.partial_order }

lemma coe_sup [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_bot α) = a ⊔ b := rfl

instance [semilattice_inf α] : semilattice_inf (with_bot α) :=
{ inf          := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a ⊓ b)),
  inf_le_left  := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, inf_le_left⟩
  end,
  inf_le_right := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, inf_le_right⟩
  end,
  le_inf       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, le_inf ab ac⟩
  end,
  ..with_bot.order_bot,
  ..with_bot.partial_order }

lemma coe_inf [semilattice_inf α] (a b : α) : ((a ⊓ b : α) : with_bot α) = a ⊓ b := rfl

instance [lattice α] : lattice (with_bot α) :=
{ ..with_bot.semilattice_sup, ..with_bot.semilattice_inf }

instance decidable_le [has_le α] [@decidable_rel α (≤)] : @decidable_rel (with_bot α) (≤)
| none x := is_true $ λ a h, option.no_confusion h
| (some x) (some y) :=
  if h : x ≤ y
  then is_true (some_le_some.2 h)
  else is_false $ by simp *
| (some x) none := is_false $ λ h, by rcases h x rfl with ⟨y, ⟨_⟩, _⟩

instance decidable_lt [has_lt α] [@decidable_rel α (<)] : @decidable_rel (with_bot α) (<)
| none (some x) := is_true $ by existsi [x,rfl]; rintros _ ⟨⟩
| (some x) (some y) :=
  if h : x < y
  then is_true $ by simp *
  else is_false $ by simp *
| x none := is_false $ by rintro ⟨a,⟨⟨⟩⟩⟩

instance is_total_le [has_le α] [is_total α (≤)] : is_total (with_bot α) (≤) :=
⟨λ a b, match a, b with
  | none  , _      := or.inl bot_le
  | _     , none   := or.inr bot_le
  | some x, some y := (total_of (≤) x y).imp some_le_some.2 some_le_some.2
  end⟩

instance [linear_order α] : linear_order (with_bot α) := lattice.to_linear_order _

@[norm_cast] -- this is not marked simp because the corresponding with_top lemmas are used
lemma coe_min [linear_order α] (x y : α) : ((min x y : α) : with_bot α) = min x y := rfl

@[norm_cast] -- this is not marked simp because the corresponding with_top lemmas are used
lemma coe_max [linear_order α] (x y : α) : ((max x y : α) : with_bot α) = max x y := rfl

lemma well_founded_lt [preorder α] (h : @well_founded α (<)) : @well_founded (with_bot α) (<) :=
have acc_bot : acc ((<) : with_bot α → with_bot α → Prop) ⊥ :=
  acc.intro _ (λ a ha, (not_le_of_gt ha bot_le).elim),
⟨λ a, option.rec_on a acc_bot (λ a, acc.intro _ (λ b, option.rec_on b (λ _, acc_bot)
(λ b, well_founded.induction h b
  (show ∀ b : α, (∀ c, c < b → (c : with_bot α) < a →
      acc ((<) : with_bot α → with_bot α → Prop) c) → (b : with_bot α) < a →
        acc ((<) : with_bot α → with_bot α → Prop) b,
  from λ b ih hba, acc.intro _ (λ c, option.rec_on c (λ _, acc_bot)
    (λ c hc, ih _ (some_lt_some.1 hc) (lt_trans hc hba)))))))⟩

instance [has_lt α] [densely_ordered α] [no_min_order α] : densely_ordered (with_bot α) :=
⟨ λ a b,
  match a, b with
  | a,      none   := λ h : a < ⊥, (not_lt_none _ h).elim
  | none,   some b := λ h, let ⟨a, ha⟩ := exists_lt b in ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
  | some a, some b := λ h, let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h) in
    ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩
  end⟩

lemma lt_iff_exists_coe_btwn [preorder α] [densely_ordered α] [no_min_order α] {a b : with_bot α} :
  a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
⟨λ h, let ⟨y, hy⟩ := exists_between h, ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1 in ⟨x, hx.1 ▸ hy⟩,
 λ ⟨x, hx⟩, lt_trans hx.1 hx.2⟩

instance [has_le α] [no_top_order α] [nonempty α] : no_top_order (with_bot α) :=
⟨begin
  apply rec_bot_coe,
  { exact ‹nonempty α›.elim (λ a, ⟨a, not_coe_le_bot a⟩) },
  { intro a,
    obtain ⟨b, h⟩ := exists_not_le a,
    exact ⟨b, by rwa coe_le_coe⟩ }
end⟩

instance [has_lt α] [no_max_order α] [nonempty α] : no_max_order (with_bot α) :=
⟨begin
  apply with_bot.rec_bot_coe,
  { apply ‹nonempty α›.elim,
    exact λ a, ⟨a, with_bot.bot_lt_coe a⟩, },
  { intro a,
    obtain ⟨b, ha⟩ := exists_gt a,
    exact ⟨b, with_bot.coe_lt_coe.mpr ha⟩, }
end⟩

end with_bot

--TODO(Mario): Construct using order dual on with_bot
/-- Attach `⊤` to a type. -/
def with_top (α : Type*) := option α

namespace with_top
variables {a b : α}

meta instance [has_to_format α] : has_to_format (with_top α) :=
{ to_format := λ x,
  match x with
  | none := "⊤"
  | (some x) := to_fmt x
  end }

instance [has_repr α] : has_repr (with_top α) :=
⟨λ o, match o with | none := "⊤" | (some a) := "↑" ++ repr a end⟩

instance : has_coe_t α (with_top α) := ⟨some⟩
instance : has_top (with_top α) := ⟨none⟩

instance : inhabited (with_top α) := ⟨⊤⟩

lemma none_eq_top : (none : with_top α) = (⊤ : with_top α) := rfl
lemma some_eq_coe (a : α) : (some a : with_top α) = (↑a : with_top α) := rfl

@[simp] lemma top_ne_coe : ⊤ ≠ (a : with_top α) .
@[simp] lemma coe_ne_top : (a : with_top α) ≠ ⊤ .

/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_eliminator]
def rec_top_coe {C : with_top α → Sort*} (h₁ : C ⊤) (h₂ : Π (a : α), C a) :
  Π (n : with_top α), C n :=
option.rec h₁ h₂

@[norm_cast] lemma coe_eq_coe : (a : with_top α) = b ↔ a = b := option.some_inj

-- the `by exact` here forces the type of the equality to be `@eq (with_top α)`
@[simp] lemma map_top (f : α → β) :
  (by exact option.map f (⊤ : with_top α)) = (⊤ : with_top β) := rfl
lemma map_coe (f : α → β) (a : α) :
  (by exact option.map f (a : with_top α)) = (f a : with_top β) := rfl

lemma ne_top_iff_exists {x : with_top α} : x ≠ ⊤ ↔ ∃ (a : α), ↑a = x := option.ne_none_iff_exists

/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : Π (x : with_top α), x ≠ ⊤ → α :=
with_bot.unbot

@[simp] lemma coe_untop (x : with_top α) (h : x ≠ ⊤) : (x.untop h : with_top α) = x :=
by { cases x, simpa using h, refl, }

@[simp] lemma untop_coe (x : α) (h : (x : with_top α) ≠ ⊤ := coe_ne_top) :
  (x : with_top α).untop h = x := rfl

instance : can_lift (with_top α) α :=
{ coe := coe,
  cond := λ r, r ≠ ⊤,
  prf := λ x h, ⟨x.untop h, coe_untop _ _⟩ }

section has_le
variables [has_le α]

@[priority 10]
instance : has_le (with_top α) := ⟨λ o₁ o₂ : option α, ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a⟩

@[simp] lemma some_le_some : @has_le.le (with_top α) _ (some a) (some b) ↔ a ≤ b := by simp [(≤)]
@[simp, norm_cast] lemma coe_le_coe : (a : with_top α) ≤ b ↔ a ≤ b := some_le_some

@[simp] lemma le_none {a : with_top α} : @has_le.le (with_top α) _ a none :=
λ b h, option.no_confusion h

instance : order_top (with_top α) := { le_top := λ a, le_none, .. with_top.has_top }

instance [order_bot α] : order_bot (with_top α) :=
{ bot := some ⊥,
  bot_le := λ o a ha, by cases ha; exact ⟨_, rfl, bot_le⟩ }

instance [order_bot α] : bounded_order (with_top α) :=
{ ..with_top.order_top, ..with_top.order_bot }

lemma not_top_le_coe (a : α) : ¬ (⊤ : with_top α) ≤ ↑a :=
λ h, let ⟨b, hb, _⟩ := h _ rfl in option.not_mem_none _ hb

lemma le_coe : ∀ {o : option α}, a ∈ o → (@has_le.le (with_top α) _ o b ↔ a ≤ b) | _ rfl :=
coe_le_coe

lemma le_coe_iff : ∀ {x : with_top α}, x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b
| (some a) := by simp [some_eq_coe, coe_eq_coe]
| none     := iff_of_false (not_top_le_coe _) $ by simp [none_eq_top]

lemma coe_le_iff : ∀ {x : with_top α}, ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b
| (some b) := by simp [some_eq_coe, coe_eq_coe]
| none     := by simp [none_eq_top]

protected lemma _root_.is_min.with_top (h : is_min a) : is_min (a : with_top α)
| none _ := le_top
| (some b) hb := some_le_some.2 $ h $ some_le_some.1 hb

end has_le

section has_lt
variables [has_lt α]

@[priority 10]
instance : has_lt (with_top α) := ⟨λ o₁ o₂ : option α, ∃ b ∈ o₁, ∀ a ∈ o₂, b < a⟩

@[simp] lemma some_lt_some : @has_lt.lt (with_top α) _ (some a) (some b) ↔ a < b := by simp [(<)]
@[simp, norm_cast] lemma coe_lt_coe : (a : with_top α) < b ↔ a < b := some_lt_some

@[simp] lemma some_lt_none (a : α) : @has_lt.lt (with_top α) _ (some a) none :=
⟨a, rfl, λ b hb, (option.not_mem_none _ hb).elim⟩
lemma coe_lt_top (a : α) : (a : with_top α) < ⊤ := some_lt_none a

@[simp] lemma not_none_lt (a : with_top α) : ¬ @has_lt.lt (with_top α) _ none a :=
λ ⟨_, h, _⟩, option.not_mem_none _ h

lemma lt_iff_exists_coe : ∀ {a b : with_top α}, a < b ↔ ∃ p : α, a = p ∧ ↑p < b
| (some a) b := by simp [some_eq_coe, coe_eq_coe]
| none     b := iff_of_false (not_none_lt _) $ by simp [none_eq_top]

lemma coe_lt_iff : ∀ {x : with_top α}, ↑a < x ↔ ∀ b, x = ↑b → a < b
| (some b) := by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
| none     := by simp [none_eq_top, coe_lt_top]

end has_lt

instance [preorder α] : preorder (with_top α) :=
{ le          := (≤),
  lt          := (<),
  lt_iff_le_not_le := by { intros, cases a; cases b; simp [lt_iff_le_not_le]; simp [(<), (≤)] },
  le_refl     := λ o a ha, ⟨a, ha, le_rfl⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ c hc,
    let ⟨b, hb, bc⟩ := h₂ c hc, ⟨a, ha, ab⟩ := h₁ b hb in
    ⟨a, ha, le_trans ab bc⟩ }

instance [partial_order α] : partial_order (with_top α) :=
{ le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₂ with b,
    { cases o₁ with a, {refl},
      rcases h₂ a rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ b rfl with ⟨a, ⟨⟩, h₁'⟩,
      rcases h₂ a rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end,
  .. with_top.preorder }

instance [semilattice_inf α] : semilattice_inf (with_top α) :=
{ inf          := option.lift_or_get (⊓),
  inf_le_left  := λ o₁ o₂ a ha,
    by cases ha; cases o₂; simp [option.lift_or_get],
  inf_le_right := λ o₁ o₂ a ha,
    by cases ha; cases o₁; simp [option.lift_or_get],
  le_inf       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases o₂ with b; cases o₃ with c; cases ha,
    { exact h₂ a rfl },
    { exact h₁ a rfl },
    { rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩,
      simp at h₂,
      exact ⟨d, rfl, le_inf h₁' h₂⟩ }
  end,
  ..with_top.partial_order }

lemma coe_inf [semilattice_inf α] (a b : α) : ((a ⊓ b : α) : with_top α) = a ⊓ b := rfl

instance [semilattice_sup α] : semilattice_sup (with_top α) :=
{ sup          := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a ⊔ b)),
  le_sup_left  := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, le_sup_left⟩
  end,
  le_sup_right := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, le_sup_right⟩
  end,
  sup_le       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, sup_le ab ac⟩
  end,
  ..with_top.partial_order }

lemma coe_sup [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_top α) = a ⊔ b := rfl

instance [lattice α] : lattice (with_top α) :=
{ ..with_top.semilattice_sup, ..with_top.semilattice_inf }

instance decidable_le [has_le α] [@decidable_rel α (≤)] : @decidable_rel (with_top α) (≤) :=
λ x y, @with_bot.decidable_le αᵒᵈ _ _ y x

instance decidable_lt [has_lt α] [@decidable_rel α (<)] : @decidable_rel (with_top α) (<) :=
λ x y, @with_bot.decidable_lt αᵒᵈ _ _ y x

instance is_total_le [has_le α] [is_total α (≤)] : is_total (with_top α) (≤) :=
⟨λ a b, match a, b with
  | _     , none   := or.inl le_top
  | none  , _      := or.inr le_top
  | some x, some y := (total_of (≤) x y).imp some_le_some.2 some_le_some.2
  end⟩

instance [linear_order α] : linear_order (with_top α) := lattice.to_linear_order _

@[simp, norm_cast]
lemma coe_min [linear_order α] (x y : α) : (↑(min x y) : with_top α) = min x y := rfl

@[simp, norm_cast]
lemma coe_max [linear_order α] (x y : α) : (↑(max x y) : with_top α) = max x y := rfl

lemma well_founded_lt [preorder α] (h : @well_founded α (<)) : @well_founded (with_top α) (<) :=
have acc_some : ∀ a : α, acc ((<) : with_top α → with_top α → Prop) (some a) :=
λ a, acc.intro _ (well_founded.induction h a
  (show ∀ b, (∀ c, c < b → ∀ d : with_top α, d < some c → acc (<) d) →
    ∀ y : with_top α, y < some b → acc (<) y,
  from λ b ih c, option.rec_on c (λ hc, (not_lt_of_ge le_top hc).elim)
    (λ c hc, acc.intro _ (ih _ (some_lt_some.1 hc))))),
⟨λ a, option.rec_on a (acc.intro _ (λ y, option.rec_on y (λ h, (lt_irrefl _ h).elim)
  (λ _ _, acc_some _))) acc_some⟩

lemma well_founded_gt [preorder α] (h : @well_founded α (>)) : @well_founded (with_top α) (>) :=
@with_bot.well_founded_lt αᵒᵈ _ h

lemma _root_.with_bot.well_founded_gt [preorder α] (h : @well_founded α (>)) :
  @well_founded (with_bot α) (>) :=
@with_top.well_founded_lt αᵒᵈ _ h

instance [has_lt α] [densely_ordered α] [no_max_order α] : densely_ordered (with_top α) :=
⟨ λ a b,
  match a, b with
  | none,   a   := λ h : ⊤ < a, (not_none_lt _ h).elim
  | some a, none := λ h, let ⟨b, hb⟩ := exists_gt a in ⟨b, coe_lt_coe.2 hb, coe_lt_top b⟩
  | some a, some b := λ h, let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h) in
    ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩
  end⟩

lemma lt_iff_exists_coe_btwn [preorder α] [densely_ordered α] [no_max_order α] {a b : with_top α} :
  a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
⟨λ h, let ⟨y, hy⟩ := exists_between h, ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2 in ⟨x, hx.1 ▸ hy⟩,
 λ ⟨x, hx⟩, lt_trans hx.1 hx.2⟩

instance [has_le α] [no_bot_order α] [nonempty α] : no_bot_order (with_top α) :=
⟨begin
  apply with_top.rec_top_coe,
  { exact ‹nonempty α›.elim (λ a, ⟨a, not_top_le_coe a⟩) },
  { intro a,
    obtain ⟨b, h⟩ := exists_not_ge a,
    exact ⟨b, by rwa coe_le_coe⟩ }
end⟩

instance [has_lt α] [no_min_order α] [nonempty α] : no_min_order (with_top α) :=
⟨begin
  apply rec_top_coe,
  { exact ‹nonempty α›.elim (λ a, ⟨a, with_top.coe_lt_top a⟩) },
  { intro a,
    obtain ⟨b, ha⟩ := exists_lt a,
    exact ⟨b, coe_lt_coe.mpr ha⟩ }
end⟩

end with_top

/-! ### Subtype, order dual, product lattices -/

namespace subtype
variables {p : α → Prop}

/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
@[reducible] -- See note [reducible non-instances]
protected def order_bot [has_le α] [order_bot α] (hbot : p ⊥) : order_bot {x : α // p x} :=
{ bot := ⟨⊥, hbot⟩,
  bot_le := λ _, bot_le }

/-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/
@[reducible] -- See note [reducible non-instances]
protected def order_top [has_le α] [order_top α] (htop : p ⊤) : order_top {x : α // p x} :=
{ top := ⟨⊤, htop⟩,
  le_top := λ _, le_top }

/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
@[reducible] -- See note [reducible non-instances]
protected def bounded_order [has_le α] [bounded_order α] (hbot : p ⊥) (htop : p ⊤) :
  bounded_order (subtype p) :=
{ ..subtype.order_top htop, ..subtype.order_bot hbot }

variables [partial_order α]

@[simp] lemma mk_bot [order_bot α] [order_bot (subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
le_bot_iff.1 $ coe_le_coe.1 bot_le

@[simp] lemma mk_top [order_top α] [order_top (subtype p)] (htop : p ⊤) : mk ⊤ htop = ⊤ :=
top_le_iff.1 $ coe_le_coe.1 le_top

lemma coe_bot [order_bot α] [order_bot (subtype p)] (hbot : p ⊥) : ((⊥ : subtype p) : α) = ⊥ :=
congr_arg coe (mk_bot hbot).symm

lemma coe_top [order_top α] [order_top (subtype p)] (htop : p ⊤) : ((⊤ : subtype p) : α) = ⊤ :=
congr_arg coe (mk_top htop).symm

@[simp] lemma coe_eq_bot_iff [order_bot α] [order_bot (subtype p)] (hbot : p ⊥) {x : {x // p x}} :
  (x : α) = ⊥ ↔ x = ⊥ :=
by rw [←coe_bot hbot, ext_iff]

@[simp] lemma coe_eq_top_iff [order_top α] [order_top (subtype p)] (htop : p ⊤) {x : {x // p x}} :
  (x : α) = ⊤ ↔ x = ⊤ :=
by rw [←coe_top htop, ext_iff]

@[simp] lemma mk_eq_bot_iff [order_bot α] [order_bot (subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
  (⟨x, hx⟩ : subtype p) = ⊥ ↔ x = ⊥ :=
(coe_eq_bot_iff hbot).symm

@[simp] lemma mk_eq_top_iff [order_top α] [order_top (subtype p)] (htop : p ⊤) {x : α} (hx : p x) :
  (⟨x, hx⟩ : subtype p) = ⊤ ↔ x = ⊤ :=
(coe_eq_top_iff htop).symm

end subtype

section order_dual
variable (α)

instance [has_bot α] : has_top αᵒᵈ := ⟨(⊥ : α)⟩
instance [has_top α] : has_bot αᵒᵈ := ⟨(⊤ : α)⟩

instance [has_le α] [order_bot α] : order_top αᵒᵈ :=
{ le_top := @bot_le α _ _,
  .. order_dual.has_top α }

instance [has_le α] [order_top α] : order_bot αᵒᵈ :=
{ bot_le := @le_top α _ _,
  .. order_dual.has_bot α }

instance [has_le α] [bounded_order α] : bounded_order αᵒᵈ :=
{ .. order_dual.order_top α, .. order_dual.order_bot α }

open order_dual

@[simp] lemma of_dual_bot [has_top α] : of_dual ⊥ = (⊤ : α) := rfl
@[simp] lemma of_dual_top [has_bot α] : of_dual ⊤ = (⊥ : α) := rfl
@[simp] lemma to_dual_bot [has_bot α] : to_dual (⊥ : α) = ⊤ := rfl
@[simp] lemma to_dual_top [has_top α] : to_dual (⊤ : α) = ⊥ := rfl

end order_dual

namespace prod
variables (α β)

instance [has_top α] [has_top β] : has_top (α × β) := ⟨⟨⊤, ⊤⟩⟩
instance [has_bot α] [has_bot β] : has_bot (α × β) := ⟨⟨⊥, ⊥⟩⟩

instance [has_le α] [has_le β] [order_top α] [order_top β] : order_top (α × β) :=
{ le_top := λ a, ⟨le_top, le_top⟩,
  .. prod.has_top α β }

instance [has_le α] [has_le β] [order_bot α] [order_bot β] : order_bot (α × β) :=
{ bot_le := λ a, ⟨bot_le, bot_le⟩,
  .. prod.has_bot α β }

instance [has_le α] [has_le β] [bounded_order α] [bounded_order β] : bounded_order (α × β) :=
{ .. prod.order_top α β, .. prod.order_bot α β }


end prod

/-! ### Disjointness and complements -/

section disjoint
section semilattice_inf_bot
variables [semilattice_inf α] [order_bot α]

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.) -/
def disjoint (a b : α) : Prop := a ⊓ b ≤ ⊥

theorem disjoint.eq_bot {a b : α} (h : disjoint a b) : a ⊓ b = ⊥ :=
eq_bot_iff.2 h

theorem disjoint_iff {a b : α} : disjoint a b ↔ a ⊓ b = ⊥ :=
eq_bot_iff.symm

theorem disjoint.comm {a b : α} : disjoint a b ↔ disjoint b a :=
by rw [disjoint, disjoint, inf_comm]

@[symm] theorem disjoint.symm ⦃a b : α⦄ : disjoint a b → disjoint b a :=
disjoint.comm.1

lemma symmetric_disjoint : symmetric (disjoint : α → α → Prop) := disjoint.symm

@[simp] theorem disjoint_bot_left {a : α} : disjoint ⊥ a := inf_le_left
@[simp] theorem disjoint_bot_right {a : α} : disjoint a ⊥ := inf_le_right

theorem disjoint.mono {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
  disjoint b d → disjoint a c := le_trans (inf_le_inf h₁ h₂)

theorem disjoint.mono_left {a b c : α} (h : a ≤ b) : disjoint b c → disjoint a c :=
disjoint.mono h le_rfl

theorem disjoint.mono_right {a b c : α} (h : b ≤ c) : disjoint a c → disjoint a b :=
disjoint.mono le_rfl h

@[simp] lemma disjoint_self {a : α} : disjoint a a ↔ a = ⊥ :=
by simp [disjoint]

lemma disjoint.ne {a b : α} (ha : a ≠ ⊥) (hab : disjoint a b) : a ≠ b :=
by { intro h, rw [←h, disjoint_self] at hab, exact ha hab }

lemma disjoint.eq_bot_of_le {a b : α} (hab : disjoint a b) (h : a ≤ b) : a = ⊥ :=
eq_bot_iff.2 (by rwa ←inf_eq_left.2 h)

lemma disjoint_assoc {a b c : α} : disjoint (a ⊓ b) c ↔ disjoint a (b ⊓ c) :=
by rw [disjoint, disjoint, inf_assoc]

lemma disjoint.of_disjoint_inf_of_le {a b c : α} (h : disjoint (a ⊓ b) c) (hle : a ≤ c) :
  disjoint a b := by rw [disjoint_iff, h.eq_bot_of_le (inf_le_left.trans hle)]

lemma disjoint.of_disjoint_inf_of_le' {a b c : α} (h : disjoint (a ⊓ b) c) (hle : b ≤ c) :
  disjoint a b := by rw [disjoint_iff, h.eq_bot_of_le (inf_le_right.trans hle)]

end semilattice_inf_bot

section order_bot

variables [lattice α] [order_bot α]

lemma eq_bot_of_disjoint_absorbs
  {a b : α} (w : disjoint a b) (h : a ⊔ b = a) : b = ⊥ :=
begin
  rw disjoint_iff at w,
  rw [←w, right_eq_inf],
  rwa sup_eq_left at h,
end

end order_bot

section bounded_order

variables [lattice α] [bounded_order α] {a : α}

@[simp] theorem disjoint_top : disjoint a ⊤ ↔ a = ⊥ := by simp [disjoint_iff]
@[simp] theorem top_disjoint : disjoint ⊤ a ↔ a = ⊥ := by simp [disjoint_iff]

end bounded_order

section linear_order

variables [linear_order α]

lemma min_top_left [order_top α] (a : α) : min (⊤ : α) a = a := min_eq_right le_top
lemma min_top_right [order_top α] (a : α) : min a ⊤ = a := min_eq_left le_top
lemma max_bot_left [order_bot α] (a : α) : max (⊥ : α) a = a := max_eq_right bot_le
lemma max_bot_right [order_bot α] (a : α) : max a ⊥ = a := max_eq_left bot_le

-- `simp` can prove these, so they shouldn't be simp-lemmas.
lemma min_bot_left [order_bot α] (a : α) : min ⊥ a = ⊥ := min_eq_left bot_le
lemma min_bot_right [order_bot α] (a : α) : min a ⊥ = ⊥ := min_eq_right bot_le
lemma max_top_left [order_top α] (a : α) : max ⊤ a = ⊤ := max_eq_left le_top
lemma max_top_right [order_top α] (a : α) : max a ⊤ = ⊤ := max_eq_right le_top

@[simp] lemma min_eq_bot [order_bot α] {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ :=
by { symmetry, cases le_total a b; simpa [*, min_eq_left, min_eq_right] using eq_bot_mono h }

@[simp] lemma max_eq_top [order_top α] {a b : α} : max a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
@min_eq_bot αᵒᵈ _ _ a b

@[simp] lemma max_eq_bot [order_bot α] {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := sup_eq_bot_iff
@[simp] lemma min_eq_top [order_top α] {a b : α} : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ := inf_eq_top_iff

end linear_order

section distrib_lattice_bot
variables [distrib_lattice α] [order_bot α] {a b c : α}

@[simp] lemma disjoint_sup_left : disjoint (a ⊔ b) c ↔ disjoint a c ∧ disjoint b c :=
by simp only [disjoint_iff, inf_sup_right, sup_eq_bot_iff]

@[simp] lemma disjoint_sup_right : disjoint a (b ⊔ c) ↔ disjoint a b ∧ disjoint a c :=
by simp only [disjoint_iff, inf_sup_left, sup_eq_bot_iff]

lemma disjoint.sup_left (ha : disjoint a c) (hb : disjoint b c) : disjoint (a ⊔ b) c :=
disjoint_sup_left.2 ⟨ha, hb⟩

lemma disjoint.sup_right (hb : disjoint a b) (hc : disjoint a c) : disjoint a (b ⊔ c) :=
disjoint_sup_right.2 ⟨hb, hc⟩

lemma disjoint.left_le_of_le_sup_right {a b c : α} (h : a ≤ b ⊔ c) (hd : disjoint a c) : a ≤ b :=
(λ x, le_of_inf_le_sup_le x (sup_le h le_sup_right)) ((disjoint_iff.mp hd).symm ▸ bot_le)

lemma disjoint.left_le_of_le_sup_left {a b c : α} (h : a ≤ c ⊔ b) (hd : disjoint a c) : a ≤ b :=
@le_of_inf_le_sup_le _ _ a b c ((disjoint_iff.mp hd).symm ▸ bot_le)
  ((@sup_comm _ _ c b) ▸ (sup_le h le_sup_left))

end distrib_lattice_bot

section semilattice_inf_bot

variables [semilattice_inf α] [order_bot α] {a b : α} (c : α)

lemma disjoint.inf_left (h : disjoint a b) : disjoint (a ⊓ c) b :=
h.mono_left inf_le_left

lemma disjoint.inf_left' (h : disjoint a b) : disjoint (c ⊓ a) b :=
h.mono_left inf_le_right

lemma disjoint.inf_right (h : disjoint a b) : disjoint a (b ⊓ c) :=
h.mono_right inf_le_left

lemma disjoint.inf_right' (h : disjoint a b) : disjoint a (c ⊓ b) :=
h.mono_right inf_le_right

end semilattice_inf_bot

end disjoint

lemma inf_eq_bot_iff_le_compl [distrib_lattice α] [bounded_order α] {a b c : α}
  (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c :=
⟨λ h,
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (a ⊓ b) ⊔ (a ⊓ c) : by simp [inf_sup_left]
    ... ≤ c : by simp [h, inf_le_right],
  λ h,
  bot_unique $
    calc a ⊓ b ≤ b ⊓ c : by { rw inf_comm, exact inf_le_inf_left _ h }
      ... = ⊥ : h₂⟩

section is_compl

/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
structure is_compl [lattice α] [bounded_order α] (x y : α) : Prop :=
(inf_le_bot : x ⊓ y ≤ ⊥)
(top_le_sup : ⊤ ≤ x ⊔ y)

namespace is_compl

section bounded_order

variables [lattice α] [bounded_order α] {x y z : α}

protected lemma disjoint (h : is_compl x y) : disjoint x y := h.1

@[symm] protected lemma symm (h : is_compl x y) : is_compl y x :=
⟨by { rw inf_comm, exact h.1 }, by { rw sup_comm, exact h.2 }⟩

lemma of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : is_compl x y :=
⟨le_of_eq h₁, le_of_eq h₂.symm⟩

lemma inf_eq_bot (h : is_compl x y) : x ⊓ y = ⊥ := h.disjoint.eq_bot

lemma sup_eq_top (h : is_compl x y) : x ⊔ y = ⊤ := top_unique h.top_le_sup

open order_dual (to_dual)

lemma to_order_dual (h : is_compl x y) : is_compl (to_dual x) (to_dual y) := ⟨h.2, h.1⟩

end bounded_order

variables [distrib_lattice α] [bounded_order α] {a b x y z : α}

lemma inf_left_le_of_le_sup_right (h : is_compl x y) (hle : a ≤ b ⊔ y) : a ⊓ x ≤ b :=
calc a ⊓ x ≤ (b ⊔ y) ⊓ x : inf_le_inf hle le_rfl
... = (b ⊓ x) ⊔ (y ⊓ x) : inf_sup_right
... = b ⊓ x : by rw [h.symm.inf_eq_bot, sup_bot_eq]
... ≤ b : inf_le_left

lemma le_sup_right_iff_inf_left_le {a b} (h : is_compl x y) : a ≤ b ⊔ y ↔ a ⊓ x ≤ b :=
⟨h.inf_left_le_of_le_sup_right, h.symm.to_order_dual.inf_left_le_of_le_sup_right⟩

lemma inf_left_eq_bot_iff (h : is_compl y z) : x ⊓ y = ⊥ ↔ x ≤ z :=
by rw [← le_bot_iff, ← h.le_sup_right_iff_inf_left_le, bot_sup_eq]

lemma inf_right_eq_bot_iff (h : is_compl y z) : x ⊓ z = ⊥ ↔ x ≤ y :=
h.symm.inf_left_eq_bot_iff

lemma disjoint_left_iff (h : is_compl y z) : disjoint x y ↔ x ≤ z :=
by { rw disjoint_iff, exact h.inf_left_eq_bot_iff }

lemma disjoint_right_iff (h : is_compl y z) : disjoint x z ↔ x ≤ y :=
h.symm.disjoint_left_iff

lemma le_left_iff (h : is_compl x y) : z ≤ x ↔ disjoint z y :=
h.disjoint_right_iff.symm

lemma le_right_iff (h : is_compl x y) : z ≤ y ↔ disjoint z x :=
h.symm.le_left_iff

lemma left_le_iff (h : is_compl x y) : x ≤ z ↔ ⊤ ≤ z ⊔ y :=
h.to_order_dual.le_left_iff

lemma right_le_iff (h : is_compl x y) : y ≤ z ↔ ⊤ ≤ z ⊔ x :=
h.symm.left_le_iff

protected lemma antitone {x' y'} (h : is_compl x y) (h' : is_compl x' y') (hx : x ≤ x') :
  y' ≤ y :=
h'.right_le_iff.2 $ le_trans h.symm.top_le_sup (sup_le_sup_left hx _)

lemma right_unique (hxy : is_compl x y) (hxz : is_compl x z) :
  y = z :=
le_antisymm (hxz.antitone hxy $ le_refl x) (hxy.antitone hxz $ le_refl x)

lemma left_unique (hxz : is_compl x z) (hyz : is_compl y z) :
  x = y :=
hxz.symm.right_unique hyz.symm

lemma sup_inf {x' y'} (h : is_compl x y) (h' : is_compl x' y') :
  is_compl (x ⊔ x') (y ⊓ y') :=
of_eq
  (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm,
    h'.inf_eq_bot, inf_bot_eq])
  (by rw [sup_inf_left, @sup_comm _ _ x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq,
    sup_assoc, sup_left_comm, h'.sup_eq_top, sup_top_eq])

lemma inf_sup {x' y'} (h : is_compl x y) (h' : is_compl x' y') :
  is_compl (x ⊓ x') (y ⊔ y') :=
(h.symm.sup_inf h'.symm).symm

end is_compl

lemma is_compl_bot_top [lattice α] [bounded_order α] : is_compl (⊥ : α) ⊤ :=
is_compl.of_eq bot_inf_eq sup_top_eq

lemma is_compl_top_bot [lattice α] [bounded_order α] : is_compl (⊤ : α) ⊥ :=
is_compl.of_eq inf_bot_eq top_sup_eq

section
variables [lattice α] [bounded_order α] {x : α}

lemma eq_top_of_is_compl_bot (h : is_compl x ⊥) : x = ⊤ :=
sup_bot_eq.symm.trans h.sup_eq_top

lemma eq_top_of_bot_is_compl (h : is_compl ⊥ x) : x = ⊤ :=
eq_top_of_is_compl_bot h.symm

lemma eq_bot_of_is_compl_top (h : is_compl x ⊤) : x = ⊥ :=
eq_top_of_is_compl_bot h.to_order_dual

lemma eq_bot_of_top_is_compl (h : is_compl ⊤ x) : x = ⊥ :=
eq_top_of_bot_is_compl h.to_order_dual

end

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
class is_complemented (α) [lattice α] [bounded_order α] : Prop :=
(exists_is_compl : ∀ (a : α), ∃ (b : α), is_compl a b)

export is_complemented (exists_is_compl)

namespace is_complemented
variables [lattice α] [bounded_order α] [is_complemented α]

instance : is_complemented αᵒᵈ :=
⟨λ a, let ⟨b, hb⟩ := exists_is_compl (show α, from a) in ⟨b, hb.to_order_dual⟩⟩

end is_complemented

end is_compl

section nontrivial

variables [partial_order α] [bounded_order α] [nontrivial α]

lemma bot_ne_top : (⊥ : α) ≠ ⊤ :=
λ H, not_nontrivial_iff_subsingleton.mpr (subsingleton_of_bot_eq_top H) ‹_›

lemma top_ne_bot : (⊤ : α) ≠ ⊥ := bot_ne_top.symm
lemma bot_lt_top : (⊥ : α) < ⊤ := lt_top_iff_ne_top.2 bot_ne_top

end nontrivial

namespace bool

-- TODO: is this comment relevant now that `bounded_order` is factored out?
-- Could be generalised to `bounded_distrib_lattice` and `is_complemented`
instance : bounded_order bool :=
{ top := tt,
  le_top := λ x, le_tt,
  bot := ff,
  bot_le := λ x, ff_le }

end bool

section bool

@[simp] lemma top_eq_tt : ⊤ = tt := rfl

@[simp] lemma bot_eq_ff : ⊥ = ff := rfl

end bool
