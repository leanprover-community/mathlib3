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

open order_dual

set_option old_structure_cmd true

universes u v

variables {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

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

namespace order_dual
variable (α)

instance [has_bot α] : has_top αᵒᵈ := ⟨(⊥ : α)⟩
instance [has_top α] : has_bot αᵒᵈ := ⟨(⊤ : α)⟩

instance [has_le α] [order_bot α] : order_top αᵒᵈ :=
{ le_top := @bot_le α _ _,
  .. order_dual.has_top α }

instance [has_le α] [order_top α] : order_bot αᵒᵈ :=
{ bot_le := @le_top α _ _,
  .. order_dual.has_bot α }

@[simp] lemma of_dual_bot [has_top α] : of_dual ⊥ = (⊤ : α) := rfl
@[simp] lemma of_dual_top [has_bot α] : of_dual ⊤ = (⊥ : α) := rfl
@[simp] lemma to_dual_bot [has_bot α] : to_dual (⊥ : α) = ⊤ := rfl
@[simp] lemma to_dual_top [has_top α] : to_dual (⊤ : α) = ⊥ := rfl

end order_dual

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
hf.dual.apply_eq_top_iff

lemma strict_anti.apply_eq_bot_iff (hf : strict_anti f) : f a = f ⊥ ↔ a = ⊥ :=
hf.dual.apply_eq_top_iff

variables [nontrivial α]

lemma not_is_max_bot : ¬ is_max (⊥ : α) := @not_is_min_top αᵒᵈ _ _ _

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
@sup_eq_bot_iff αᵒᵈ _ _ _ _

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

instance (α : Type u) [has_le α] [bounded_order α] : bounded_order αᵒᵈ :=
{ .. order_dual.order_top α, .. order_dual.order_bot α }

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

/-- Lift a map `f : α → β` to `with_bot α → with_bot β`. Implemented using `option.map`. -/
def map (f : α → β) : with_bot α → with_bot β := option.map f

@[simp] lemma map_bot (f : α → β) : map f ⊥ = ⊥ := rfl
@[simp] lemma map_coe (f : α → β) (a : α) : map f a = f a := rfl

lemma ne_bot_iff_exists {x : with_bot α} : x ≠ ⊥ ↔ ∃ (a : α), ↑a = x := option.ne_none_iff_exists

instance : can_lift (with_bot α) α :=
{ coe := coe,
  cond := λ r, r ≠ ⊥,
  prf := λ x, ne_bot_iff_exists.mp }

/-- Deconstruct a `x : with_bot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : Π (x : with_bot α), x ≠ ⊥ → α
| ⊥       h := absurd rfl h
| (x : α) h := x

@[simp] lemma coe_unbot (x : with_bot α) (h : x ≠ ⊥) : (x.unbot h : with_bot α) = x :=
by { lift x to α using id h, refl  }

@[simp] lemma unbot_coe (x : α) (h : (x : with_bot α) ≠ ⊥ := coe_ne_bot) :
  (x : with_bot α).unbot h = x := rfl

section has_le

protected def le (r : α → α → Prop) : with_bot α → with_bot α → Prop
| ⊥       _       := true
| (a : α) ⊥       := false
| (a : α) (b : α) := r a b

variables [has_le α]

@[priority 10]
instance : has_le (with_bot α) := ⟨with_bot.le (≤)⟩

@[simp, norm_cast] lemma coe_le_coe : (a : with_bot α) ≤ b ↔ a ≤ b := iff.rfl

instance : order_bot (with_bot α) := { bot_le := λ a, trivial, bot := ⊥ }

lemma not_coe_le_bot (a : α) : ¬ (a : with_bot α) ≤ ⊥ := not_false

protected lemma _root_.is_top.with_bot (h : is_top a) : is_top (a : with_bot α)
| ⊥       := bot_le
| (b : α) := coe_le_coe.2 $ h b

protected lemma _root_.is_max.with_bot (h : is_max a) : is_max (a : with_bot α)
| ⊥ _       := bot_le
| (b : α) hb := coe_le_coe.2 $ h $ coe_le_coe.1 hb

instance [order_top α] : order_top (with_bot α) :=
{ top := (⊤ : α),
  le_top := is_top_top.with_bot }

instance [order_top α] : bounded_order (with_bot α) :=
{ ..with_bot.order_top, ..with_bot.order_bot }

@[simp] lemma le_bot_iff : ∀ {a : with_bot α}, a ≤ ⊥ ↔ a = ⊥
| ⊥       := iff_of_true bot_le rfl
| (a : α) := iff_of_false (not_coe_le_bot _) coe_ne_bot

lemma coe_le : ∀ {o : option α}, b ∈ o → ((a : with_bot α) ≤ o ↔ a ≤ b) | _ rfl := coe_le_coe

lemma coe_le_iff : ∀ {x : with_bot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
| (b : α) := by simp [coe_eq_coe]
| ⊥       := iff_of_false (not_coe_le_bot _) $ by simp

lemma le_coe_iff : ∀ {x : with_bot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
| (b : α) := by simp [coe_eq_coe]
| ⊥       := by simp

lemma le_iff' : ∀ {a b : with_bot α}, a ≤ b ↔ ∀ x : α, a = x → ↑x ≤ b
| ⊥       _       := by simp
| (a : α) b       := by simp [coe_eq_coe]

lemma le_iff {a b : with_bot α} : a ≤ b ↔ ∀ x : α, a = x → ∃ y : α, b = y ∧ x ≤ y :=
by simp only [le_iff', coe_le_iff]

instance decidable_le [h : @decidable_rel α (≤)] : @decidable_rel (with_bot α) (≤)
| ⊥ x := is_true bot_le
| (x : α) (y : α) := h x y
| (x : α) ⊥ := is_false $ not_coe_le_bot x

instance is_total_le [is_total α (≤)] : is_total (with_bot α) (≤) :=
⟨λ a b, match a, b with
  | none  , _      := or.inl bot_le
  | _     , none   := or.inr bot_le
  | some x, some y := total_of (≤) x y
  end⟩

end has_le

section has_lt
variables [has_lt α]

@[priority 10]
instance : has_lt (with_bot α) :=
⟨λ a b, -- we swap `a` and `b` in `match` to ensure `⊥ < _` is `false` by `rfl`
  match b, a with
  ⊥, _ := false,
  (x : α), ⊥ := true,
  (x : α), (y : α) := y < x
  end⟩

@[simp, norm_cast] lemma coe_lt_coe : (a : with_bot α) < b ↔ a < b := iff.rfl

@[simp] lemma bot_lt_coe (a : α) : (⊥ : with_bot α) < a := trivial

@[simp] lemma not_lt_bot (a : with_bot α) : ¬ a < ⊥ := not_false

lemma lt_iff_exists_coe : ∀ {a b : with_bot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
| a (b : α) := by simp [coe_eq_coe]
| a ⊥       := iff_of_false (not_lt_bot _) $ λ ⟨p, hp, hap⟩, bot_ne_coe hp

lemma lt_coe_iff : ∀ {x : with_bot α}, x < b ↔ ∀ a, x = ↑a → a < b
| (a : α) := by simp [coe_eq_coe]
| ⊥       := by simp

instance decidable_lt [h : @decidable_rel α (<)] : @decidable_rel (with_bot α) (<)
| ⊥ (x : α) := is_true $ bot_lt_coe x
| (x : α) (y : α) := h x y
| x ⊥ := is_false $ not_lt_bot x

end has_lt

instance [preorder α] : preorder (with_bot α) :=
{ le          := (≤),
  lt          := (<),
  lt_iff_le_not_le := λ a b,
    by { cases a; cases b; simp [none_eq_bot, some_eq_coe, lt_iff_le_not_le] },
  le_refl     := λ a, rec_bot_coe bot_le le_refl a,
  le_trans    := λ a b c hab hbc,
    begin
      induction a using with_bot.rec_bot_coe, { exact bot_le },
      rcases coe_le_iff.1 hab with ⟨b, rfl, hab'⟩,
      rcases coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩,
      exact hab'.trans hbc'
    end}

instance [partial_order α] : partial_order (with_bot α) :=
{ le_antisymm := λ a b hab hba, begin
    induction a using with_bot.rec_bot_coe,
    { rwa [le_bot_iff, eq_comm] at hba },
    { rcases coe_le_iff.1 hab with ⟨b, rfl, hab'⟩,
      exact coe_eq_coe.mpr (hab'.antisymm hba) }
  end,
  .. with_bot.preorder }

lemma le_coe_get_or_else [preorder α] : ∀ (a : with_bot α) (b : α), a ≤ a.get_or_else b
| (a : α) b := le_refl a
| ⊥       b := bot_le

@[simp] lemma get_or_else_bot (a : α) : option.get_or_else (⊥ : with_bot α) a = a := rfl

lemma get_or_else_bot_le_iff [has_le α] [order_bot α] {a : with_bot α} {b : α} :
  a.get_or_else ⊥ ≤ b ↔ a ≤ b :=
by cases a; simp [none_eq_bot, some_eq_coe]

lemma get_or_else_bot_lt_iff [partial_order α] [order_bot α] {a : with_bot α} {b : α}
  (ha : a ≠ ⊥) :
  a.get_or_else ⊥ < b ↔ a < b :=
by { lift a to α using ha, refl }

instance [has_sup α] : has_sup (with_bot α) := ⟨option.lift_or_get (⊔)⟩

@[simp] lemma coe_sup [has_sup α] (a b : α) : ((a ⊔ b : α) : with_bot α) = a ⊔ b := rfl
@[simp] lemma bot_sup [has_sup α] (a : with_bot α) : ⊥ ⊔ a = a := option.lift_or_get_none_left
@[simp] lemma sup_bot [has_sup α] (a : with_bot α) : a ⊔ ⊥ = a := option.lift_or_get_none_right

private lemma sup_le_iff' [semilattice_sup α] {a b c : with_bot α} : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
by cases a; cases b; cases c;
  simp only [some_eq_coe, none_eq_bot, bot_sup, sup_bot, ← coe_sup, bot_le, true_and, and_true,
    not_coe_le_bot, coe_le_coe, sup_le_iff, false_and]

instance [semilattice_sup α] : semilattice_sup (with_bot α) :=
{ sup          := (⊔),
  le_sup_left  := λ a b, (sup_le_iff'.1 le_rfl).1,
  le_sup_right := λ a b, (sup_le_iff'.1 le_rfl).2,
  sup_le       := λ a b c hac hbc, sup_le_iff'.2 ⟨hac, hbc⟩,
  ..with_bot.order_bot,
  ..with_bot.partial_order }

instance [has_inf α] : has_inf (with_bot α) := ⟨λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a ⊓ b))⟩

@[simp] lemma coe_inf [has_inf α] (a b : α) : ((a ⊓ b : α) : with_bot α) = a ⊓ b := rfl
@[simp] lemma bot_inf [has_inf α] (a : with_bot α) : ⊥ ⊓ a = ⊥ := rfl
@[simp] lemma inf_bot [has_inf α] (a : with_bot α) : a ⊓ ⊥ = ⊥ := by cases a; refl

private lemma le_inf_iff' [semilattice_inf α] {a b c : with_bot α} : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
begin
  cases a, { simp [none_eq_bot] },
  cases b, { simp [none_eq_bot, some_eq_coe] },
  cases c, { simp [none_eq_bot, some_eq_coe] },
  simp only [some_eq_coe, ← coe_inf, coe_le_coe, le_inf_iff],
end

instance [semilattice_inf α] : semilattice_inf (with_bot α) :=
{ inf          := (⊓),
  inf_le_left  := λ a b, (le_inf_iff'.1 le_rfl).1,
  inf_le_right := λ a b, (le_inf_iff'.1 le_rfl).2,
  le_inf       := λ a b c hab hac, le_inf_iff'.2 ⟨hab, hac⟩,
  ..with_bot.order_bot,
  ..with_bot.partial_order }

instance [lattice α] : lattice (with_bot α) :=
{ ..with_bot.semilattice_sup, ..with_bot.semilattice_inf }

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
    (λ c hc, ih _ hc (lt_trans hc hba)))))))⟩

lemma well_founded_gt [preorder α] (h : @well_founded α (>)) : @well_founded (with_bot α) (>) :=
have acc_coe : ∀ a : α, acc (>) (a : with_bot α) :=
λ a, acc.intro _ (well_founded.induction h a
  (show ∀ b : α, (∀ (c > b) (d > (↑c : with_bot α)),  acc (>) d) →
    ∀ y > (↑b : with_bot α), acc (>) y,
  from λ b ih c, option.rec_on c (λ hc, (not_lt_of_ge bot_le hc).elim)
    (λ c hc, acc.intro _ (ih _ (hc))))),
⟨λ a, option.rec_on a (acc.intro _ (λ y, option.rec_on y (λ h, (lt_irrefl _ h).elim)
  (λ _ _, acc_coe _))) acc_coe⟩

instance [has_lt α] [densely_ordered α] [no_min_order α] : densely_ordered (with_bot α) :=
⟨ λ a b h,
  match a, b, h with
  | ⊥,       (b : α), h := let ⟨a, ha⟩ := exists_lt b in ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
  | (a : α), (b : α), h := let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h) in
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
    exact λ a, ⟨a, bot_lt_coe a⟩, },
  { intro a,
    obtain ⟨b, ha⟩ := exists_gt a,
    exact ⟨b, coe_lt_coe.mpr ha⟩, }
end⟩

end with_bot

--TODO(Mario): Construct using order dual on with_bot
/-- Attach `⊤` to a type. -/
def with_top (α : Type*) := (with_bot αᵒᵈ)ᵒᵈ

namespace with_top
variables {a b : α}

meta instance [has_to_format α] : has_to_format (with_top α) :=
{ to_format := λ x,
  match x with
  | none := "⊤"
  | some (x : α) := to_fmt x
  end }

instance [has_repr α] : has_repr (with_top α) :=
⟨λ o, match o with | none := "⊤" | some (a : α) := "↑" ++ repr a end⟩

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

/-- Lift a map `f : α → β` to `with_top α → with_top β`. Implemented using `option.map`. -/
def map (f : α → β) : with_top α → with_top β := option.map f

@[simp] lemma map_top (f : α → β) : map f ⊤ = ⊤ := rfl
@[simp] lemma map_coe (f : α → β) (a : α) : map f a = f a := rfl

lemma ne_top_iff_exists {x : with_top α} : x ≠ ⊤ ↔ ∃ (a : α), ↑a = x := option.ne_none_iff_exists

instance : can_lift (with_top α) α :=
{ coe := coe,
  cond := λ r, r ≠ ⊤,
  .. with_bot.can_lift }

/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : Π (x : with_top α), x ≠ ⊤ → α :=
with_bot.unbot

@[simp] lemma coe_untop (x : with_top α) (h : x ≠ ⊤) : (x.untop h : with_top α) = x :=
with_bot.coe_unbot x h

@[simp] lemma untop_coe (x : α) (h : (x : with_top α) ≠ ⊤ := coe_ne_top) :
  (x : with_top α).untop h = x := rfl

section has_le
variables [has_le α]

@[priority 10]
instance : has_le (with_top α) := order_dual.has_le _

@[simp, norm_cast] lemma coe_le_coe : (a : with_top α) ≤ b ↔ a ≤ b := iff.rfl

@[simp] protected lemma le_top {a : with_top α} : a ≤ ⊤ := trivial

lemma le_iff' {a b : with_top α} : a ≤ b ↔ ∀ y : α, b = y → a ≤ y := with_bot.le_iff'

lemma le_iff {a b : with_top α} : a ≤ b ↔ ∀ y : α, b = y → ∃ x : α, a = x ∧ x ≤ y :=
with_bot.le_iff

instance : order_top (with_top α) := order_dual.order_top _

instance [order_bot α] : order_bot (with_top α) :=
{ bot := (⊥ : α), .. order_dual.order_bot _ }

instance [order_bot α] : bounded_order (with_top α) :=
{ ..with_top.order_top, ..with_top.order_bot }

lemma not_top_le_coe (a : α) : ¬ (⊤ : with_top α) ≤ ↑a := with_bot.not_coe_le_bot (to_dual a)

lemma le_coe : ∀ {o : option α}, a ∈ o → (@has_le.le (with_top α) _ o b ↔ a ≤ b) | _ rfl :=
coe_le_coe

lemma le_coe_iff {x : with_top α} : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b := with_bot.coe_le_iff

lemma coe_le_iff {x : with_top α} : ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b := with_bot.le_coe_iff

protected lemma _root_.is_min.with_top (h : is_min a) : is_min (a : with_top α) :=
h.to_dual.with_bot

instance decidable_le [@decidable_rel α (≤)] : @decidable_rel (with_top α) (≤) :=
λ x y, @with_bot.decidable_le αᵒᵈ _ _ y x

end has_le

section has_lt
variables [has_lt α]

@[priority 10]
instance : has_lt (with_top α) := order_dual.has_lt _

@[simp, norm_cast] lemma coe_lt_coe : (a : with_top α) < b ↔ a < b := iff.rfl

lemma coe_lt_top (a : α) : (a : with_top α) < ⊤ := trivial

@[simp] lemma not_top_lt (a : with_top α) : ¬ ⊤ < a := not_false

lemma lt_iff_exists_coe {a b : with_top α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b :=
with_bot.lt_iff_exists_coe

lemma coe_lt_iff {x : with_top α} : ↑a < x ↔ ∀ b, x = ↑b → a < b := with_bot.lt_coe_iff

instance decidable_lt [@decidable_rel α (<)] : @decidable_rel (with_top α) (<) :=
λ x y, @with_bot.decidable_lt αᵒᵈ _ _ y x

end has_lt

instance [preorder α] : preorder (with_top α) := order_dual.preorder _

instance [partial_order α] : partial_order (with_top α) := order_dual.partial_order _

instance [has_inf α] : has_inf (with_top α) := order_dual.has_inf _

@[simp] lemma coe_inf [has_inf α] (a b : α) : ((a ⊓ b : α) : with_top α) = a ⊓ b := rfl
@[simp] lemma top_inf [has_inf α] (a : with_top α) : ⊤ ⊓ a = a := with_bot.bot_sup a
@[simp] lemma inf_top [has_inf α] (a : with_top α) : a ⊓ ⊤ = a := with_bot.sup_bot a

instance [semilattice_inf α] : semilattice_inf (with_top α) := order_dual.semilattice_inf _

instance [has_sup α] : has_sup (with_top α) := order_dual.has_sup _

@[simp] lemma coe_sup [has_sup α] (a b : α) : ((a ⊔ b : α) : with_top α) = a ⊔ b := rfl
@[simp] lemma top_sup [has_sup α] (a : with_top α) : ⊤ ⊔ a = ⊤ := rfl
@[simp] lemma sup_top [has_sup α] (a : with_top α) : a ⊔ ⊤ = ⊤ := with_bot.inf_bot a

instance [semilattice_sup α] : semilattice_sup (with_top α) := order_dual.semilattice_sup _

instance [lattice α] : lattice (with_top α) := order_dual.lattice _

instance is_total_le [has_le α] [is_total α (≤)] : is_total (with_top α) (≤) :=
@order_dual.is_total_le (with_bot αᵒᵈ) _ _

instance [linear_order α] : linear_order (with_top α) := order_dual.linear_order _

@[simp, norm_cast]
lemma coe_min [linear_order α] (x y : α) : (↑(min x y) : with_top α) = min x y := rfl

@[simp, norm_cast]
lemma coe_max [linear_order α] (x y : α) : (↑(max x y) : with_top α) = max x y := rfl

lemma well_founded_lt [preorder α] (h : @well_founded α (<)) : @well_founded (with_top α) (<) :=
with_bot.well_founded_gt h

lemma well_founded_gt [preorder α] (h : @well_founded α (>)) : @well_founded (with_top α) (>) :=
with_bot.well_founded_lt h

instance [has_lt α] [densely_ordered α] [no_max_order α] : densely_ordered (with_top α) :=
order_dual.densely_ordered (with_bot αᵒᵈ)

lemma lt_iff_exists_coe_btwn [preorder α] [densely_ordered α] [no_max_order α] {a b : with_top α} :
  a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
with_bot.lt_iff_exists_coe_btwn.trans $ exists_congr $ λ _, and_comm _ _

instance [has_le α] [no_bot_order α] [nonempty α] : no_bot_order (with_top α) :=
order_dual.no_bot_order (with_bot αᵒᵈ)

instance [has_lt α] [no_min_order α] [nonempty α] : no_min_order (with_top α) :=
order_dual.no_min_order (with_bot αᵒᵈ)

end with_top

section mono

variables [preorder α] [preorder β] {f : α → β}

protected lemma monotone.with_bot_map (hf : monotone f) : monotone (with_bot.map f)
| ⊥       _       h           := bot_le
| (a : α) (b : α) (h : a ≤ b) := hf h

protected lemma monotone.with_top_map (hf : monotone f) : monotone (with_top.map f) :=
hf.dual.with_bot_map.dual

protected lemma strict_mono.with_bot_map (hf : strict_mono f) : strict_mono (with_bot.map f)
| ⊥       (a : α) h           := with_bot.bot_lt_coe _
| (a : α) (b : α) (h : a < b) := hf h

protected lemma strict_mono.with_top_map (hf : strict_mono f) : strict_mono (with_top.map f) :=
hf.dual.with_bot_map.dual

end mono

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

section linear_order
variables [linear_order α]

-- `simp` can prove these, so they shouldn't be simp-lemmas.
lemma min_bot_left [order_bot α] (a : α) : min ⊥ a = ⊥ := bot_inf_eq
lemma max_top_left [order_top α] (a : α) : max ⊤ a = ⊤ := top_sup_eq
lemma min_top_left [order_top α] (a : α) : min ⊤ a = a := top_inf_eq
lemma max_bot_left [order_bot α] (a : α) : max ⊥ a = a := bot_sup_eq
lemma min_top_right [order_top α] (a : α) : min a ⊤ = a := inf_top_eq
lemma max_bot_right [order_bot α] (a : α) : max a ⊥ = a := sup_bot_eq
lemma min_bot_right [order_bot α] (a : α) : min a ⊥ = ⊥ := inf_bot_eq
lemma max_top_right [order_top α] (a : α) : max a ⊤ = ⊤ := sup_top_eq

@[simp] lemma min_eq_bot [order_bot α] {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ :=
by simp only [←inf_eq_min, ←le_bot_iff, inf_le_iff]

@[simp] lemma max_eq_top [order_top α] {a b : α} : max a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
@min_eq_bot αᵒᵈ _ _ a b

@[simp] lemma max_eq_bot [order_bot α] {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := sup_eq_bot_iff
@[simp] lemma min_eq_top [order_top α] {a b : α} : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ := inf_eq_top_iff

end linear_order

/-! ### Disjointness and complements -/

section disjoint
section semilattice_inf_bot
variables [semilattice_inf α] [order_bot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.) -/
def disjoint (a b : α) : Prop := a ⊓ b ≤ ⊥

lemma disjoint_iff : disjoint a b ↔ a ⊓ b = ⊥ := le_bot_iff
lemma disjoint.eq_bot : disjoint a b → a ⊓ b = ⊥ := bot_unique
lemma disjoint.comm : disjoint a b ↔ disjoint b a := by rw [disjoint, disjoint, inf_comm]
@[symm] lemma disjoint.symm ⦃a b : α⦄ : disjoint a b → disjoint b a := disjoint.comm.1
lemma symmetric_disjoint : symmetric (disjoint : α → α → Prop) := disjoint.symm
lemma disjoint_assoc : disjoint (a ⊓ b) c ↔ disjoint a (b ⊓ c) :=
by rw [disjoint, disjoint, inf_assoc]

@[simp] lemma disjoint_bot_left : disjoint ⊥ a := inf_le_left
@[simp] lemma disjoint_bot_right : disjoint a ⊥ := inf_le_right

lemma disjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : disjoint b d → disjoint a c :=
le_trans $ inf_le_inf h₁ h₂

lemma disjoint.mono_left (h : a ≤ b) : disjoint b c → disjoint a c := disjoint.mono h le_rfl
lemma disjoint.mono_right : b ≤ c → disjoint a c → disjoint a b := disjoint.mono le_rfl

variables (c)

lemma disjoint.inf_left (h : disjoint a b) : disjoint (a ⊓ c) b := h.mono_left inf_le_left
lemma disjoint.inf_left' (h : disjoint a b) : disjoint (c ⊓ a) b := h.mono_left inf_le_right
lemma disjoint.inf_right (h : disjoint a b) : disjoint a (b ⊓ c) := h.mono_right inf_le_left
lemma disjoint.inf_right' (h : disjoint a b) : disjoint a (c ⊓ b) := h.mono_right inf_le_right

variables {c}

@[simp] lemma disjoint_self : disjoint a a ↔ a = ⊥ := by simp [disjoint]

/- TODO: Rename `disjoint.eq_bot` to `disjoint.inf_eq` and `disjoint.eq_bot_of_self` to
`disjoint.eq_bot` -/
alias disjoint_self ↔ disjoint.eq_bot_of_self _

lemma disjoint.ne (ha : a ≠ ⊥) (hab : disjoint a b) : a ≠ b :=
λ h, ha $ disjoint_self.1 $ by rwa ←h at hab

lemma disjoint.eq_bot_of_le (hab : disjoint a b) (h : a ≤ b) : a = ⊥ :=
eq_bot_iff.2 (by rwa ←inf_eq_left.2 h)

lemma disjoint.eq_bot_of_ge (hab : disjoint a b) : b ≤ a → b = ⊥ := hab.symm.eq_bot_of_le

lemma disjoint.of_disjoint_inf_of_le (h : disjoint (a ⊓ b) c) (hle : a ≤ c) : disjoint a b :=
disjoint_iff.2 $ h.eq_bot_of_le $ inf_le_of_left_le hle

lemma disjoint.of_disjoint_inf_of_le' (h : disjoint (a ⊓ b) c) (hle : b ≤ c) : disjoint a b :=
disjoint_iff.2 $ h.eq_bot_of_le $ inf_le_of_right_le hle

end semilattice_inf_bot

section lattice
variables [lattice α] [bounded_order α] {a : α}

@[simp] theorem disjoint_top : disjoint a ⊤ ↔ a = ⊥ := by simp [disjoint_iff]
@[simp] theorem top_disjoint : disjoint ⊤ a ↔ a = ⊥ := by simp [disjoint_iff]

end lattice

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

lemma disjoint.left_le_of_le_sup_right (h : a ≤ b ⊔ c) (hd : disjoint a c) : a ≤ b :=
le_of_inf_le_sup_le (le_trans hd bot_le) $ sup_le h le_sup_right

lemma disjoint.left_le_of_le_sup_left (h : a ≤ c ⊔ b) (hd : disjoint a c) : a ≤ b :=
hd.left_le_of_le_sup_right $ by rwa sup_comm

end distrib_lattice_bot
end disjoint

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

lemma of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : is_compl x y := ⟨h₁.le, h₂.ge⟩

lemma inf_eq_bot (h : is_compl x y) : x ⊓ y = ⊥ := h.disjoint.eq_bot

lemma sup_eq_top (h : is_compl x y) : x ⊔ y = ⊤ := top_unique h.top_le_sup

lemma dual (h : is_compl x y) : is_compl (to_dual x) (to_dual y) := ⟨h.2, h.1⟩
lemma of_dual {a b : αᵒᵈ} (h : is_compl a b) : is_compl (of_dual a) (of_dual b) := ⟨h.2, h.1⟩

end bounded_order

variables [distrib_lattice α] [bounded_order α] {a b x y z : α}

lemma inf_left_le_of_le_sup_right (h : is_compl x y) (hle : a ≤ b ⊔ y) : a ⊓ x ≤ b :=
calc a ⊓ x ≤ (b ⊔ y) ⊓ x : inf_le_inf hle le_rfl
... = (b ⊓ x) ⊔ (y ⊓ x) : inf_sup_right
... = b ⊓ x : by rw [h.symm.inf_eq_bot, sup_bot_eq]
... ≤ b : inf_le_left

lemma le_sup_right_iff_inf_left_le {a b} (h : is_compl x y) : a ≤ b ⊔ y ↔ a ⊓ x ≤ b :=
⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩

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

lemma left_le_iff (h : is_compl x y) : x ≤ z ↔ ⊤ ≤ z ⊔ y := h.dual.le_left_iff

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

section
variables [lattice α] [bounded_order α] {a b x : α}

@[simp] lemma is_compl_to_dual_iff : is_compl (to_dual a) (to_dual b) ↔ is_compl a b :=
⟨is_compl.of_dual, is_compl.dual⟩

@[simp] lemma is_compl_of_dual_iff {a b : αᵒᵈ} : is_compl (of_dual a) (of_dual b) ↔ is_compl a b :=
⟨is_compl.dual, is_compl.of_dual⟩

lemma is_compl_bot_top : is_compl (⊥ : α) ⊤ := is_compl.of_eq bot_inf_eq sup_top_eq
lemma is_compl_top_bot : is_compl (⊤ : α) ⊥ := is_compl.of_eq inf_bot_eq top_sup_eq

lemma eq_top_of_is_compl_bot (h : is_compl x ⊥) : x = ⊤ := sup_bot_eq.symm.trans h.sup_eq_top
lemma eq_top_of_bot_is_compl (h : is_compl ⊥ x) : x = ⊤ := eq_top_of_is_compl_bot h.symm
lemma eq_bot_of_is_compl_top (h : is_compl x ⊤) : x = ⊥ := eq_top_of_is_compl_bot h.dual
lemma eq_bot_of_top_is_compl (h : is_compl ⊤ x) : x = ⊥ := eq_top_of_bot_is_compl h.dual

end

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
class is_complemented (α) [lattice α] [bounded_order α] : Prop :=
(exists_is_compl : ∀ (a : α), ∃ (b : α), is_compl a b)

export is_complemented (exists_is_compl)

namespace is_complemented
variables [lattice α] [bounded_order α] [is_complemented α]

instance : is_complemented αᵒᵈ :=
⟨λ a, let ⟨b, hb⟩ := exists_is_compl (show α, from a) in ⟨b, hb.dual⟩⟩

end is_complemented

end is_compl

section nontrivial

variables [partial_order α] [bounded_order α] [nontrivial α]

lemma bot_ne_top : (⊥ : α) ≠ ⊤ :=
λ H, not_nontrivial_iff_subsingleton.mpr (subsingleton_of_bot_eq_top H) ‹_›

lemma top_ne_bot : (⊤ : α) ≠ ⊥ := bot_ne_top.symm
lemma bot_lt_top : (⊥ : α) < ⊤ := lt_top_iff_ne_top.2 bot_ne_top

end nontrivial

section bool
open bool

instance : bounded_order bool :=
{ top := tt,
  le_top := λ x, le_tt,
  bot := ff,
  bot_le := λ x, ff_le }

@[simp] lemma top_eq_tt : ⊤ = tt := rfl
@[simp] lemma bot_eq_ff : ⊥ = ff := rfl

end bool
