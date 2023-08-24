/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.lattice
import data.option.basic

/-!
# ⊤ and ⊥, bounded lattices and variants

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `has_<top/bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `order_<top/bot> α`: Order with a top/bottom element.
* `bounded_order α`: Order with a top and bottom element.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[distrib_lattice α] [order_bot α]`
  It captures the properties of `disjoint` that are common to `generalized_boolean_algebra` and
  `distrib_lattice` when `order_bot`.
* Bounded and distributive lattice. Notated by `[distrib_lattice α] [bounded_order α]`.
  Typical examples include `Prop` and `set α`.
-/

open function order_dual

set_option old_structure_cmd true

universes u v

variables {α : Type u} {β : Type v} {γ δ : Type*}

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

/-- An order is (noncomputably) either an `order_top` or a `no_order_top`. Use as
`casesI bot_order_or_no_bot_order α`. -/
noncomputable def top_order_or_no_top_order (α : Type*) [has_le α] :
  psum (order_top α) (no_top_order α) :=
begin
  by_cases H : ∀ a : α, ∃ b, ¬ b ≤ a,
  { exact psum.inr ⟨H⟩ },
  { push_neg at H,
    exact psum.inl ⟨_, classical.some_spec H⟩ }
end

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

/-- An order is (noncomputably) either an `order_bot` or a `no_order_bot`. Use as
`casesI bot_order_or_no_bot_order α`. -/
noncomputable def bot_order_or_no_bot_order (α : Type*) [has_le α] :
  psum (order_bot α) (no_bot_order α) :=
begin
  by_cases H : ∀ a : α, ∃ b, ¬ a ≤ b,
  { exact psum.inr ⟨H⟩ },
  { push_neg at H,
    exact psum.inl ⟨_, classical.some_spec H⟩ }
end

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



section nontrivial

variables [partial_order α] [bounded_order α] [nontrivial α]

@[simp] lemma bot_ne_top : (⊥ : α) ≠ ⊤ := λ h, not_subsingleton _ $ subsingleton_of_bot_eq_top h
@[simp] lemma top_ne_bot : (⊤ : α) ≠ ⊥ := bot_ne_top.symm
@[simp] lemma bot_lt_top : (⊥ : α) < ⊤ := lt_top_iff_ne_top.2 bot_ne_top

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
