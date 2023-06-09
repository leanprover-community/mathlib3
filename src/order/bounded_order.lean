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
lemma disjoint_left_comm : disjoint a (b ⊓ c) ↔ disjoint b (a ⊓ c) :=
by simp_rw [disjoint, inf_left_comm]
lemma disjoint_right_comm : disjoint (a ⊓ b) c ↔ disjoint (a ⊓ c) b :=
by simp_rw [disjoint, inf_right_comm]

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

section codisjoint
section semilattice_sup_top
variables [semilattice_sup α] [order_top α] {a b c d : α}

/-- Two elements of a lattice are codisjoint if their sup is the top element. -/
def codisjoint (a b : α) : Prop := ⊤ ≤ a ⊔ b

lemma codisjoint_iff : codisjoint a b ↔ a ⊔ b = ⊤ := top_le_iff
lemma codisjoint.eq_top : codisjoint a b → a ⊔ b = ⊤ := top_unique
lemma codisjoint.comm : codisjoint a b ↔ codisjoint b a := by rw [codisjoint, codisjoint, sup_comm]
@[symm] lemma codisjoint.symm ⦃a b : α⦄ : codisjoint a b → codisjoint b a := codisjoint.comm.1
lemma symmetric_codisjoint : symmetric (codisjoint : α → α → Prop) := codisjoint.symm
lemma codisjoint_assoc : codisjoint (a ⊔ b) c ↔ codisjoint a (b ⊔ c) :=
by rw [codisjoint, codisjoint, sup_assoc]
lemma codisjoint_left_comm : codisjoint a (b ⊔ c) ↔ codisjoint b (a ⊔ c) :=
by simp_rw [codisjoint, sup_left_comm]
lemma codisjoint_right_comm : codisjoint (a ⊔ b) c ↔ codisjoint (a ⊔ c) b :=
by simp_rw [codisjoint, sup_right_comm]

@[simp] lemma codisjoint_top_left : codisjoint ⊤ a := le_sup_left
@[simp] lemma codisjoint_top_right : codisjoint a ⊤ := le_sup_right

lemma codisjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : codisjoint a c → codisjoint b d :=
le_trans' $ sup_le_sup h₁ h₂

lemma codisjoint.mono_left (h : a ≤ b) : codisjoint a c → codisjoint b c := codisjoint.mono h le_rfl
lemma codisjoint.mono_right : b ≤ c → codisjoint a b → codisjoint a c := codisjoint.mono le_rfl

variables (c)

lemma codisjoint.sup_left (h : codisjoint a b) : codisjoint (a ⊔ c) b := h.mono_left le_sup_left
lemma codisjoint.sup_left' (h : codisjoint a b) : codisjoint (c ⊔ a) b := h.mono_left le_sup_right
lemma codisjoint.sup_right (h : codisjoint a b) : codisjoint a (b ⊔ c) := h.mono_right le_sup_left
lemma codisjoint.sup_right' (h : codisjoint a b) : codisjoint a (c ⊔ b) := h.mono_right le_sup_right

variables {c}

@[simp] lemma codisjoint_self : codisjoint a a ↔ a = ⊤ := by simp [codisjoint]

/- TODO: Rename `codisjoint.eq_top` to `codisjoint.sup_eq` and `codisjoint.eq_top_of_self` to
`codisjoint.eq_top` -/
alias codisjoint_self ↔ codisjoint.eq_top_of_self _

lemma codisjoint.ne (ha : a ≠ ⊤) (hab : codisjoint a b) : a ≠ b :=
λ h, ha $ codisjoint_self.1 $ by rwa ←h at hab

lemma codisjoint.eq_top_of_ge (hab : codisjoint a b) (h : b ≤ a) : a = ⊤ :=
eq_top_iff.2 $ by rwa ←sup_eq_left.2 h

lemma codisjoint.eq_top_of_le (hab : codisjoint a b) : a ≤ b → b = ⊤ := hab.symm.eq_top_of_ge

lemma codisjoint.of_codisjoint_sup_of_le (h : codisjoint (a ⊔ b) c) (hle : c ≤ a) :
  codisjoint a b :=
codisjoint_iff.2 $ h.eq_top_of_ge $ le_sup_of_le_left hle

lemma codisjoint.of_codisjoint_sup_of_le' (h : codisjoint (a ⊔ b) c) (hle : c ≤ b) :
  codisjoint a b :=
codisjoint_iff.2 $ h.eq_top_of_ge $ le_sup_of_le_right hle

end semilattice_sup_top

section lattice
variables [lattice α] [bounded_order α] {a : α}

@[simp] lemma codisjoint_bot : codisjoint a ⊥ ↔ a = ⊤ := by simp [codisjoint_iff]
@[simp] lemma bot_codisjoint : codisjoint ⊥ a ↔ a = ⊤ := by simp [codisjoint_iff]

end lattice

section distrib_lattice_top
variables [distrib_lattice α] [order_top α] {a b c : α}

@[simp] lemma codisjoint_inf_left : codisjoint (a ⊓ b) c ↔ codisjoint a c ∧ codisjoint b c :=
by simp only [codisjoint_iff, sup_inf_right, inf_eq_top_iff]

@[simp] lemma codisjoint_inf_right : codisjoint a (b ⊓ c) ↔ codisjoint a b ∧ codisjoint a c :=
by simp only [codisjoint_iff, sup_inf_left, inf_eq_top_iff]

lemma codisjoint.inf_left (ha : codisjoint a c) (hb : codisjoint b c) : codisjoint (a ⊓ b) c :=
codisjoint_inf_left.2 ⟨ha, hb⟩

lemma codisjoint.inf_right (hb : codisjoint a b) (hc : codisjoint a c) : codisjoint a (b ⊓ c) :=
codisjoint_inf_right.2 ⟨hb, hc⟩

lemma codisjoint.left_le_of_le_inf_right (h : a ⊓ b ≤ c) (hd : codisjoint b c) : a ≤ c :=
le_of_inf_le_sup_le (le_inf h inf_le_right) $ le_top.trans hd.symm

lemma codisjoint.left_le_of_le_inf_left (h : b ⊓ a ≤ c) (hd : codisjoint b c) : a ≤ c :=
hd.left_le_of_le_inf_right $ by rwa inf_comm

end distrib_lattice_top
end codisjoint

lemma disjoint.dual [semilattice_inf α] [order_bot α] {a b : α} :
  disjoint a b → codisjoint (to_dual a) (to_dual b) := id

lemma codisjoint.dual [semilattice_sup α] [order_top α] {a b : α} :
  codisjoint a b → disjoint (to_dual a) (to_dual b) := id

@[simp] lemma disjoint_to_dual_iff [semilattice_sup α] [order_top α] {a b : α} :
  disjoint (to_dual a) (to_dual b) ↔ codisjoint a b := iff.rfl
@[simp] lemma disjoint_of_dual_iff [semilattice_inf α] [order_bot α] {a b : αᵒᵈ} :
  disjoint (of_dual a) (of_dual b) ↔ codisjoint a b := iff.rfl
@[simp] lemma codisjoint_to_dual_iff [semilattice_inf α] [order_bot α] {a b : α} :
  codisjoint (to_dual a) (to_dual b) ↔ disjoint a b := iff.rfl
@[simp] lemma codisjoint_of_dual_iff [semilattice_sup α] [order_top α] {a b : αᵒᵈ} :
  codisjoint (of_dual a) (of_dual b) ↔ disjoint a b := iff.rfl

section distrib_lattice
variables [distrib_lattice α] [bounded_order α] {a b c : α}

lemma disjoint.le_of_codisjoint (hab : disjoint a b) (hbc : codisjoint b c) : a ≤ c :=
begin
  rw [←@inf_top_eq _ _ _ a, ←@bot_sup_eq _ _ _ c, ←hab.eq_bot, ←hbc.eq_top, sup_inf_right],
  exact inf_le_inf_right _ le_sup_left,
end

end distrib_lattice

section is_compl

/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
@[protect_proj] structure is_compl [lattice α] [bounded_order α] (x y : α) : Prop :=
(disjoint : disjoint x y)
(codisjoint : codisjoint x y)

namespace is_compl

section bounded_order

variables [lattice α] [bounded_order α] {x y z : α}

@[symm] protected lemma symm (h : is_compl x y) : is_compl y x := ⟨h.1.symm, h.2.symm⟩

lemma of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : is_compl x y := ⟨le_of_eq h₁, ge_of_eq h₂⟩

lemma inf_eq_bot (h : is_compl x y) : x ⊓ y = ⊥ := h.disjoint.eq_bot
lemma sup_eq_top (h : is_compl x y) : x ⊔ y = ⊤ := h.codisjoint.eq_top

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
h'.right_le_iff.2 $ le_trans h.symm.codisjoint (sup_le_sup_left hx _)

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

lemma is_compl_iff : is_compl a b ↔ disjoint a b ∧ codisjoint a b :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

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

section is_complemented
section lattice
variables [lattice α] [bounded_order α]

/-- An element is *complemented* if it has a complement. -/
def is_complemented (a : α) : Prop := ∃ b, is_compl a b

lemma is_complemented_bot : is_complemented (⊥ : α) := ⟨⊤, is_compl_bot_top⟩
lemma is_complemented_top : is_complemented (⊤ : α) := ⟨⊥, is_compl_top_bot⟩

end lattice

variables [distrib_lattice α] [bounded_order α] {a b : α}

lemma is_complemented.sup : is_complemented a → is_complemented b → is_complemented (a ⊔ b) :=
λ ⟨a', ha⟩ ⟨b', hb⟩, ⟨a' ⊓ b', ha.sup_inf hb⟩

lemma is_complemented.inf : is_complemented a → is_complemented b → is_complemented (a ⊓ b) :=
λ ⟨a', ha⟩ ⟨b', hb⟩, ⟨a' ⊔ b', ha.inf_sup hb⟩

end is_complemented

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
class complemented_lattice (α) [lattice α] [bounded_order α] : Prop :=
(exists_is_compl : ∀ a : α, is_complemented a)

export complemented_lattice (exists_is_compl)

namespace complemented_lattice
variables [lattice α] [bounded_order α] [complemented_lattice α]

instance : complemented_lattice αᵒᵈ :=
⟨λ a, let ⟨b, hb⟩ := exists_is_compl (show α, from a) in ⟨b, hb.dual⟩⟩

end complemented_lattice

-- TODO: Define as a sublattice?
/-- The sublattice of complemented elements. -/
@[reducible, derive partial_order]
def complementeds (α : Type*) [lattice α] [bounded_order α] : Type* := {a : α // is_complemented a}

namespace complementeds
section lattice
variables [lattice α] [bounded_order α] {a b : complementeds α}

instance has_coe_t : has_coe_t (complementeds α) α := ⟨subtype.val⟩

lemma coe_injective : injective (coe : complementeds α → α) := subtype.coe_injective

@[simp, norm_cast] lemma coe_inj : (a : α) = b ↔ a = b := subtype.coe_inj
@[simp, norm_cast] lemma coe_le_coe : (a : α) ≤ b ↔ a ≤ b := by simp
@[simp, norm_cast] lemma coe_lt_coe : (a : α) < b ↔ a < b := iff.rfl

instance : bounded_order (complementeds α) :=
subtype.bounded_order is_complemented_bot is_complemented_top

@[simp, norm_cast] lemma coe_bot : ((⊥ : complementeds α) : α) = ⊥ := rfl
@[simp, norm_cast] lemma coe_top : ((⊤ : complementeds α) : α) = ⊤ := rfl
@[simp] lemma mk_bot : (⟨⊥, is_complemented_bot⟩ : complementeds α) = ⊥ := rfl
@[simp] lemma mk_top : (⟨⊤, is_complemented_top⟩ : complementeds α) = ⊤ := rfl

instance : inhabited (complementeds α) := ⟨⊥⟩

end lattice

variables [distrib_lattice α] [bounded_order α] {a b : complementeds α}

instance : has_sup (complementeds α) := ⟨λ a b, ⟨a ⊔ b, a.2.sup b.2⟩⟩
instance : has_inf (complementeds α) := ⟨λ a b, ⟨a ⊓ b, a.2.inf b.2⟩⟩

@[simp, norm_cast] lemma coe_sup (a b : complementeds α) : (↑(a ⊔ b) : α) = a ⊔ b := rfl
@[simp, norm_cast] lemma coe_inf (a b : complementeds α) : (↑(a ⊓ b) : α) = a ⊓ b := rfl
@[simp] lemma mk_sup_mk {a b : α} (ha : is_complemented a) (hb : is_complemented b) :
  (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : complementeds α) = ⟨a ⊔ b, ha.sup hb⟩ := rfl
@[simp] lemma mk_inf_mk {a b : α} (ha : is_complemented a) (hb : is_complemented b) :
  (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : complementeds α) = ⟨a ⊓ b, ha.inf hb⟩ := rfl

instance : distrib_lattice (complementeds α) :=
complementeds.coe_injective.distrib_lattice _ coe_sup coe_inf

@[simp, norm_cast] lemma disjoint_coe : disjoint (a : α) b ↔ disjoint a b :=
by rw [disjoint, disjoint, ←coe_inf, ←coe_bot, coe_le_coe]

@[simp, norm_cast] lemma codisjoint_coe : codisjoint (a : α) b ↔ codisjoint a b :=
by rw [codisjoint, codisjoint, ←coe_sup, ←coe_top, coe_le_coe]

@[simp, norm_cast] lemma is_compl_coe : is_compl (a : α) b ↔ is_compl a b :=
by simp_rw [is_compl_iff, disjoint_coe, codisjoint_coe]

instance : complemented_lattice (complementeds α) :=
⟨λ ⟨a, b, h⟩, ⟨⟨b, a, h.symm⟩, is_compl_coe.1 h⟩⟩

end complementeds
end is_compl

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
