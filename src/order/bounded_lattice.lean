/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.option.basic
import logic.nontrivial
import order.lattice
import tactic.pi_instances

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `has_<top/bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `order_<top/bot> α`: Order with a top/bottom element.
* `with_<top/bot> α`: Equips `option α` with the order on `α` plus `none` as the top/bottom element.
* `semilattice_<sup/inf>_<top/bot>`: Semilattice with a join/meet and a top/bottom element (all four
  combinations). Typical examples include `ℕ`.
* `bounded_lattice α`: Lattice with a top and bottom element.
* `distrib_lattice_bot α`: Distributive lattice with a bottom element. It captures the properties
  of `disjoint` that are common to `generalized_boolean_algebra` and `bounded_distrib_lattice`.
* `bounded_distrib_lattice α`: Bounded and distributive lattice. Typical examples include `Prop` and
  `set α`.
* `is_compl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non distributive lattice, an element can have several complements.
* `is_complemented α`: Typeclass stating that any element of a lattice has a complement.

## Implementation notes

We didn't define `distrib_lattice_top` because the dual notion of `disjoint` isn't really used
anywhere.
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

/-- An `order_top` is a partial order with a greatest element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_top (α : Type u) extends has_top α, partial_order α :=
(le_top : ∀ a : α, a ≤ ⊤)

section order_top
variables [order_top α] {a b : α}

@[simp] theorem le_top : a ≤ ⊤ :=
order_top.le_top a

theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
le_top.antisymm h

-- TODO: delete in favor of the next?
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
⟨λ eq, eq.symm ▸ le_refl ⊤, top_unique⟩

@[simp] theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
⟨top_unique, λ h, h.symm ▸ le_refl ⊤⟩

@[simp] theorem not_top_lt : ¬ ⊤ < a :=
λ h, lt_irrefl a (lt_of_le_of_lt le_top h)

theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
top_le_iff.1 $ h₂ ▸ h

lemma lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ := le_top.lt_iff_ne

lemma ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
lt_top_iff_ne_top.1 $ lt_of_lt_of_le h le_top

theorem ne_top_of_le_ne_top {a b : α} (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
λ ha, hb $ top_unique $ ha ▸ hab

lemma eq_top_of_maximal (h : ∀ b, ¬ a < b) : a = ⊤ :=
or.elim (lt_or_eq_of_le le_top) (λ hlt, absurd hlt (h ⊤)) (λ he, he)

lemma ne.lt_top (h : a ≠ ⊤) : a < ⊤ := lt_top_iff_ne_top.mpr h

lemma ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ := h.symm.lt_top

end order_top

lemma strict_mono.top_preimage_top' [linear_order α] [order_top β]
  {f : α → β} (H : strict_mono f) {a} (h_top : f a = ⊤) (x : α) :
  x ≤ a :=
H.top_preimage_top (λ p, by { rw h_top, exact le_top }) x

theorem order_top.ext_top {α} {A B : order_top α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) :
  (by haveI := A; exact ⊤ : α) = ⊤ :=
top_unique $ by rw ← H; apply le_top

theorem order_top.ext {α} {A B : order_top α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  have := partial_order.ext H,
  have tt := order_top.ext_top H,
  casesI A, casesI B,
  injection this; congr'
end

/-- An `order_bot` is a partial order with a least element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_bot (α : Type u) extends has_bot α, partial_order α :=
(bot_le : ∀ a : α, ⊥ ≤ a)

section order_bot
variables [order_bot α] {a b : α}

@[simp] theorem bot_le : ⊥ ≤ a := order_bot.bot_le a

theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
h.antisymm bot_le

-- TODO: delete?
theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
⟨λ eq, eq.symm ▸ le_refl ⊥, bot_unique⟩

@[simp] theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
⟨bot_unique, λ h, h.symm ▸ le_refl ⊥⟩

@[simp] theorem not_lt_bot : ¬ a < ⊥ :=
λ h, lt_irrefl a (lt_of_lt_of_le h bot_le)

theorem ne_bot_of_le_ne_bot {a b : α} (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
λ ha, hb $ bot_unique $ ha ▸ hab

theorem eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
le_bot_iff.1 $ h₂ ▸ h

lemma bot_lt_iff_ne_bot : ⊥ < a ↔ a ≠ ⊥ :=
begin
  haveI := classical.dec_eq α,
  haveI : decidable (a ≤ ⊥) := decidable_of_iff' _ le_bot_iff,
  simp only [lt_iff_le_not_le, not_iff_not.mpr le_bot_iff, true_and, bot_le],
end

lemma ne_bot_of_gt (h : a < b) : b ≠ ⊥ :=
bot_lt_iff_ne_bot.1 $ lt_of_le_of_lt bot_le h

lemma eq_bot_of_minimal (h : ∀ b, ¬ b < a) : a = ⊥ :=
or.elim (lt_or_eq_of_le bot_le) (λ hlt, absurd hlt (h ⊥)) (λ he, he.symm)

lemma ne.bot_lt (h : a ≠ ⊥) : ⊥ < a := bot_lt_iff_ne_bot.mpr h

lemma ne.bot_lt' (h : ⊥ ≠ a) : ⊥ < a := h.symm.bot_lt

end order_bot

lemma strict_mono.bot_preimage_bot' [linear_order α] [order_bot β]
  {f : α → β} (H : strict_mono f) {a} (h_bot : f a = ⊥) (x : α) :
  a ≤ x :=
H.bot_preimage_bot (λ p, by { rw h_bot, exact bot_le }) x

theorem order_bot.ext_bot {α} {A B : order_bot α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) :
  (by haveI := A; exact ⊥ : α) = ⊥ :=
bot_unique $ by rw ← H; apply bot_le

theorem order_bot.ext {α} {A B : order_bot α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  have := partial_order.ext H,
  have tt := order_bot.ext_bot H,
  casesI A, casesI B,
  injection this; congr'
end

/-- A `semilattice_sup_top` is a semilattice with top and join. -/
class semilattice_sup_top (α : Type u) extends order_top α, semilattice_sup α

section semilattice_sup_top
variables [semilattice_sup_top α] {a : α}

@[simp] theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
sup_of_le_left le_top

@[simp] theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
sup_of_le_right le_top

end semilattice_sup_top

/-- A `semilattice_sup_bot` is a semilattice with bottom and join. -/
class semilattice_sup_bot (α : Type u) extends order_bot α, semilattice_sup α

section semilattice_sup_bot
variables [semilattice_sup_bot α] {a b : α}

@[simp] theorem bot_sup_eq : ⊥ ⊔ a = a :=
sup_of_le_right bot_le

@[simp] theorem sup_bot_eq : a ⊔ ⊥ = a :=
sup_of_le_left bot_le

@[simp] theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ (a = ⊥ ∧ b = ⊥) :=
by rw [eq_bot_iff, sup_le_iff]; simp

end semilattice_sup_bot

instance nat.semilattice_sup_bot : semilattice_sup_bot ℕ :=
{ bot := 0, bot_le := nat.zero_le, .. nat.distrib_lattice }

/-- A `semilattice_inf_top` is a semilattice with top and meet. -/
class semilattice_inf_top (α : Type u) extends order_top α, semilattice_inf α

section semilattice_inf_top
variables [semilattice_inf_top α] {a b : α}

@[simp] theorem top_inf_eq : ⊤ ⊓ a = a :=
inf_of_le_right le_top

@[simp] theorem inf_top_eq : a ⊓ ⊤ = a :=
inf_of_le_left le_top

@[simp] theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ (a = ⊤ ∧ b = ⊤) :=
by rw [eq_top_iff, le_inf_iff]; simp

end semilattice_inf_top

/-- A `semilattice_inf_bot` is a semilattice with bottom and meet. -/
class semilattice_inf_bot (α : Type u) extends order_bot α, semilattice_inf α

section semilattice_inf_bot
variables [semilattice_inf_bot α] {a : α}

@[simp] theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
inf_of_le_left bot_le

@[simp] theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
inf_of_le_right bot_le

end semilattice_inf_bot

/-! ### Bounded lattice -/

/-- A bounded lattice is a lattice with a top and bottom element,
  denoted `⊤` and `⊥` respectively. This allows for the interpretation
  of all finite suprema and infima, taking `inf ∅ = ⊤` and `sup ∅ = ⊥`. -/
class bounded_lattice (α : Type u) extends lattice α, order_top α, order_bot α

@[priority 100] -- see Note [lower instance priority]
instance semilattice_inf_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] :
  semilattice_inf_top α :=
{ le_top := λ x, @le_top α _ x, ..bl }

@[priority 100] -- see Note [lower instance priority]
instance semilattice_inf_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] :
  semilattice_inf_bot α :=
{ bot_le := λ x, @bot_le α _ x, ..bl }

@[priority 100] -- see Note [lower instance priority]
instance semilattice_sup_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] :
  semilattice_sup_top α :=
{ le_top := λ x, @le_top α _ x, ..bl }

@[priority 100] -- see Note [lower instance priority]
instance semilattice_sup_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] :
  semilattice_sup_bot α :=
{ bot_le := λ x, @bot_le α _ x, ..bl }

theorem bounded_lattice.ext {α} {A B : bounded_lattice α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  have H1 : @bounded_lattice.to_lattice α A =
             @bounded_lattice.to_lattice α B := lattice.ext H,
  have H2 := order_bot.ext H,
  have H3 : @bounded_lattice.to_order_top α A =
             @bounded_lattice.to_order_top α B := order_top.ext H,
  have tt := order_bot.ext_bot H,
  casesI A, casesI B,
  injection H1; injection H2; injection H3; congr'
end

/-- A `distrib_lattice_bot` is a distributive lattice with a least element. -/
class distrib_lattice_bot α extends distrib_lattice α, semilattice_inf_bot α, semilattice_sup_bot α

/-- A bounded distributive lattice is exactly what it sounds like. -/
class bounded_distrib_lattice α extends distrib_lattice_bot α, bounded_lattice α

lemma inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a b c : α}
  (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c :=
⟨λ h,
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (a ⊓ b) ⊔ (a ⊓ c) : by simp [inf_sup_left]
    ... ≤ c : by simp [h, inf_le_right],
  λ h,
  bot_unique $
    calc a ⊓ b ≤ b ⊓ c : by { rw inf_comm, exact inf_le_inf_left _ h }
      ... = ⊥ : h₂⟩

/-- Propositions form a bounded distributive lattice. -/
instance Prop.bounded_distrib_lattice : bounded_distrib_lattice Prop :=
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
    λ Ha, ⟨H.1.resolve_left Ha, H.2.resolve_left Ha⟩,

  top          := true,
  le_top       := λ a Ha, true.intro,

  bot          := false,
  bot_le       := @false.elim }

noncomputable instance Prop.linear_order : linear_order Prop :=
{ le_total := by intros p q; change (p → q) ∨ (q → p); tauto!,
  decidable_le := classical.dec_rel _,
  .. (_ : partial_order Prop) }

@[simp] lemma le_Prop_eq : ((≤) : Prop → Prop → Prop) = (→) := rfl
@[simp] lemma sup_Prop_eq : (⊔) = (∨) := rfl
@[simp] lemma inf_Prop_eq : (⊓) = (∧) := rfl

section logic
variable [preorder α]

theorem monotone_and {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λ x, p x ∧ q x) :=
λ a b h, and.imp (m_p h) (m_q h)
-- Note: by finish [monotone] doesn't work

theorem monotone_or {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λ x, p x ∨ q x) :=
λ a b h, or.imp (m_p h) (m_q h)
end logic

instance pi.order_bot {α : Type*} {β : α → Type*} [∀ a, order_bot $ β a]  : order_bot (Π a, β a) :=
{ bot := λ _, ⊥,
  bot_le := λ x a, bot_le,
  .. pi.partial_order }

/-! ### Function lattices -/

instance pi.has_sup {ι : Type*} {α : ι → Type*} [Π i, has_sup (α i)] : has_sup (Π i, α i) :=
⟨λ f g i, f i ⊔ g i⟩

@[simp] lemma sup_apply {ι : Type*} {α : ι → Type*} [Π i, has_sup (α i)] (f g : Π i, α i) (i : ι) :
  (f ⊔ g) i = f i ⊔ g i :=
rfl

instance pi.has_inf {ι : Type*} {α : ι → Type*} [Π i, has_inf (α i)] : has_inf (Π i, α i) :=
⟨λ f g i, f i ⊓ g i⟩

@[simp] lemma inf_apply {ι : Type*} {α : ι → Type*} [Π i, has_inf (α i)] (f g : Π i, α i) (i : ι) :
  (f ⊓ g) i = f i ⊓ g i :=
rfl

instance pi.has_bot {ι : Type*} {α : ι → Type*} [Π i, has_bot (α i)] : has_bot (Π i, α i) :=
⟨λ i, ⊥⟩

@[simp] lemma bot_apply {ι : Type*} {α : ι → Type*} [Π i, has_bot (α i)] (i : ι) :
  (⊥ : Π i, α i) i = ⊥ :=
rfl

instance pi.has_top {ι : Type*} {α : ι → Type*} [Π i, has_top (α i)] : has_top (Π i, α i) :=
⟨λ i, ⊤⟩

@[simp] lemma top_apply {ι : Type*} {α : ι → Type*} [Π i, has_top (α i)] (i : ι) :
  (⊤ : Π i, α i) i = ⊤ :=
rfl

instance pi.semilattice_sup {ι : Type*} {α : ι → Type*} [Π i, semilattice_sup (α i)] :
  semilattice_sup (Π i, α i) :=
by refine_struct { sup := (⊔), .. pi.partial_order }; tactic.pi_instance_derive_field

instance pi.semilattice_inf {ι : Type*} {α : ι → Type*} [Π i, semilattice_inf (α i)] :
  semilattice_inf (Π i, α i) :=
by refine_struct { inf := (⊓), .. pi.partial_order }; tactic.pi_instance_derive_field

instance pi.semilattice_inf_bot {ι : Type*} {α : ι → Type*} [Π i, semilattice_inf_bot (α i)] :
  semilattice_inf_bot (Π i, α i) :=
by refine_struct { inf := (⊓), bot := ⊥, .. pi.partial_order }; tactic.pi_instance_derive_field

instance pi.semilattice_inf_top {ι : Type*} {α : ι → Type*} [Π i, semilattice_inf_top (α i)] :
  semilattice_inf_top (Π i, α i) :=
by refine_struct { inf := (⊓), top := ⊤, .. pi.partial_order }; tactic.pi_instance_derive_field

instance pi.semilattice_sup_bot {ι : Type*} {α : ι → Type*} [Π i, semilattice_sup_bot (α i)] :
  semilattice_sup_bot (Π i, α i) :=
by refine_struct { sup := (⊔), bot := ⊥, .. pi.partial_order }; tactic.pi_instance_derive_field

instance pi.semilattice_sup_top {ι : Type*} {α : ι → Type*} [Π i, semilattice_sup_top (α i)] :
  semilattice_sup_top (Π i, α i) :=
by refine_struct { sup := (⊔), top := ⊤, .. pi.partial_order }; tactic.pi_instance_derive_field

instance pi.lattice {ι : Type*} {α : ι → Type*} [Π i, lattice (α i)] : lattice (Π i, α i) :=
{ .. pi.semilattice_sup, .. pi.semilattice_inf }

instance pi.distrib_lattice {ι : Type*} {α : ι → Type*} [Π i, distrib_lattice (α i)] :
  distrib_lattice (Π i, α i) :=
by refine_struct { .. pi.lattice }; tactic.pi_instance_derive_field

instance pi.bounded_lattice {ι : Type*} {α : ι → Type*} [Π i, bounded_lattice (α i)] :
  bounded_lattice (Π i, α i) :=
{ .. pi.semilattice_sup_top, .. pi.semilattice_inf_bot }

instance pi.distrib_lattice_bot {ι : Type*} {α : ι → Type*} [Π i, distrib_lattice_bot (α i)] :
  distrib_lattice_bot (Π i, α i) :=
{ .. pi.distrib_lattice, .. pi.order_bot }

instance pi.bounded_distrib_lattice {ι : Type*} {α : ι → Type*}
  [Π i, bounded_distrib_lattice (α i)] :
  bounded_distrib_lattice (Π i, α i) :=
{ .. pi.bounded_lattice, .. pi.distrib_lattice }

lemma eq_bot_of_bot_eq_top {α : Type*} [bounded_lattice α] (hα : (⊥ : α) = ⊤) (x : α) :
  x = (⊥ : α) :=
eq_bot_mono le_top (eq.symm hα)

lemma eq_top_of_bot_eq_top {α : Type*} [bounded_lattice α] (hα : (⊥ : α) = ⊤) (x : α) :
  x = (⊤ : α) :=
eq_top_mono bot_le hα

lemma subsingleton_of_top_le_bot {α : Type*} [bounded_lattice α] (h : (⊤ : α) ≤ (⊥ : α)) :
  subsingleton α :=
⟨λ a b, le_antisymm (le_trans le_top $ le_trans h bot_le) (le_trans le_top $ le_trans h bot_le)⟩

lemma subsingleton_of_bot_eq_top {α : Type*} [bounded_lattice α] (hα : (⊥ : α) = (⊤ : α)) :
  subsingleton α :=
subsingleton_of_top_le_bot (ge_of_eq hα)

lemma subsingleton_iff_bot_eq_top {α : Type*} [bounded_lattice α] :
  (⊥ : α) = (⊤ : α) ↔ subsingleton α :=
⟨subsingleton_of_bot_eq_top, λ h, by exactI subsingleton.elim ⊥ ⊤⟩

/-! ### `with_bot`, `with_top` -/

/-- Attach `⊥` to a type. -/
def with_bot (α : Type*) := option α

namespace with_bot

meta instance {α} [has_to_format α] : has_to_format (with_bot α) :=
{ to_format := λ x,
  match x with
  | none := "⊥"
  | (some x) := to_fmt x
  end }

instance : has_coe_t α (with_bot α) := ⟨some⟩
instance has_bot : has_bot (with_bot α) := ⟨none⟩

instance : inhabited (with_bot α) := ⟨⊥⟩

lemma none_eq_bot : (none : with_bot α) = (⊥ : with_bot α) := rfl
lemma some_eq_coe (a : α) : (some a : with_bot α) = (↑a : with_bot α) := rfl

@[simp] theorem bot_ne_coe (a : α) : ⊥ ≠ (a : with_bot α) .
@[simp] theorem coe_ne_bot (a : α) : (a : with_bot α) ≠ ⊥ .

/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_eliminator]
def rec_bot_coe {C : with_bot α → Sort*} (h₁ : C ⊥) (h₂ : Π (a : α), C a) :
  Π (n : with_bot α), C n :=
option.rec h₁ h₂

@[norm_cast]
theorem coe_eq_coe {a b : α} : (a : with_bot α) = b ↔ a = b :=
by rw [← option.some.inj_eq a b]; refl

lemma ne_bot_iff_exists {x : with_bot α} : x ≠ ⊥ ↔ ∃ (a : α), ↑a = x :=
option.ne_none_iff_exists

/-- Deconstruct a `x : with_bot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : Π (x : with_bot α), x ≠ ⊥ → α
| ⊥        h := absurd rfl h
| (some x) h := x

@[simp] lemma unbot_coe (x : α) (h : (x : with_bot α) ≠ ⊥ := coe_ne_bot _) :
  (x : with_bot α).unbot h = x := rfl

@[priority 10]
instance has_lt [has_lt α] : has_lt (with_bot α) :=
{ lt := λ o₁ o₂ : option α, ∃ b ∈ o₂, ∀ a ∈ o₁, a < b }

@[simp] theorem some_lt_some [has_lt α] {a b : α} :
  @has_lt.lt (with_bot α) _ (some a) (some b) ↔ a < b :=
by simp [(<)]

lemma bot_lt_some [has_lt α] (a : α) : (⊥ : with_bot α) < some a :=
⟨a, rfl, λ b hb, (option.not_mem_none _ hb).elim⟩

lemma bot_lt_coe [has_lt α] (a : α) : (⊥ : with_bot α) < a := bot_lt_some a

instance : can_lift (with_bot α) α :=
{ coe := coe,
  cond := λ r, r ≠ ⊥,
  prf := λ x hx, ⟨option.get $ option.ne_none_iff_is_some.1 hx, option.some_get _⟩ }

instance [preorder α] : preorder (with_bot α) :=
{ le          := λ o₁ o₂ : option α, ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b,
  lt          := (<),
  lt_iff_le_not_le := by intros; cases a; cases b;
                         simp [lt_iff_le_not_le]; simp [(<)];
                         split; refl,
  le_refl     := λ o a ha, ⟨a, ha, le_refl _⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ a ha,
    let ⟨b, hb, ab⟩ := h₁ a ha, ⟨c, hc, bc⟩ := h₂ b hb in
    ⟨c, hc, le_trans ab bc⟩ }

instance partial_order [partial_order α] : partial_order (with_bot α) :=
{ le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₁ with a,
    { cases o₂ with b, {refl},
      rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩,
      rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end,
  .. with_bot.preorder }

instance order_bot [partial_order α] : order_bot (with_bot α) :=
{ bot_le := λ a a' h, option.no_confusion h,
  ..with_bot.partial_order, ..with_bot.has_bot }

@[simp, norm_cast] theorem coe_le_coe [preorder α] {a b : α} :
  (a : with_bot α) ≤ b ↔ a ≤ b :=
⟨λ h, by rcases h a rfl with ⟨_, ⟨⟩, h⟩; exact h,
 λ h a' e, option.some_inj.1 e ▸ ⟨b, rfl, h⟩⟩

@[simp] theorem some_le_some [preorder α] {a b : α} :
  @has_le.le (with_bot α) _ (some a) (some b) ↔ a ≤ b := coe_le_coe

theorem coe_le [partial_order α] {a b : α} :
  ∀ {o : option α}, b ∈ o → ((a : with_bot α) ≤ o ↔ a ≤ b)
| _ rfl := coe_le_coe

@[norm_cast]
lemma coe_lt_coe [partial_order α] {a b : α} : (a : with_bot α) < b ↔ a < b := some_lt_some

lemma le_coe_get_or_else [preorder α] : ∀ (a : with_bot α) (b : α), a ≤ a.get_or_else b
| (some a) b := le_refl a
| none     b := λ _ h, option.no_confusion h

@[simp] lemma get_or_else_bot (a : α) : option.get_or_else (⊥ : with_bot α) a = a := rfl

lemma get_or_else_bot_le_iff [order_bot α] {a : with_bot α} {b : α} :
  a.get_or_else ⊥ ≤ b ↔ a ≤ b :=
by cases a; simp [none_eq_bot, some_eq_coe]

instance decidable_le [preorder α] [@decidable_rel α (≤)] : @decidable_rel (with_bot α) (≤)
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

instance [partial_order α] [is_total α (≤)] : is_total (with_bot α) (≤) :=
{ total := λ a b, match a, b with
  | none  , _      := or.inl bot_le
  | _     , none   := or.inr bot_le
  | some x, some y := by simp only [some_le_some, total_of]
  end }

instance linear_order [linear_order α] : linear_order (with_bot α) :=
{ le_total := λ o₁ o₂, begin
    cases o₁ with a, {exact or.inl bot_le},
    cases o₂ with b, {exact or.inr bot_le},
    simp [le_total]
  end,
  decidable_le := with_bot.decidable_le,
  decidable_lt := with_bot.decidable_lt,
  ..with_bot.partial_order }

instance semilattice_sup [semilattice_sup α] : semilattice_sup_bot (with_bot α) :=
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
  ..with_bot.order_bot }

lemma coe_sup [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_bot α) = a ⊔ b := rfl

instance semilattice_inf [semilattice_inf α] : semilattice_inf_bot (with_bot α) :=
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
  ..with_bot.order_bot }

lemma coe_inf [semilattice_inf α] (a b : α) : ((a ⊓ b : α) : with_bot α) = a ⊓ b := rfl

instance lattice [lattice α] : lattice (with_bot α) :=
{ ..with_bot.semilattice_sup, ..with_bot.semilattice_inf }

theorem lattice_eq_DLO [linear_order α] :
  lattice_of_linear_order = @with_bot.lattice α _ :=
lattice.ext $ λ x y, iff.rfl

theorem sup_eq_max [linear_order α] (x y : with_bot α) : x ⊔ y = max x y :=
by rw [← sup_eq_max, lattice_eq_DLO]

theorem inf_eq_min [linear_order α] (x y : with_bot α) : x ⊓ y = min x y :=
by rw [← inf_eq_min, lattice_eq_DLO]

@[norm_cast] -- this is not marked simp because the corresponding with_top lemmas are used
lemma coe_min [linear_order α] (x y : α) : ((min x y : α) : with_bot α) = min x y :=
by simp [min, ite_cast]

@[norm_cast] -- this is not marked simp because the corresponding with_top lemmas are used
lemma coe_max [linear_order α] (x y : α) : ((max x y : α) : with_bot α) = max x y :=
by simp [max, ite_cast]

instance order_top [order_top α] : order_top (with_bot α) :=
{ top := some ⊤,
  le_top := λ o a ha, by cases ha; exact ⟨_, rfl, le_top⟩,
  ..with_bot.partial_order }

instance bounded_lattice [bounded_lattice α] : bounded_lattice (with_bot α) :=
{ ..with_bot.lattice, ..with_bot.order_top, ..with_bot.order_bot }

lemma well_founded_lt [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_bot α → with_bot α → Prop) :=
have acc_bot : acc ((<) : with_bot α → with_bot α → Prop) ⊥ :=
  acc.intro _ (λ a ha, (not_le_of_gt ha bot_le).elim),
⟨λ a, option.rec_on a acc_bot (λ a, acc.intro _ (λ b, option.rec_on b (λ _, acc_bot)
(λ b, well_founded.induction h b
  (show ∀ b : α, (∀ c, c < b → (c : with_bot α) < a →
      acc ((<) : with_bot α → with_bot α → Prop) c) → (b : with_bot α) < a →
        acc ((<) : with_bot α → with_bot α → Prop) b,
  from λ b ih hba, acc.intro _ (λ c, option.rec_on c (λ _, acc_bot)
    (λ c hc, ih _ (some_lt_some.1 hc) (lt_trans hc hba)))))))⟩

instance densely_ordered [partial_order α] [densely_ordered α] [no_bot_order α] :
  densely_ordered (with_bot α) :=
⟨ λ a b,
  match a, b with
  | a,      none   := λ h : a < ⊥, (not_lt_bot h).elim
  | none,   some b := λ h, let ⟨a, ha⟩ := no_bot b in ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
  | some a, some b := λ h, let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h) in
    ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩
  end⟩

end with_bot

--TODO(Mario): Construct using order dual on with_bot
/-- Attach `⊤` to a type. -/
def with_top (α : Type*) := option α

namespace with_top

meta instance {α} [has_to_format α] : has_to_format (with_top α) :=
{ to_format := λ x,
  match x with
  | none := "⊤"
  | (some x) := to_fmt x
  end }

instance : has_coe_t α (with_top α) := ⟨some⟩
instance has_top : has_top (with_top α) := ⟨none⟩

instance : inhabited (with_top α) := ⟨⊤⟩

lemma none_eq_top : (none : with_top α) = (⊤ : with_top α) := rfl
lemma some_eq_coe (a : α) : (some a : with_top α) = (↑a : with_top α) := rfl

/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_eliminator]
def rec_top_coe {C : with_top α → Sort*} (h₁ : C ⊤) (h₂ : Π (a : α), C a) :
  Π (n : with_top α), C n :=
option.rec h₁ h₂

@[norm_cast]
theorem coe_eq_coe {a b : α} : (a : with_top α) = b ↔ a = b :=
by rw [← option.some.inj_eq a b]; refl

@[simp] theorem top_ne_coe {a : α} : ⊤ ≠ (a : with_top α) .
@[simp] theorem coe_ne_top {a : α} : (a : with_top α) ≠ ⊤ .

lemma ne_top_iff_exists {x : with_top α} : x ≠ ⊤ ↔ ∃ (a : α), ↑a = x :=
option.ne_none_iff_exists

/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : Π (x : with_top α), x ≠ ⊤ → α :=
with_bot.unbot

@[simp] lemma untop_coe (x : α) (h : (x : with_top α) ≠ ⊤ := coe_ne_top) :
  (x : with_top α).untop h = x := rfl

@[priority 10]
instance has_lt [has_lt α] : has_lt (with_top α) :=
{ lt := λ o₁ o₂ : option α, ∃ b ∈ o₁, ∀ a ∈ o₂, b < a }

@[priority 10]
instance has_le [has_le α] : has_le (with_top α) :=
{ le          := λ o₁ o₂ : option α, ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a }

@[simp] theorem some_lt_some [has_lt α] {a b : α} :
  @has_lt.lt (with_top α) _ (some a) (some b) ↔ a < b :=
by simp [(<)]

@[simp] theorem some_le_some [has_le α] {a b : α} :
  @has_le.le (with_top α) _ (some a) (some b) ↔ a ≤ b :=
by simp [(≤)]

@[simp] theorem le_none [has_le α] {a : with_top α} :
  @has_le.le (with_top α) _ a none :=
by simp [(≤)]

@[simp] theorem some_lt_none [has_lt α] {a : α} :
  @has_lt.lt (with_top α) _ (some a) none :=
by simp [(<)]; existsi a; refl

instance : can_lift (with_top α) α :=
{ coe := coe,
  cond := λ r, r ≠ ⊤,
  prf := λ x hx, ⟨option.get $ option.ne_none_iff_is_some.1 hx, option.some_get _⟩ }

instance [preorder α] : preorder (with_top α) :=
{ le          := λ o₁ o₂ : option α, ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a,
  lt          := (<),
  lt_iff_le_not_le := by { intros; cases a; cases b;
                           simp [lt_iff_le_not_le]; simp [(<),(≤)] },
  le_refl     := λ o a ha, ⟨a, ha, le_refl _⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ c hc,
    let ⟨b, hb, bc⟩ := h₂ c hc, ⟨a, ha, ab⟩ := h₁ b hb in
    ⟨a, ha, le_trans ab bc⟩,
 }

instance partial_order [partial_order α] : partial_order (with_top α) :=
{ le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₂ with b,
    { cases o₁ with a, {refl},
      rcases h₂ a rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ b rfl with ⟨a, ⟨⟩, h₁'⟩,
      rcases h₂ a rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end,
  .. with_top.preorder }

instance order_top [partial_order α] : order_top (with_top α) :=
{ le_top := λ a a' h, option.no_confusion h,
  ..with_top.partial_order, .. with_top.has_top }

@[simp, norm_cast] theorem coe_le_coe [partial_order α] {a b : α} :
  (a : with_top α) ≤ b ↔ a ≤ b :=
⟨λ h, by rcases h b rfl with ⟨_, ⟨⟩, h⟩; exact h,
 λ h a' e, option.some_inj.1 e ▸ ⟨a, rfl, h⟩⟩

theorem le_coe [partial_order α] {a b : α} :
  ∀ {o : option α}, a ∈ o →
  (@has_le.le (with_top α) _ o b ↔ a ≤ b)
| _ rfl := coe_le_coe

theorem le_coe_iff [partial_order α] {b : α} : ∀{x : with_top α}, x ≤ b ↔ (∃a:α, x = a ∧ a ≤ b)
| (some a) := by simp [some_eq_coe, coe_eq_coe]
| none     := by simp [none_eq_top]

theorem coe_le_iff [partial_order α] {a : α} : ∀{x : with_top α}, ↑a ≤ x ↔ (∀b:α, x = ↑b → a ≤ b)
| (some b) := by simp [some_eq_coe, coe_eq_coe]
| none     := by simp [none_eq_top]

theorem lt_iff_exists_coe [partial_order α] : ∀{a b : with_top α}, a < b ↔ (∃p:α, a = p ∧ ↑p < b)
| (some a) b := by simp [some_eq_coe, coe_eq_coe]
| none     b := by simp [none_eq_top]

@[norm_cast]
lemma coe_lt_coe [partial_order α] {a b : α} : (a : with_top α) < b ↔ a < b := some_lt_some

lemma coe_lt_top [partial_order α] (a : α) : (a : with_top α) < ⊤ := some_lt_none

theorem coe_lt_iff [partial_order α] {a : α} : ∀{x : with_top α}, ↑a < x ↔ (∀b:α, x = ↑b → a < b)
| (some b) := by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
| none     := by simp [none_eq_top, coe_lt_top]

lemma not_top_le_coe [partial_order α] (a : α) : ¬ (⊤:with_top α) ≤ ↑a :=
λ h, (lt_irrefl ⊤ (lt_of_le_of_lt h (coe_lt_top a))).elim

instance decidable_le [preorder α] [@decidable_rel α (≤)] : @decidable_rel (with_top α) (≤) :=
λ x y, @with_bot.decidable_le (order_dual α) _ _ y x

instance decidable_lt [has_lt α] [@decidable_rel α (<)] : @decidable_rel (with_top α) (<) :=
λ x y, @with_bot.decidable_lt (order_dual α) _ _ y x

instance [partial_order α] [is_total α (≤)] : is_total (with_top α) (≤) :=
{ total := λ a b, match a, b with
  | none  , _      := or.inr le_top
  | _     , none   := or.inl le_top
  | some x, some y := by simp only [some_le_some, total_of]
  end }

instance linear_order [linear_order α] : linear_order (with_top α) :=
{ le_total := λ o₁ o₂, begin
    cases o₁ with a, {exact or.inr le_top},
    cases o₂ with b, {exact or.inl le_top},
    simp [le_total]
  end,
  decidable_le := with_top.decidable_le,
  decidable_lt := with_top.decidable_lt,
  ..with_top.partial_order }

instance semilattice_inf [semilattice_inf α] : semilattice_inf_top (with_top α) :=
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
  ..with_top.order_top }

lemma coe_inf [semilattice_inf α] (a b : α) : ((a ⊓ b : α) : with_top α) = a ⊓ b := rfl

instance semilattice_sup [semilattice_sup α] : semilattice_sup_top (with_top α) :=
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
  ..with_top.order_top }

lemma coe_sup [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_top α) = a ⊔ b := rfl

instance lattice [lattice α] : lattice (with_top α) :=
{ ..with_top.semilattice_sup, ..with_top.semilattice_inf }

theorem lattice_eq_DLO [linear_order α] :
  lattice_of_linear_order = @with_top.lattice α _ :=
lattice.ext $ λ x y, iff.rfl

theorem sup_eq_max [linear_order α] (x y : with_top α) : x ⊔ y = max x y :=
by rw [← sup_eq_max, lattice_eq_DLO]

theorem inf_eq_min [linear_order α] (x y : with_top α) : x ⊓ y = min x y :=
by rw [← inf_eq_min, lattice_eq_DLO]

@[simp, norm_cast]
lemma coe_min [linear_order α] (x y : α) : ((min x y : α) : with_top α) = min x y :=
by simp [min, ite_cast]

@[simp, norm_cast]
lemma coe_max [linear_order α] (x y : α) : ((max x y : α) : with_top α) = max x y :=
by simp [max, ite_cast]

instance order_bot [order_bot α] : order_bot (with_top α) :=
{ bot := some ⊥,
  bot_le := λ o a ha, by cases ha; exact ⟨_, rfl, bot_le⟩,
  ..with_top.partial_order }

instance bounded_lattice [bounded_lattice α] : bounded_lattice (with_top α) :=
{ ..with_top.lattice, ..with_top.order_top, ..with_top.order_bot }

lemma well_founded_lt {α : Type*} [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_top α → with_top α → Prop) :=
have acc_some : ∀ a : α, acc ((<) : with_top α → with_top α → Prop) (some a) :=
λ a, acc.intro _ (well_founded.induction h a
  (show ∀ b, (∀ c, c < b → ∀ d : with_top α, d < some c → acc (<) d) →
    ∀ y : with_top α, y < some b → acc (<) y,
  from λ b ih c, option.rec_on c (λ hc, (not_lt_of_ge le_top hc).elim)
    (λ c hc, acc.intro _ (ih _ (some_lt_some.1 hc))))),
⟨λ a, option.rec_on a (acc.intro _ (λ y, option.rec_on y (λ h, (lt_irrefl _ h).elim)
  (λ _ _, acc_some _))) acc_some⟩

instance densely_ordered [partial_order α] [densely_ordered α] [no_top_order α] :
  densely_ordered (with_top α) :=
⟨ λ a b,
  match a, b with
  | none,   a   := λ h : ⊤ < a, (not_top_lt h).elim
  | some a, none := λ h, let ⟨b, hb⟩ := no_top a in ⟨b, coe_lt_coe.2 hb, coe_lt_top b⟩
  | some a, some b := λ h, let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h) in
    ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩
  end⟩

lemma lt_iff_exists_coe_btwn [partial_order α] [densely_ordered α] [no_top_order α]
  {a b : with_top α} :
  (a < b) ↔ (∃ x : α, a < ↑x ∧ ↑x < b) :=
⟨λ h, let ⟨y, hy⟩ := exists_between h, ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2 in ⟨x, hx.1 ▸ hy⟩,
 λ ⟨x, hx⟩, lt_trans hx.1 hx.2⟩

end with_top

/-! ### Subtype, order dual, product lattices -/

namespace subtype

/-- A subtype forms a `⊔`-`⊥`-semilattice if `⊥` and `⊔` preserve the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilattice_sup_bot [semilattice_sup_bot α] {P : α → Prop}
  (Pbot : P ⊥) (Psup : ∀⦃x y⦄, P x → P y → P (x ⊔ y)) : semilattice_sup_bot {x : α // P x} :=
{ bot := ⟨⊥, Pbot⟩,
  bot_le := λ x, @bot_le α _ x,
  ..subtype.semilattice_sup Psup }

/-- A subtype forms a `⊓`-`⊥`-semilattice if `⊥` and `⊓` preserve the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilattice_inf_bot [semilattice_inf_bot α] {P : α → Prop}
  (Pbot : P ⊥) (Pinf : ∀⦃x y⦄, P x → P y → P (x ⊓ y)) : semilattice_inf_bot {x : α // P x} :=
{ bot := ⟨⊥, Pbot⟩,
  bot_le := λ x, @bot_le α _ x,
  ..subtype.semilattice_inf Pinf }

/-- A subtype forms a `⊔`-`⊤`-semilattice if `⊤` and `⊔` preserve the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilattice_sup_top [semilattice_sup_top α] {P : α → Prop}
  (Ptop : P ⊤) (Psup : ∀{{x y}}, P x → P y → P (x ⊔ y)) : semilattice_sup_top {x : α // P x} :=
{ top := ⟨⊤, Ptop⟩,
  le_top := λ x, @le_top α _ x,
  ..subtype.semilattice_sup Psup }

/-- A subtype forms a `⊓`-`⊤`-semilattice if `⊤` and `⊓` preserve the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilattice_inf_top [semilattice_inf_top α] {P : α → Prop}
  (Ptop : P ⊤) (Pinf : ∀{{x y}}, P x → P y → P (x ⊓ y)) : semilattice_inf_top {x : α // P x} :=
{ top := ⟨⊤, Ptop⟩,
  le_top := λ x, @le_top α _ x,
  ..subtype.semilattice_inf Pinf }

end subtype

namespace order_dual
variable (α)

instance [has_bot α] : has_top (order_dual α) := ⟨(⊥ : α)⟩
instance [has_top α] : has_bot (order_dual α) := ⟨(⊤ : α)⟩

instance [order_bot α] : order_top (order_dual α) :=
{ le_top := @bot_le α _,
  .. order_dual.partial_order α, .. order_dual.has_top α }

instance [order_top α] : order_bot (order_dual α) :=
{ bot_le := @le_top α _,
  .. order_dual.partial_order α, .. order_dual.has_bot α }

instance [semilattice_inf_bot α] : semilattice_sup_top (order_dual α) :=
{ .. order_dual.semilattice_sup α, .. order_dual.order_top α }

instance [semilattice_inf_top α] : semilattice_sup_bot (order_dual α) :=
{ .. order_dual.semilattice_sup α, .. order_dual.order_bot α }

instance [semilattice_sup_bot α] : semilattice_inf_top (order_dual α) :=
{ .. order_dual.semilattice_inf α, .. order_dual.order_top α }

instance [semilattice_sup_top α] : semilattice_inf_bot (order_dual α) :=
{ .. order_dual.semilattice_inf α, .. order_dual.order_bot α }

instance [bounded_lattice α] : bounded_lattice (order_dual α) :=
{ .. order_dual.lattice α, .. order_dual.order_top α, .. order_dual.order_bot α }

/- If you define `distrib_lattice_top`, add the `order_dual` instances between `distrib_lattice_bot`
and `distrib_lattice_top` here -/

instance [bounded_distrib_lattice α] : bounded_distrib_lattice (order_dual α) :=
{ .. order_dual.bounded_lattice α, .. order_dual.distrib_lattice α }

end order_dual

namespace prod
variables (α β)

instance [has_top α] [has_top β] : has_top (α × β) := ⟨⟨⊤, ⊤⟩⟩
instance [has_bot α] [has_bot β] : has_bot (α × β) := ⟨⟨⊥, ⊥⟩⟩

instance [order_top α] [order_top β] : order_top (α × β) :=
{ le_top := λ a, ⟨le_top, le_top⟩,
  .. prod.partial_order α β, .. prod.has_top α β }

instance [order_bot α] [order_bot β] : order_bot (α × β) :=
{ bot_le := λ a, ⟨bot_le, bot_le⟩,
  .. prod.partial_order α β, .. prod.has_bot α β }

instance [semilattice_sup_top α] [semilattice_sup_top β] : semilattice_sup_top (α × β) :=
{ .. prod.semilattice_sup α β, .. prod.order_top α β }

instance [semilattice_inf_top α] [semilattice_inf_top β] : semilattice_inf_top (α × β) :=
{ .. prod.semilattice_inf α β, .. prod.order_top α β }

instance [semilattice_sup_bot α] [semilattice_sup_bot β] : semilattice_sup_bot (α × β) :=
{ .. prod.semilattice_sup α β, .. prod.order_bot α β }

instance [semilattice_inf_bot α] [semilattice_inf_bot β] : semilattice_inf_bot (α × β) :=
{ .. prod.semilattice_inf α β, .. prod.order_bot α β }

instance [bounded_lattice α] [bounded_lattice β] : bounded_lattice (α × β) :=
{ .. prod.lattice α β, .. prod.order_top α β, .. prod.order_bot α β }

instance [distrib_lattice_bot α] [distrib_lattice_bot β] :
  distrib_lattice_bot (α × β) :=
{ .. prod.distrib_lattice α β, .. prod.order_bot α β }

instance [bounded_distrib_lattice α] [bounded_distrib_lattice β] :
  bounded_distrib_lattice (α × β) :=
{ .. prod.bounded_lattice α β, .. prod.distrib_lattice α β }

end prod

/-! ### Disjointness and complements -/

section disjoint
section semilattice_inf_bot
variable [semilattice_inf_bot α]

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

@[simp] theorem disjoint_bot_left {a : α} : disjoint ⊥ a := inf_le_left
@[simp] theorem disjoint_bot_right {a : α} : disjoint a ⊥ := inf_le_right

theorem disjoint.mono {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
  disjoint b d → disjoint a c := le_trans (inf_le_inf h₁ h₂)

theorem disjoint.mono_left {a b c : α} (h : a ≤ b) : disjoint b c → disjoint a c :=
disjoint.mono h (le_refl _)

theorem disjoint.mono_right {a b c : α} (h : b ≤ c) : disjoint a c → disjoint a b :=
disjoint.mono (le_refl _) h

@[simp] lemma disjoint_self {a : α} : disjoint a a ↔ a = ⊥ :=
by simp [disjoint]

lemma disjoint.ne {a b : α} (ha : a ≠ ⊥) (hab : disjoint a b) : a ≠ b :=
by { intro h, rw [←h, disjoint_self] at hab, exact ha hab }

lemma disjoint.eq_bot_of_le {a b : α} (hab : disjoint a b) (h : a ≤ b) : a = ⊥ :=
eq_bot_iff.2 (by rwa ←inf_eq_left.2 h)

lemma disjoint.of_disjoint_inf_of_le {a b c : α} (h : disjoint (a ⊓ b) c) (hle : a ≤ c) :
  disjoint a b := by rw [disjoint_iff, h.eq_bot_of_le (inf_le_left.trans hle)]

lemma disjoint.of_disjoint_inf_of_le' {a b c : α} (h : disjoint (a ⊓ b) c) (hle : b ≤ c) :
  disjoint a b := by rw [disjoint_iff, h.eq_bot_of_le (inf_le_right.trans hle)]

end semilattice_inf_bot

section bounded_lattice

variables [bounded_lattice α] {a : α}

@[simp] theorem disjoint_top : disjoint a ⊤ ↔ a = ⊥ := by simp [disjoint_iff]
@[simp] theorem top_disjoint : disjoint ⊤ a ↔ a = ⊥ := by simp [disjoint_iff]

lemma eq_bot_of_disjoint_absorbs
  {a b : α} (w : disjoint a b) (h : a ⊔ b = a) : b = ⊥ :=
begin
  rw disjoint_iff at w,
  rw [←w, right_eq_inf],
  rwa sup_eq_left at h,
end

end bounded_lattice

section distrib_lattice_bot
variables [distrib_lattice_bot α] {a b c : α}

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

variables [semilattice_inf_bot α] {a b : α} (c : α)

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

section is_compl

/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
structure is_compl [bounded_lattice α] (x y : α) : Prop :=
(inf_le_bot : x ⊓ y ≤ ⊥)
(top_le_sup : ⊤ ≤ x ⊔ y)

namespace is_compl

section bounded_lattice

variables [bounded_lattice α] {x y z : α}

protected lemma disjoint (h : is_compl x y) : disjoint x y := h.1

@[symm] protected lemma symm (h : is_compl x y) : is_compl y x :=
⟨by { rw inf_comm, exact h.1 }, by { rw sup_comm, exact h.2 }⟩

lemma of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : is_compl x y :=
⟨le_of_eq h₁, le_of_eq h₂.symm⟩

lemma inf_eq_bot (h : is_compl x y) : x ⊓ y = ⊥ := h.disjoint.eq_bot

lemma sup_eq_top (h : is_compl x y) : x ⊔ y = ⊤ := top_unique h.top_le_sup

lemma to_order_dual (h : is_compl x y) : @is_compl (order_dual α) _ x y := ⟨h.2, h.1⟩

end bounded_lattice

variables [bounded_distrib_lattice α] {x y z : α}

lemma inf_left_eq_bot_iff (h : is_compl y z) : x ⊓ y = ⊥ ↔ x ≤ z :=
inf_eq_bot_iff_le_compl h.sup_eq_top h.inf_eq_bot

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

lemma antimono {x' y'} (h : is_compl x y) (h' : is_compl x' y') (hx : x ≤ x') :
  y' ≤ y :=
h'.right_le_iff.2 $ le_trans h.symm.top_le_sup (sup_le_sup_left hx _)

lemma right_unique (hxy : is_compl x y) (hxz : is_compl x z) :
  y = z :=
le_antisymm (hxz.antimono hxy $ le_refl x) (hxy.antimono hxz $ le_refl x)

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

lemma is_compl_bot_top [bounded_lattice α] : is_compl (⊥ : α) ⊤ :=
is_compl.of_eq bot_inf_eq sup_top_eq

lemma is_compl_top_bot [bounded_lattice α] : is_compl (⊤ : α) ⊥ :=
is_compl.of_eq inf_bot_eq top_sup_eq

section
variables [bounded_lattice α] {x : α}

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
class is_complemented (α) [bounded_lattice α] : Prop :=
(exists_is_compl : ∀ (a : α), ∃ (b : α), is_compl a b)

export is_complemented (exists_is_compl)

namespace is_complemented
variables [bounded_lattice α] [is_complemented α]

instance : is_complemented (order_dual α) :=
⟨λ a, let ⟨b, hb⟩ := exists_is_compl (show α, from a) in ⟨b, hb.to_order_dual⟩⟩

end is_complemented

end is_compl

section nontrivial

variables [bounded_lattice α] [nontrivial α]

lemma bot_ne_top : (⊥ : α) ≠ ⊤ :=
λ H, not_nontrivial_iff_subsingleton.mpr (subsingleton_of_bot_eq_top H) ‹_›

lemma top_ne_bot : (⊤ : α) ≠ ⊥ := ne.symm bot_ne_top

end nontrivial

namespace bool

-- Could be generalised to `bounded_distrib_lattice` and `is_complemented`
instance : bounded_lattice bool :=
{ top := tt,
  le_top := λ x, le_tt,
  bot := ff,
  bot_le := λ x, ff_le,
  .. (infer_instance : lattice bool)}

end bool

section bool

@[simp] lemma top_eq_tt : ⊤ = tt := rfl

@[simp] lemma bot_eq_ff : ⊥ = ff := rfl

end bool
