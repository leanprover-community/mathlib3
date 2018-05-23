/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines bounded lattice type class hierarchy.

Includes the Prop and fun instances.
-/

import order.lattice

set_option old_structure_cmd true

universes u v
variable {α : Type u}

namespace lattice

/-- Typeclass for the `⊤` (`\top`) notation -/
class has_top (α : Type u) := (top : α)
/-- Typeclass for the `⊥` (`\bot`) notation -/
class has_bot (α : Type u) := (bot : α)

notation `⊤` := has_top.top _
notation `⊥` := has_bot.bot _

/-- An `order_top` is a partial order with a maximal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_top (α : Type u) extends has_top α, partial_order α :=
(le_top : ∀ a : α, a ≤ ⊤)

section order_top
variables [order_top α] {a : α}

@[simp] theorem le_top : a ≤ ⊤ :=
order_top.le_top a

theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
le_antisymm le_top h

-- TODO: delete in favor of the next?
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
⟨assume eq, eq.symm ▸ le_refl ⊤, top_unique⟩

@[simp] theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
⟨top_unique, λ h, h.symm ▸ le_refl ⊤⟩

@[simp] theorem not_top_lt : ¬ ⊤ < a :=
assume h, lt_irrefl a (lt_of_le_of_lt le_top h)

end order_top

/-- An `order_bot` is a partial order with a minimal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_bot (α : Type u) extends has_bot α, partial_order α :=
(bot_le : ∀ a : α, ⊥ ≤ a)

section order_bot
variables [order_bot α] {a : α}

@[simp] theorem bot_le : ⊥ ≤ a := order_bot.bot_le a

theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
le_antisymm h bot_le

-- TODO: delete?
theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
⟨assume eq, eq.symm ▸ le_refl ⊥, bot_unique⟩

@[simp] theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
⟨bot_unique, assume h, h.symm ▸ le_refl ⊥⟩

@[simp] theorem not_lt_bot : ¬ a < ⊥ :=
assume h, lt_irrefl a (lt_of_lt_of_le h bot_le)

theorem neq_bot_of_le_neq_bot {a b : α} (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
assume ha, hb $ bot_unique $ ha ▸ hab

end order_bot

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

/- Bounded lattices -/

/-- A bounded lattice is a lattice with a top and bottom element,
  denoted `⊤` and `⊥` respectively. This allows for the interpretation
  of all finite suprema and infima, taking `inf ∅ = ⊤` and `sup ∅ = ⊥`. -/
class bounded_lattice (α : Type u) extends lattice α, order_top α, order_bot α

instance semilattice_inf_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_top α :=
{ le_top := assume x, @le_top α _ x, ..bl }

instance semilattice_inf_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_bot α :=
{ bot_le := assume x, @bot_le α _ x, ..bl }

instance semilattice_sup_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_top α :=
{ le_top := assume x, @le_top α _ x, ..bl }

instance semilattice_sup_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_bot α :=
{ bot_le := assume x, @bot_le α _ x, ..bl }

/-- A bounded distributive lattice is exactly what it sounds like. -/
class bounded_distrib_lattice α extends distrib_lattice α, bounded_lattice α

lemma inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a b c : α}
  (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c :=
⟨assume : a ⊓ b = ⊥,
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (a ⊓ b) ⊔ (a ⊓ c) : by simp [inf_sup_left]
    ... ≤ c : by simp [this, inf_le_right],
  assume : a ≤ c,
  bot_unique $
    calc a ⊓ b ≤ b ⊓ c : by rw [inf_comm]; exact inf_le_inf (le_refl _) this
      ... = ⊥ : h₂⟩

/- Prop instance -/
instance bounded_lattice_Prop : bounded_lattice Prop :=
{ lattice.bounded_lattice .
  le           := λa b, a → b,
  le_refl      := assume _, id,
  le_trans     := assume a b c f g, g ∘ f,
  le_antisymm  := assume a b Hab Hba, propext ⟨Hab, Hba⟩,

  sup          := or,
  le_sup_left  := @or.inl,
  le_sup_right := @or.inr,
  sup_le       := assume a b c, or.rec,

  inf          := and,
  inf_le_left  := @and.left,
  inf_le_right := @and.right,
  le_inf       := assume a b c Hab Hac Ha, and.intro (Hab Ha) (Hac Ha),

  top          := true,
  le_top       := assume a Ha, true.intro,

  bot          := false,
  bot_le       := @false.elim }

section logic
variable [preorder α]

theorem monotone_and {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λx, p x ∧ q x) :=
assume a b h, and.imp (m_p h) (m_q h)
-- Note: by finish [monotone] doesn't work

theorem monotone_or {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λx, p x ∨ q x) :=
assume a b h, or.imp (m_p h) (m_q h)
end logic

/- Function lattices -/

/- TODO:
 * build up the lattice hierarchy for `fun`-functor piecewise. semilattic_*, bounded_lattice, lattice ...
 * can this be generalized to the dependent function space?
-/
instance bounded_lattice_fun {α : Type u} {β : Type v} [bounded_lattice β] :
  bounded_lattice (α → β) :=
{ sup          := λf g a, f a ⊔ g a,
  le_sup_left  := assume f g a, le_sup_left,
  le_sup_right := assume f g a, le_sup_right,
  sup_le       := assume f g h Hfg Hfh a, sup_le (Hfg a) (Hfh a),

  inf          := λf g a, f a ⊓ g a,
  inf_le_left  := assume f g a, inf_le_left,
  inf_le_right := assume f g a, inf_le_right,
  le_inf       := assume f g h Hfg Hfh a, le_inf (Hfg a) (Hfh a),

  top          := λa, ⊤,
  le_top       := assume f a, le_top,

  bot          := λa, ⊥,
  bot_le       := assume f a, bot_le,
  ..partial_order_fun }

end lattice
