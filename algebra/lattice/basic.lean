/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines the inf/sup (semi)-lattice with optionally top/bot type class hierarchy.
-/

import algebra.order tactic.finish
open auto

set_option old_structure_cmd true

universes u v w

-- TODO: move this eventually, if we decide to use them
attribute [ematch] le_trans lt_of_le_of_lt lt_of_lt_of_le lt_trans

section
  variable {α : Type u}

  -- TODO: this seems crazy, but it also seems to work reasonably well
  @[ematch] lemma le_antisymm' [weak_order α] : ∀ {a b : α}, (: a ≤ b :) → b ≤ a → a = b :=
  weak_order.le_antisymm
end

/- TODO: automatic construction of dual definitions / theorems -/
namespace lattice

reserve infixl ` ⊓ `:70
reserve infixl ` ⊔ `:65

class has_top (α : Type u) := (top : α)
class has_bot (α : Type u) := (bot : α)
class has_sup (α : Type u) := (sup : α → α → α)
class has_inf (α : Type u) := (inf : α → α → α)
class has_imp (α : Type u) := (imp : α → α → α) /- Better name -/

infix ⊔ := has_sup.sup
infix ⊓ := has_inf.inf
notation `⊤` := has_top.top _
notation `⊥` := has_bot.bot _

class order_top (α : Type u) extends has_top α, weak_order α :=
(le_top : ∀ a : α, a ≤ ⊤)

section order_top
variables {α : Type u} [order_top α] {a : α}

@[simp] lemma le_top : a ≤ ⊤ :=
order_top.le_top a

lemma top_unique (h : ⊤ ≤ a) : a = ⊤ :=
le_antisymm le_top h

-- TODO: delete in favor of the next?
lemma eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
⟨assume eq, eq^.symm ▸ le_refl ⊤, top_unique⟩

@[simp] lemma top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
⟨top_unique, λ h, h.symm ▸ le_refl ⊤⟩

end order_top

class order_bot (α : Type u) extends has_bot α, weak_order α :=
(bot_le : ∀ a : α, ⊥ ≤ a)

section order_bot
variables {α : Type u} [order_bot α] {a : α}

@[simp] lemma bot_le : ⊥ ≤ a := order_bot.bot_le a

lemma bot_unique (h : a ≤ ⊥) : a = ⊥ :=
le_antisymm h bot_le

-- TODO: delete?
lemma eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
⟨assume eq, eq^.symm ▸ le_refl ⊥, bot_unique⟩

@[simp] lemma le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
⟨bot_unique, assume h, h.symm ▸ le_refl ⊥⟩

lemma neq_bot_of_le_neq_bot {a b : α} (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
assume ha, hb $ bot_unique $ ha ▸ hab

end order_bot

class semilattice_sup (α : Type u) extends has_sup α, weak_order α :=
(le_sup_left : ∀ a b : α, a ≤ a ⊔ b)
(le_sup_right : ∀ a b : α, b ≤ a ⊔ b)
(sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c)

section semilattice_sup
variables {α : Type u} [semilattice_sup α] {a b c d : α}

lemma le_sup_left : a ≤ a ⊔ b :=
semilattice_sup.le_sup_left a b

@[ematch] lemma le_sup_left' : a ≤ (: a ⊔ b :) :=
semilattice_sup.le_sup_left a b

lemma le_sup_right : b ≤ a ⊔ b :=
semilattice_sup.le_sup_right a b

@[ematch] lemma le_sup_right' : b ≤ (: a ⊔ b :) :=
semilattice_sup.le_sup_right a b

lemma le_sup_left_of_le (h : c ≤ a) : c ≤ a ⊔ b :=
by finish

lemma le_sup_right_of_le (h : c ≤ b) : c ≤ a ⊔ b :=
by finish

lemma sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
semilattice_sup.sup_le a b c

@[simp] lemma sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
⟨assume h : a ⊔ b ≤ c, ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
  assume ⟨h₁, h₂⟩, sup_le h₁ h₂⟩

-- TODO: if we just write le_antisymm, Lean doesn't know which ≤ we want to use
-- Can we do anything about that?
lemma sup_of_le_left (h : b ≤ a) : a ⊔ b = a :=
by apply le_antisymm; finish

lemma sup_of_le_right (h : a ≤ b) : a ⊔ b = b :=
by apply le_antisymm; finish

lemma sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
by finish

lemma le_of_sup_eq (h : a ⊔ b = b) : a ≤ b :=
by finish

@[simp] lemma sup_idem : a ⊔ a = a :=
by apply le_antisymm; finish

lemma sup_comm : a ⊔ b = b ⊔ a :=
by apply le_antisymm; finish

instance semilattice_sup_to_is_commutative [semilattice_sup α] : is_commutative α (⊔) :=
⟨@sup_comm _ _⟩

lemma sup_assoc : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
by apply le_antisymm; finish

instance semilattice_sup_to_is_associative [semilattice_sup α] : is_associative α (⊔) :=
⟨@sup_assoc _ _⟩

end semilattice_sup

class semilattice_inf (α : Type u) extends has_inf α, weak_order α :=
(inf_le_left : ∀ a b : α, a ⊓ b ≤ a)
(inf_le_right : ∀ a b : α, a ⊓ b ≤ b)
(le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c)

section semilattice_inf
variables {α : Type u} [semilattice_inf α] {a b c d : α}

lemma inf_le_left : a ⊓ b ≤ a :=
semilattice_inf.inf_le_left a b

@[ematch] lemma inf_le_left' : (: a ⊓ b :) ≤ a :=
semilattice_inf.inf_le_left a b

lemma inf_le_right : a ⊓ b ≤ b :=
semilattice_inf.inf_le_right a b

@[ematch] lemma inf_le_right' : (: a ⊓ b :) ≤ b :=
semilattice_inf.inf_le_right a b

lemma le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
semilattice_inf.le_inf a b c

lemma inf_le_left_of_le (h : a ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_left h

lemma inf_le_right_of_le (h : b ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_right h

@[simp] lemma le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
⟨assume h : a ≤ b ⊓ c, ⟨le_trans h inf_le_left, le_trans h inf_le_right⟩,
  assume ⟨h₁, h₂⟩, le_inf h₁ h₂⟩

lemma inf_of_le_left (h : a ≤ b) : a ⊓ b = a :=
by apply le_antisymm; finish

lemma inf_of_le_right (h : b ≤ a) : a ⊓ b = b :=
by apply le_antisymm; finish

lemma inf_le_inf (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
by finish

lemma le_of_inf_eq (h : a ⊓ b = a) : a ≤ b :=
by finish

@[simp] lemma inf_idem : a ⊓ a = a :=
by apply le_antisymm; finish

lemma inf_comm : a ⊓ b = b ⊓ a :=
by apply le_antisymm; finish

instance semilattice_inf_to_is_commutative [semilattice_inf α] : is_commutative α (⊓) :=
⟨@inf_comm _ _⟩

lemma inf_assoc : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
by apply le_antisymm; finish

instance semilattice_inf_to_is_associative [semilattice_inf α] : is_associative α (⊓) :=
⟨@inf_assoc _ _⟩

end semilattice_inf

class semilattice_sup_top (α : Type u) extends order_top α, semilattice_sup α

section semilattice_sup_top
variables {α : Type u} [semilattice_sup_top α] {a : α}

@[simp] lemma top_sup_eq : ⊤ ⊔ a = ⊤ :=
sup_of_le_left le_top

@[simp] lemma sup_top_eq : a ⊔ ⊤ = ⊤ :=
sup_of_le_right le_top

end semilattice_sup_top

class semilattice_sup_bot (α : Type u) extends order_bot α, semilattice_sup α

section semilattice_sup_bot
variables {α : Type u} [semilattice_sup_bot α] {a b : α}

@[simp] lemma bot_sup_eq : ⊥ ⊔ a = a :=
sup_of_le_right bot_le

@[simp] lemma sup_bot_eq : a ⊔ ⊥ = a :=
sup_of_le_left bot_le

@[simp] lemma sup_eq_bot_iff : a ⊔ b = ⊥ ↔ (a = ⊥ ∧ b = ⊥) :=
by rw [eq_bot_iff, sup_le_iff]; simp

end semilattice_sup_bot

class semilattice_inf_top (α : Type u) extends order_top α, semilattice_inf α

section semilattice_inf_top
variables {α : Type u} [semilattice_inf_top α] {a b : α}

@[simp] lemma top_inf_eq : ⊤ ⊓ a = a :=
inf_of_le_right le_top

@[simp] lemma inf_top_eq : a ⊓ ⊤ = a :=
inf_of_le_left le_top

@[simp] lemma inf_eq_top_iff : a ⊓ b = ⊤ ↔ (a = ⊤ ∧ b = ⊤) :=
by rw [eq_top_iff, le_inf_iff]; simp

end semilattice_inf_top

class semilattice_inf_bot (α : Type u) extends order_bot α, semilattice_inf α

section semilattice_inf_bot
variables {α : Type u} [semilattice_inf_bot α] {a : α}

@[simp] lemma bot_inf_eq : ⊥ ⊓ a = ⊥ :=
inf_of_le_left bot_le

@[simp] lemma inf_bot_eq : a ⊓ ⊥ = ⊥ :=
inf_of_le_right bot_le

end semilattice_inf_bot

/- Lattices -/

class lattice (α : Type u) extends semilattice_sup α, semilattice_inf α

section lattice
variables {α : Type u} [lattice α] {a b c d : α}

/- Distributivity laws -/
/- TODO: better names? -/
lemma sup_inf_le : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
by finish

lemma le_inf_sup : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) :=
by finish

lemma inf_sup_self : a ⊓ (a ⊔ b) = a :=
le_antisymm (by finish) (by finish)

lemma sup_inf_self : a ⊔ (a ⊓ b) = a :=
le_antisymm (by finish) (by finish)

end lattice

/- Lattices derived from linear orders -/

instance lattice_of_decidable_linear_order {α : Type u} [o : decidable_linear_order α] : lattice α :=
{ o with
  sup          := max,
  le_sup_left  := le_max_left,
  le_sup_right := le_max_right,
  sup_le       := assume a b c, max_le,

  inf          := min,
  inf_le_left  := min_le_left,
  inf_le_right := min_le_right,
  le_inf       := assume a b c, le_min }

end lattice
