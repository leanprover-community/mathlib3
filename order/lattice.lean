/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines the inf/sup (semi)-lattice with optionally top/bot type class hierarchy.
-/

import order.basic tactic.finish
open auto

set_option old_structure_cmd true

universes u v w

-- TODO: move this eventually, if we decide to use them
attribute [ematch] le_trans lt_of_le_of_lt lt_of_lt_of_le lt_trans

section
  variable {α : Type u}

  -- TODO: this seems crazy, but it also seems to work reasonably well
  @[ematch] theorem le_antisymm' [partial_order α] : ∀ {a b : α}, (: a ≤ b :) → b ≤ a → a = b :=
  @le_antisymm _ _
end

/- TODO: automatic construction of dual definitions / theorems -/
namespace lattice

reserve infixl ` ⊓ `:70
reserve infixl ` ⊔ `:65

/-- Typeclass for the `⊤` (`\top`) notation -/
class has_top (α : Type u) := (top : α)
/-- Typeclass for the `⊥` (`\bot`) notation -/
class has_bot (α : Type u) := (bot : α)
/-- Typeclass for the `⊔` (`\lub`) notation -/
class has_sup (α : Type u) := (sup : α → α → α)
/-- Typeclass for the `⊓` (`\glb`) notation -/
class has_inf (α : Type u) := (inf : α → α → α)

infix ⊔ := has_sup.sup
infix ⊓ := has_inf.inf
notation `⊤` := has_top.top _
notation `⊥` := has_bot.bot _

/-- An `order_top` is a partial order with a maximal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_top (α : Type u) extends has_top α, partial_order α :=
(le_top : ∀ a : α, a ≤ ⊤)

section order_top
variables {α : Type u} [order_top α] {a : α}

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
variables {α : Type u} [order_bot α] {a : α}

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

/-- A `semilattice_sup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class semilattice_sup (α : Type u) extends has_sup α, partial_order α :=
(le_sup_left : ∀ a b : α, a ≤ a ⊔ b)
(le_sup_right : ∀ a b : α, b ≤ a ⊔ b)
(sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c)

section semilattice_sup
variables {α : Type u} [semilattice_sup α] {a b c d : α}

@[simp] theorem le_sup_left : a ≤ a ⊔ b :=
semilattice_sup.le_sup_left a b

@[ematch] theorem le_sup_left' : a ≤ (: a ⊔ b :) :=
semilattice_sup.le_sup_left a b

@[simp] theorem le_sup_right : b ≤ a ⊔ b :=
semilattice_sup.le_sup_right a b

@[ematch] theorem le_sup_right' : b ≤ (: a ⊔ b :) :=
semilattice_sup.le_sup_right a b

theorem le_sup_left_of_le (h : c ≤ a) : c ≤ a ⊔ b :=
by finish

theorem le_sup_right_of_le (h : c ≤ b) : c ≤ a ⊔ b :=
by finish

theorem sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
semilattice_sup.sup_le a b c

@[simp] theorem sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
⟨assume h : a ⊔ b ≤ c, ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
  assume ⟨h₁, h₂⟩, sup_le h₁ h₂⟩

-- TODO: if we just write le_antisymm, Lean doesn't know which ≤ we want to use
-- Can we do anything about that?
theorem sup_of_le_left (h : b ≤ a) : a ⊔ b = a :=
by apply le_antisymm; finish

theorem sup_of_le_right (h : a ≤ b) : a ⊔ b = b :=
by apply le_antisymm; finish

theorem sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
by finish

theorem sup_le_sup_left (h₁ : a ≤ b) (c) : c ⊔ a ≤ c ⊔ b :=
by finish

theorem sup_le_sup_right (h₁ : a ≤ b) (c) : a ⊔ c ≤ b ⊔ c :=
by finish

theorem le_of_sup_eq (h : a ⊔ b = b) : a ≤ b :=
by finish

@[simp] theorem sup_idem : a ⊔ a = a :=
by apply le_antisymm; finish

theorem sup_comm : a ⊔ b = b ⊔ a :=
by apply le_antisymm; finish

instance semilattice_sup_to_is_commutative : is_commutative α (⊔) :=
⟨@sup_comm _ _⟩

theorem sup_assoc : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
by apply le_antisymm; finish

instance semilattice_sup_to_is_associative : is_associative α (⊔) :=
⟨@sup_assoc _ _⟩

lemma forall_le_or_exists_lt_sup (a : α) : (∀b, b ≤ a) ∨ (∃b, a < b) :=
suffices (∃b, ¬b ≤ a) → (∃b, a < b),
  by rwa [classical.or_iff_not_imp_left, classical.not_forall],
assume ⟨b, hb⟩,
have a ≠ a ⊔ b, from assume eq, hb $ eq.symm ▸ le_sup_right,
⟨a ⊔ b, lt_of_le_of_ne le_sup_left ‹a ≠ a ⊔ b›⟩

end semilattice_sup

/-- A `semilattice_sup` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
class semilattice_inf (α : Type u) extends has_inf α, partial_order α :=
(inf_le_left : ∀ a b : α, a ⊓ b ≤ a)
(inf_le_right : ∀ a b : α, a ⊓ b ≤ b)
(le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c)

section semilattice_inf
variables {α : Type u} [semilattice_inf α] {a b c d : α}

@[simp] theorem inf_le_left : a ⊓ b ≤ a :=
semilattice_inf.inf_le_left a b

@[ematch] theorem inf_le_left' : (: a ⊓ b :) ≤ a :=
semilattice_inf.inf_le_left a b

@[simp] theorem inf_le_right : a ⊓ b ≤ b :=
semilattice_inf.inf_le_right a b

@[ematch] theorem inf_le_right' : (: a ⊓ b :) ≤ b :=
semilattice_inf.inf_le_right a b

theorem le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
semilattice_inf.le_inf a b c

theorem inf_le_left_of_le (h : a ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_left h

theorem inf_le_right_of_le (h : b ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_right h

@[simp] theorem le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
⟨assume h : a ≤ b ⊓ c, ⟨le_trans h inf_le_left, le_trans h inf_le_right⟩,
  assume ⟨h₁, h₂⟩, le_inf h₁ h₂⟩

theorem inf_of_le_left (h : a ≤ b) : a ⊓ b = a :=
by apply le_antisymm; finish

theorem inf_of_le_right (h : b ≤ a) : a ⊓ b = b :=
by apply le_antisymm; finish

theorem inf_le_inf (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
by finish

theorem le_of_inf_eq (h : a ⊓ b = a) : a ≤ b :=
by finish

@[simp] theorem inf_idem : a ⊓ a = a :=
by apply le_antisymm; finish

theorem inf_comm : a ⊓ b = b ⊓ a :=
by apply le_antisymm; finish

instance semilattice_inf_to_is_commutative : is_commutative α (⊓) :=
⟨@inf_comm _ _⟩

theorem inf_assoc : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
by apply le_antisymm; finish

instance semilattice_inf_to_is_associative : is_associative α (⊓) :=
⟨@inf_assoc _ _⟩

lemma forall_le_or_exists_lt_inf (a : α) : (∀b, a ≤ b) ∨ (∃b, b < a) :=
suffices (∃b, ¬a ≤ b) → (∃b, b < a),
  by rwa [classical.or_iff_not_imp_left, classical.not_forall],
assume ⟨b, hb⟩,
have a ⊓ b ≠ a, from assume eq, hb $ eq ▸ inf_le_right,
⟨a ⊓ b, lt_of_le_of_ne inf_le_left ‹a ⊓ b ≠ a›⟩

end semilattice_inf

/-- A `semilattice_sup_top` is a semilattice with top and join. -/
class semilattice_sup_top (α : Type u) extends order_top α, semilattice_sup α

section semilattice_sup_top
variables {α : Type u} [semilattice_sup_top α] {a : α}

@[simp] theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
sup_of_le_left le_top

@[simp] theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
sup_of_le_right le_top

end semilattice_sup_top

/-- A `semilattice_sup_bot` is a semilattice with bottom and join. -/
class semilattice_sup_bot (α : Type u) extends order_bot α, semilattice_sup α

section semilattice_sup_bot
variables {α : Type u} [semilattice_sup_bot α] {a b : α}

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
variables {α : Type u} [semilattice_inf_top α] {a b : α}

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
variables {α : Type u} [semilattice_inf_bot α] {a : α}

@[simp] theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
inf_of_le_left bot_le

@[simp] theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
inf_of_le_right bot_le

end semilattice_inf_bot

/- Lattices -/

/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
class lattice (α : Type u) extends semilattice_sup α, semilattice_inf α

section lattice
variables {α : Type u} [lattice α] {a b c d : α}

/- Distributivity laws -/
/- TODO: better names? -/
theorem sup_inf_le : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
by finish

theorem le_inf_sup : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) :=
by finish

theorem inf_sup_self : a ⊓ (a ⊔ b) = a :=
le_antisymm (by finish) (by finish)

theorem sup_inf_self : a ⊔ (a ⊓ b) = a :=
le_antisymm (by finish) (by finish)

end lattice

variables {α : Type u} {x y z w : α}

/-- A distributive lattice is a lattice that satisfies any of four
  equivalent distribution properties (of sup over inf or inf over sup,
  on the left or right). A classic example of a distributive lattice
  is the lattice of subsets of a set, and in fact this example is
  generic in the sense that every distributive lattice is realizable
  as a sublattice of a powerset lattice. -/
class distrib_lattice α extends lattice α :=
(le_sup_inf : ∀x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z))

section distrib_lattice
variables [distrib_lattice α]

theorem le_sup_inf : ∀{x y z : α}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z) :=
distrib_lattice.le_sup_inf

theorem sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) :=
le_antisymm sup_inf_le le_sup_inf

theorem sup_inf_right : (y ⊓ z) ⊔ x = (y ⊔ x) ⊓ (z ⊔ x) :=
by simp [sup_inf_left, λy:α, @sup_comm α _ y x]

theorem inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) :=
calc x ⊓ (y ⊔ z) = (x ⊓ (x ⊔ z)) ⊓ (y ⊔ z)       : by rw [inf_sup_self]
             ... = x ⊓ ((x ⊓ y) ⊔ z)             : by simp [inf_assoc, sup_inf_right]
             ... = (x ⊔ (x ⊓ y)) ⊓ ((x ⊓ y) ⊔ z) : by rw [sup_inf_self]
             ... = ((x ⊓ y) ⊔ x) ⊓ ((x ⊓ y) ⊔ z) : by rw [sup_comm]
             ... = (x ⊓ y) ⊔ (x ⊓ z)             : by rw [sup_inf_left]

theorem inf_sup_right : (y ⊔ z) ⊓ x = (y ⊓ x) ⊔ (z ⊓ x) :=
by simp [inf_sup_left, λy:α, @inf_comm α _ y x]

lemma eq_of_sup_eq_inf_eq {α : Type u} [distrib_lattice α] {a b c : α}
  (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
le_antisymm
  (calc b ≤ (c ⊓ a) ⊔ b     : le_sup_right
    ... = (c ⊔ b) ⊓ (a ⊔ b) : sup_inf_right
    ... = c ⊔ (c ⊓ a)       : by rw [←h₁, sup_inf_left, ←h₂]; simp [sup_comm]
    ... = c                 : sup_inf_self)
  (calc c ≤ (b ⊓ a) ⊔ c     : le_sup_right
    ... = (b ⊔ c) ⊓ (a ⊔ c) : sup_inf_right
    ... = b ⊔ (b ⊓ a)       : by rw [h₁, sup_inf_left, h₂]; simp [sup_comm]
    ... = b                 : sup_inf_self)

end distrib_lattice

/- Lattices derived from linear orders -/

instance lattice_of_decidable_linear_order {α : Type u} [o : decidable_linear_order α] : lattice α :=
{ sup          := max,
  le_sup_left  := le_max_left,
  le_sup_right := le_max_right,
  sup_le       := assume a b c, max_le,

  inf          := min,
  inf_le_left  := min_le_left,
  inf_le_right := min_le_right,
  le_inf       := assume a b c, le_min,
  ..o }


instance distrib_lattice_of_decidable_linear_order {α : Type u} [o : decidable_linear_order α] : distrib_lattice α :=
{ le_sup_inf := assume a b c,
    match le_total b c with
    | or.inl h := inf_le_left_of_le $ sup_le_sup_left (le_inf (le_refl b) h) _
    | or.inr h := inf_le_right_of_le $ sup_le_sup_left (le_inf h (le_refl c)) _
    end,
  ..lattice.lattice_of_decidable_linear_order }

end lattice
