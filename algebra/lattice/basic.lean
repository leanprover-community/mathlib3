/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines the inf/sup (semi)-lattice with optionally top/bot type class hierarchy.
-/

import algebra.order

set_option old_structure_cmd true

universes u v w

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

lemma le_top : a ≤ ⊤ :=
order_top.le_top a

lemma top_unique (h : ⊤ ≤ a) : a = ⊤ :=
le_antisymm le_top h

lemma eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
⟨assume eq, eq^.symm ▸ le_refl ⊤, top_unique⟩

end order_top

class order_bot (α : Type u) extends has_bot α, weak_order α :=
(bot_le : ∀ a : α, ⊥ ≤ a)

section order_bot
variables {α : Type u} [order_bot α] {a : α}

lemma bot_le : ⊥ ≤ a := order_bot.bot_le a

lemma bot_unique (h : a ≤ ⊥) : a = ⊥ :=
le_antisymm h bot_le

lemma eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
⟨assume eq, eq^.symm ▸ le_refl ⊥, bot_unique⟩

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

lemma le_sup_right : b ≤ a ⊔ b :=
semilattice_sup.le_sup_right a b

lemma sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
semilattice_sup.sup_le a b c

lemma le_sup_left_of_le (h : c ≤ a) : c ≤ a ⊔ b :=
le_trans h le_sup_left

lemma le_sup_right_of_le (h : c ≤ b) : c ≤ a ⊔ b :=
le_trans h le_sup_right

lemma sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
⟨assume h : a ⊔ b ≤ c, ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
  assume ⟨h₁, h₂⟩, sup_le h₁ h₂⟩

lemma sup_of_le_left (h : b ≤ a) : a ⊔ b = a :=
le_antisymm (sup_le (le_refl _) h) le_sup_left

lemma sup_of_le_right (h : a ≤ b) : a ⊔ b = b :=
le_antisymm (sup_le h (le_refl _)) le_sup_right

lemma sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
sup_le (le_sup_left_of_le h₁) (le_sup_right_of_le h₂)

lemma le_of_sup_eq (h : a ⊔ b = b) : a ≤ b :=
h ▸ le_sup_left

@[simp]
lemma sup_idem : a ⊔ a = a :=
sup_of_le_left (le_refl _)

lemma sup_comm : a ⊔ b = b ⊔ a :=
have ∀{a b : α}, a ⊔ b ≤ b ⊔ a, 
  from assume a b, sup_le le_sup_right le_sup_left,
le_antisymm this this

instance semilattice_sup_to_is_commutative [semilattice_sup α] : is_commutative α (⊔) :=
⟨@sup_comm _ _⟩

lemma sup_assoc : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
le_antisymm
  (sup_le (sup_le le_sup_left (le_sup_right_of_le le_sup_left)) (le_sup_right_of_le le_sup_right))
  (sup_le (le_sup_left_of_le le_sup_left) (sup_le (le_sup_left_of_le le_sup_right) le_sup_right))

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

lemma inf_le_right : a ⊓ b ≤ b :=
semilattice_inf.inf_le_right a b

lemma le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
semilattice_inf.le_inf a b c

lemma inf_le_left_of_le (h : a ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_left h

lemma inf_le_right_of_le (h : b ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_right h

lemma le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
⟨assume h : a ≤ b ⊓ c, ⟨le_trans h inf_le_left, le_trans h inf_le_right⟩,
  assume ⟨h₁, h₂⟩, le_inf h₁ h₂⟩

lemma inf_of_le_left (h : a ≤ b) : a ⊓ b = a :=
le_antisymm inf_le_left (le_inf (le_refl _) h)

lemma inf_of_le_right (h : b ≤ a) : a ⊓ b = b :=
le_antisymm inf_le_right (le_inf h (le_refl _))

lemma inf_le_inf (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
le_inf (inf_le_left_of_le h₁) (inf_le_right_of_le h₂)

lemma le_of_inf_eq (h : a ⊓ b = a) : a ≤ b :=
h ▸ inf_le_right

@[simp]
lemma inf_idem : a ⊓ a = a :=
inf_of_le_left (le_refl _)

lemma inf_comm : a ⊓ b = b ⊓ a :=
have ∀{a b : α}, a ⊓ b ≤ b ⊓ a, 
  from assume a b, le_inf inf_le_right inf_le_left,
le_antisymm this this

instance semilattice_inf_to_is_commutative [semilattice_inf α] : is_commutative α (⊓) :=
⟨@inf_comm _ _⟩

lemma inf_assoc : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
le_antisymm
  (le_inf (inf_le_left_of_le inf_le_left) (le_inf (inf_le_left_of_le inf_le_right) inf_le_right))
  (le_inf (le_inf inf_le_left (inf_le_right_of_le inf_le_left)) (inf_le_right_of_le inf_le_right))

instance semilattice_inf_to_is_associative [semilattice_inf α] : is_associative α (⊓) :=
⟨@inf_assoc _ _⟩

end semilattice_inf

class semilattice_sup_top (α : Type u) extends order_top α, semilattice_sup α

section semilattice_sup_top
variables {α : Type u} [semilattice_sup_top α] {a : α}

@[simp]
lemma top_sup_eq : ⊤ ⊔ a = ⊤ := 
sup_of_le_left le_top

@[simp]
lemma sup_top_eq : a ⊔ ⊤ = ⊤ := 
sup_of_le_right le_top

end semilattice_sup_top

class semilattice_sup_bot (α : Type u) extends order_bot α, semilattice_sup α

section semilattice_sup_bot
variables {α : Type u} [semilattice_sup_bot α] {a b : α}

@[simp]
lemma bot_sup_eq : ⊥ ⊔ a = a := 
sup_of_le_right bot_le

@[simp]
lemma sup_bot_eq : a ⊔ ⊥ = a := 
sup_of_le_left bot_le

@[simp]
lemma sup_eq_bot_iff : a ⊔ b = ⊥ ↔ (a = ⊥ ∧ b = ⊥) :=
by simp [eq_bot_iff, sup_le_iff]

end semilattice_sup_bot

class semilattice_inf_top (α : Type u) extends order_top α, semilattice_inf α

section semilattice_inf_top
variables {α : Type u} [semilattice_inf_top α] {a b : α}

@[simp]
lemma top_inf_eq : ⊤ ⊓ a = a := 
inf_of_le_right le_top

@[simp]
lemma inf_top_eq : a ⊓ ⊤ = a := 
inf_of_le_left le_top

@[simp]
lemma inf_eq_top_iff : a ⊓ b = ⊤ ↔ (a = ⊤ ∧ b = ⊤) :=
by simp [eq_top_iff, le_inf_iff]

end semilattice_inf_top

class semilattice_inf_bot (α : Type u) extends order_bot α, semilattice_inf α

section semilattice_inf_bot
variables {α : Type u} [semilattice_inf_bot α] {a : α}

@[simp]
lemma bot_inf_eq : ⊥ ⊓ a = ⊥ := 
inf_of_le_left bot_le

@[simp]
lemma inf_bot_eq : a ⊓ ⊥ = ⊥ := 
inf_of_le_right bot_le

end semilattice_inf_bot

/- Lattices -/

class lattice (α : Type u) extends semilattice_sup α, semilattice_inf α

section lattice
variables {α : Type u} [lattice α] {a b c d : α}

/- Distributivity laws -/
/- TODO: better names? -/
lemma sup_inf_le : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
sup_le (le_inf le_sup_left le_sup_left) $
  le_inf (inf_le_left_of_le le_sup_right) (inf_le_right_of_le le_sup_right)

lemma le_inf_sup : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) :=
le_inf (sup_le inf_le_left inf_le_left) $
  sup_le (le_sup_left_of_le inf_le_right) (le_sup_right_of_le inf_le_right)

lemma inf_sup_self : a ⊓ (a ⊔ b) = a :=
le_antisymm inf_le_left (le_inf (le_refl a) le_sup_left)

lemma sup_inf_self : a ⊔ (a ⊓ b) = a :=
le_antisymm (sup_le (le_refl a) inf_le_left) le_sup_left

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
