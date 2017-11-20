/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Type class hierarchy for Boolean algebras.
-/
import order.bounded_lattice algebra.functions

set_option old_structure_cmd true

universes u
variables {α : Type u} {x y z w : α}

namespace lattice

class distrib_lattice α extends lattice α :=
(le_sup_inf : ∀x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z))

section distrib_lattice
variables [distrib_lattice α]

theorem le_sup_inf : ∀{x y z : α}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z) :=
distrib_lattice.le_sup_inf

theorem sup_inf_left {x y z : α} : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) :=
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

instance distrib_lattice_of_decidable_linear_order {α : Type u} [o : decidable_linear_order α] : distrib_lattice α :=
{ le_sup_inf := assume a b c, le_of_eq max_min_distrib_left.symm,
  ..lattice.lattice_of_decidable_linear_order }

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


class boolean_algebra α extends bounded_distrib_lattice α, has_neg α, has_sub α :=
(inf_neg_eq_bot : ∀x:α, x ⊓ - x = ⊥)
(sup_neg_eq_top : ∀x:α, x ⊔ - x = ⊤)
(sub_eq : ∀x y:α, x - y = x ⊓ - y)

section boolean_algebra
variables [boolean_algebra α]

@[simp] theorem inf_neg_eq_bot : x ⊓ - x = ⊥ :=
boolean_algebra.inf_neg_eq_bot x

@[simp] theorem neg_inf_eq_bot : - x ⊓ x = ⊥ :=
eq.trans inf_comm inf_neg_eq_bot

@[simp] theorem sup_neg_eq_top : x ⊔ - x = ⊤ :=
boolean_algebra.sup_neg_eq_top x

@[simp] theorem neg_sup_eq_top : - x ⊔ x = ⊤ :=
eq.trans sup_comm sup_neg_eq_top

theorem sub_eq : x - y = x ⊓ - y :=
boolean_algebra.sub_eq x y

theorem neg_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : - x = y :=
have (- x ⊓ x) ⊔ (- x ⊓ y) = (y ⊓ x) ⊔ (y ⊓ - x),
  by rsimp,
have - x ⊓ (x ⊔ y) = y ⊓ (x ⊔ - x),
  begin [smt] eblast_using inf_sup_left end,
by rsimp

@[simp] theorem neg_top : - ⊤ = (⊥:α) :=
neg_unique (by simp) (by simp)

@[simp] theorem neg_bot : - ⊥ = (⊤:α) :=
neg_unique (by simp) (by simp)

@[simp] theorem neg_neg : - (- x) = x :=
neg_unique (by simp) (by simp)

theorem neg_eq_neg_of_eq (h : - x = - y) : x = y :=
have - - x = - - y,
  from congr_arg has_neg.neg h,
by simp [neg_neg] at this; assumption

@[simp] theorem neg_eq_neg_iff : - x = - y ↔ x = y :=
⟨neg_eq_neg_of_eq, congr_arg has_neg.neg⟩

@[simp] theorem neg_inf : - (x ⊓ y) = -x ⊔ -y :=
neg_unique -- TODO: try rsimp if it supports custom lemmas
  (calc (x ⊓ y) ⊓ (- x ⊔ - y) = (y ⊓ (x ⊓ - x)) ⊔ (x ⊓ (y ⊓ - y)) : by rw [inf_sup_left]; ac_refl
                          ... = ⊥ : by simp)
  (calc (x ⊓ y) ⊔ (- x ⊔ - y) = (- y ⊔ (x ⊔ - x)) ⊓ (- x ⊔ (y ⊔ - y)) : by rw [sup_inf_right]; ac_refl
                          ... = ⊤ : by simp)

@[simp] theorem neg_sup : - (x ⊔ y) = -x ⊓ -y :=
begin [smt] eblast_using [neg_neg, neg_inf] end

theorem neg_le_neg (h : y ≤ x) : - x ≤ - y :=
le_of_inf_eq $
  calc -x ⊓ -y = - (x ⊔ y) : neg_sup.symm
           ... = -x        : congr_arg has_neg.neg $ sup_of_le_left h

theorem neg_le_neg_iff_le : - y ≤ - x ↔ x ≤ y :=
⟨assume h, by have h := neg_le_neg h; simp at h; assumption,
  neg_le_neg⟩

theorem le_neg_of_le_neg (h : y ≤ - x) : x ≤ - y :=
have - (- x) ≤ - y, from neg_le_neg h,
by simp at this; assumption

theorem neg_le_of_neg_le (h : - y ≤ x) : - x ≤ y :=
have - x ≤ - (- y), from neg_le_neg h,
by simp at this; assumption

theorem neg_le_iff_neg_le : y ≤ - x ↔ x ≤ - y :=
⟨le_neg_of_le_neg, le_neg_of_le_neg⟩

theorem sup_sub_same : x ⊔ (y - x) = x ⊔ y :=
by simp [sub_eq, sup_inf_left]

theorem sub_eq_left (h : x ⊓ y = ⊥) : x - y = x :=
calc x - y = (x ⊓ -y) ⊔ (x ⊓ y) : by simp [h, sub_eq]
  ... = (-y ⊓ x) ⊔ (y ⊓ x) : by simp [inf_comm]
  ... = (-y ⊔ y) ⊓ x : inf_sup_right.symm
  ... = x : by simp

theorem sub_le_sub (h₁ : w ≤ y) (h₂ : z ≤ x) : w - x ≤ y - z :=
by rw [sub_eq, sub_eq]; from inf_le_inf h₁ (neg_le_neg h₂)

end boolean_algebra

end lattice
