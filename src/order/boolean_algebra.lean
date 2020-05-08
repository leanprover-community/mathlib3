/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Type class hierarchy for Boolean algebras.
-/
import order.bounded_lattice
import logic.function
set_option old_structure_cmd true

universes u
variables {α : Type u} {w x y z : α}

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A boolean algebra is a bounded distributive lattice with a
  complementation operation `-` such that `x ⊓ - x = ⊥` and `x ⊔ - x = ⊤`.
  This is a generalization of (classical) logic of propositions, or
  the powerset lattice. -/
class boolean_algebra α extends bounded_distrib_lattice α, has_neg α, has_sub α :=
(inf_compl_eq_bot : ∀x:α, x ⊓ - x = ⊥)
(sup_compl_eq_top : ∀x:α, x ⊔ - x = ⊤)
(sub_eq : ∀x y:α, x - y = x ⊓ - y)
end prio

section boolean_algebra
variables [boolean_algebra α]

@[simp] theorem inf_compl_eq_bot : x ⊓ - x = ⊥ :=
boolean_algebra.inf_compl_eq_bot x

@[simp] theorem compl_inf_eq_bot : - x ⊓ x = ⊥ :=
eq.trans inf_comm inf_compl_eq_bot

@[simp] theorem sup_compl_eq_top : x ⊔ - x = ⊤ :=
boolean_algebra.sup_compl_eq_top x

@[simp] theorem compl_sup_eq_top : - x ⊔ x = ⊤ :=
eq.trans sup_comm sup_compl_eq_top

theorem is_compl_neg : is_compl x (-x) :=
is_compl.of_eq inf_compl_eq_bot sup_compl_eq_top

theorem is_compl.neg_eq (h : is_compl x y) : -x = y :=
(h.right_unique is_compl_neg).symm

theorem sub_eq : x - y = x ⊓ - y :=
boolean_algebra.sub_eq x y

theorem compl_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : - x = y :=
(is_compl.of_eq i s).neg_eq

@[simp] theorem compl_top : - ⊤ = (⊥:α) :=
is_compl_top_bot.neg_eq

@[simp] theorem compl_bot : - ⊥ = (⊤:α) :=
is_compl_bot_top.neg_eq

@[simp] theorem compl_compl' : - (- x) = x :=
is_compl_neg.symm.neg_eq

theorem compl_inj : function.injective (has_neg.neg : α → α) :=
function.involutive.injective $ λ x, compl_compl'

@[simp] theorem compl_inj_iff : - x = - y ↔ x = y :=
compl_inj.eq_iff

@[simp] theorem compl_inf : - (x ⊓ y) = -x ⊔ -y :=
(is_compl_neg.inf_sup is_compl_neg).neg_eq

@[simp] theorem compl_sup : - (x ⊔ y) = -x ⊓ -y :=
(is_compl_neg.sup_inf is_compl_neg).neg_eq

theorem compl_le_compl (h : y ≤ x) : - x ≤ - y :=
is_compl_neg.antimono is_compl_neg h

theorem compl_le_compl_iff_le : - y ≤ - x ↔ x ≤ y :=
⟨assume h, by have h := compl_le_compl h; simp at h; assumption,
  compl_le_compl⟩

theorem le_compl_of_le_compl (h : y ≤ - x) : x ≤ - y :=
have - (- x) ≤ - y, from compl_le_compl h,
by simp at this; assumption

theorem compl_le_of_compl_le (h : - y ≤ x) : - x ≤ y :=
have - x ≤ - (- y), from compl_le_compl h,
by simp at this; assumption

theorem compl_le_iff_compl_le : y ≤ - x ↔ x ≤ - y :=
⟨le_compl_of_le_compl, le_compl_of_le_compl⟩

theorem sup_sub_same : x ⊔ (y - x) = x ⊔ y :=
by simp [sub_eq, sup_inf_left]

theorem sub_eq_left (h : x ⊓ y = ⊥) : x - y = x :=
by rwa [sub_eq, inf_eq_left, is_compl_neg.le_right_iff, disjoint_iff]

theorem boolean_algebra.sub_le_sub (h₁ : w ≤ y) (h₂ : z ≤ x) : w - x ≤ y - z :=
by rw [sub_eq, sub_eq]; from inf_le_inf h₁ (compl_le_compl h₂)

end boolean_algebra
