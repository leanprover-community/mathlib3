/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Type class hierarchy for Boolean algebras.
-/
import order.bounded_lattice
import logic.function.basic
set_option old_structure_cmd true

universes u
variables {α : Type u} {w x y z : α}

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A boolean algebra is a bounded distributive lattice with a
  complementation operation `-` such that `x ⊓ - x = ⊥` and `x ⊔ - x = ⊤`.
  This is a generalization of (classical) logic of propositions, or
  the powerset lattice. -/
class boolean_algebra α extends bounded_distrib_lattice α, has_compl α, has_sdiff α :=
(inf_compl_eq_bot : ∀x:α, x ⊓ xᶜ = ⊥)
(sup_compl_eq_top : ∀x:α, x ⊔ xᶜ = ⊤)
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)
end prio

section boolean_algebra
variables [boolean_algebra α]

@[simp] theorem inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
boolean_algebra.inf_compl_eq_bot x

@[simp] theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
eq.trans inf_comm inf_compl_eq_bot

@[simp] theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
boolean_algebra.sup_compl_eq_top x

@[simp] theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ :=
eq.trans sup_comm sup_compl_eq_top

theorem is_compl_compl : is_compl x xᶜ :=
is_compl.of_eq inf_compl_eq_bot sup_compl_eq_top

theorem is_compl.compl_eq (h : is_compl x y) : xᶜ = y :=
(h.right_unique is_compl_compl).symm

theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
boolean_algebra.sdiff_eq x y

theorem compl_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : xᶜ = y :=
(is_compl.of_eq i s).compl_eq

@[simp] theorem compl_top : ⊤ᶜ = (⊥:α) :=
is_compl_top_bot.compl_eq

@[simp] theorem compl_bot : ⊥ᶜ = (⊤:α) :=
is_compl_bot_top.compl_eq

@[simp] theorem compl_compl' : xᶜᶜ = x :=
is_compl_compl.symm.compl_eq

theorem compl_injective : function.injective (compl : α → α) :=
function.involutive.injective $ λ x, compl_compl'

@[simp] theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
compl_injective.eq_iff

@[simp] theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
(is_compl_compl.inf_sup is_compl_compl).compl_eq

@[simp] theorem compl_sup : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ :=
(is_compl_compl.sup_inf is_compl_compl).compl_eq

theorem compl_le_compl (h : y ≤ x) : xᶜ ≤ yᶜ :=
is_compl_compl.antimono is_compl_compl h

theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
⟨assume h, by have h := compl_le_compl h; simp at h; assumption,
  compl_le_compl⟩

theorem le_compl_of_le_compl (h : y ≤ xᶜ) : x ≤ yᶜ :=
by simpa only [compl_compl'] using compl_le_compl h

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y :=
by simpa only [compl_compl'] using compl_le_compl h

theorem compl_le_iff_compl_le : y ≤ xᶜ ↔ x ≤ yᶜ :=
⟨le_compl_of_le_compl, le_compl_of_le_compl⟩

theorem sup_sdiff_same : x ⊔ (y \ x) = x ⊔ y :=
by simp [sdiff_eq, sup_inf_left]

theorem sdiff_eq_left (h : x ⊓ y = ⊥) : x \ y = x :=
by rwa [sdiff_eq, inf_eq_left, is_compl_compl.le_right_iff, disjoint_iff]

theorem sdiff_le_sdiff (h₁ : w ≤ y) (h₂ : z ≤ x) : w \ x ≤ y \ z :=
by rw [sdiff_eq, sdiff_eq]; from inf_le_inf h₁ (compl_le_compl h₂)

end boolean_algebra
