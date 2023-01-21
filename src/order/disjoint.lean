/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.bounded_order

/-!
# Disjointness and complements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `disjoint`, `codisjoint`, and the `is_compl` predicate.

## Main declarations

* `disjoint x y`: two elements of a lattice are disjoint if their `inf` is the bottom element.
* `codisjoint x y`: two elements of a lattice are codisjoint if their `join` is the top element.
* `is_compl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non distributive lattice, an element can have several complements.
* `complemented_lattice α`: Typeclass stating that any element of a lattice has a complement.

-/

variable {α : Type*}

section disjoint
section partial_order_bot
variables [partial_order α] [order_bot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.)

Note that we define this without reference to `⊓`, as this allows us to talk about orders where
the infimum is not unique, or where implementing `has_inf` would require additional `decidable`
arguments. -/
def disjoint (a b : α) : Prop := ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥

lemma disjoint.comm : disjoint a b ↔ disjoint b a := forall_congr $ λ _, forall_swap
@[symm] lemma disjoint.symm ⦃a b : α⦄ : disjoint a b → disjoint b a := disjoint.comm.1
lemma symmetric_disjoint : symmetric (disjoint : α → α → Prop) := disjoint.symm

@[simp] lemma disjoint_bot_left : disjoint ⊥ a := λ x hbot ha, hbot
@[simp] lemma disjoint_bot_right : disjoint a ⊥ := λ x ha hbot, hbot

lemma disjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : disjoint b d → disjoint a c :=
λ h x ha hc, h (ha.trans h₁) (hc.trans h₂)

lemma disjoint.mono_left (h : a ≤ b) : disjoint b c → disjoint a c := disjoint.mono h le_rfl
lemma disjoint.mono_right : b ≤ c → disjoint a c → disjoint a b := disjoint.mono le_rfl

@[simp] lemma disjoint_self : disjoint a a ↔ a = ⊥ :=
⟨λ hd, bot_unique $ hd le_rfl le_rfl, λ h x ha hb, ha.trans_eq h⟩

/- TODO: Rename `disjoint.eq_bot` to `disjoint.inf_eq` and `disjoint.eq_bot_of_self` to
`disjoint.eq_bot` -/
alias disjoint_self ↔ disjoint.eq_bot_of_self _

lemma disjoint.ne (ha : a ≠ ⊥) (hab : disjoint a b) : a ≠ b :=
λ h, ha $ disjoint_self.1 $ by rwa ←h at hab

lemma disjoint.eq_bot_of_le (hab : disjoint a b) (h : a ≤ b) : a = ⊥ :=
eq_bot_iff.2 $ hab le_rfl h

lemma disjoint.eq_bot_of_ge (hab : disjoint a b) : b ≤ a → b = ⊥ := hab.symm.eq_bot_of_le

end partial_order_bot

section partial_bounded_order
variables [partial_order α] [bounded_order α] {a : α}

@[simp] theorem disjoint_top : disjoint a ⊤ ↔ a = ⊥ :=
⟨λ h, bot_unique $ h le_rfl le_top, λ h x ha htop, ha.trans_eq h⟩

@[simp] theorem top_disjoint : disjoint ⊤ a ↔ a = ⊥ :=
⟨λ h, bot_unique $ h le_top le_rfl, λ h x htop ha, ha.trans_eq h⟩

end partial_bounded_order

section semilattice_inf_bot
variables [semilattice_inf α] [order_bot α] {a b c d : α}

lemma disjoint_iff_inf_le : disjoint a b ↔ a ⊓ b ≤ ⊥ :=
⟨λ hd, hd inf_le_left inf_le_right, λ h x ha hb, (le_inf ha hb).trans h⟩
lemma disjoint_iff : disjoint a b ↔ a ⊓ b = ⊥ := disjoint_iff_inf_le.trans le_bot_iff
lemma disjoint.le_bot : disjoint a b → a ⊓ b ≤ ⊥ := disjoint_iff_inf_le.mp
lemma disjoint.eq_bot : disjoint a b → a ⊓ b = ⊥ := bot_unique ∘ disjoint.le_bot
lemma disjoint_assoc : disjoint (a ⊓ b) c ↔ disjoint a (b ⊓ c) :=
by rw [disjoint_iff_inf_le, disjoint_iff_inf_le, inf_assoc]
lemma disjoint_left_comm : disjoint a (b ⊓ c) ↔ disjoint b (a ⊓ c) :=
by simp_rw [disjoint_iff_inf_le, inf_left_comm]
lemma disjoint_right_comm : disjoint (a ⊓ b) c ↔ disjoint (a ⊓ c) b :=
by simp_rw [disjoint_iff_inf_le, inf_right_comm]

variables (c)

lemma disjoint.inf_left (h : disjoint a b) : disjoint (a ⊓ c) b := h.mono_left inf_le_left
lemma disjoint.inf_left' (h : disjoint a b) : disjoint (c ⊓ a) b := h.mono_left inf_le_right
lemma disjoint.inf_right (h : disjoint a b) : disjoint a (b ⊓ c) := h.mono_right inf_le_left
lemma disjoint.inf_right' (h : disjoint a b) : disjoint a (c ⊓ b) := h.mono_right inf_le_right

variables {c}

lemma disjoint.of_disjoint_inf_of_le (h : disjoint (a ⊓ b) c) (hle : a ≤ c) : disjoint a b :=
disjoint_iff.2 $ h.eq_bot_of_le $ inf_le_of_left_le hle

lemma disjoint.of_disjoint_inf_of_le' (h : disjoint (a ⊓ b) c) (hle : b ≤ c) : disjoint a b :=
disjoint_iff.2 $ h.eq_bot_of_le $ inf_le_of_right_le hle

end semilattice_inf_bot

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
le_of_inf_le_sup_le (le_trans hd.le_bot bot_le) $ sup_le h le_sup_right

lemma disjoint.left_le_of_le_sup_left (h : a ≤ c ⊔ b) (hd : disjoint a c) : a ≤ b :=
hd.left_le_of_le_sup_right $ by rwa sup_comm

end distrib_lattice_bot
end disjoint

section codisjoint
section partial_order_top
variables [partial_order α] [order_top α] {a b c d : α}

/-- Two elements of a lattice are codisjoint if their sup is the top element.

Note that we define this without reference to `⊔`, as this allows us to talk about orders where
the supremum is not unique, or where implement `has_sup` would require additional `decidable`
arguments. -/
def codisjoint (a b : α) : Prop := ∀ ⦃x⦄, a ≤ x → b ≤ x → ⊤ ≤ x

lemma codisjoint.comm : codisjoint a b ↔ codisjoint b a := forall_congr $ λ _, forall_swap
@[symm] lemma codisjoint.symm ⦃a b : α⦄ : codisjoint a b → codisjoint b a := codisjoint.comm.1
lemma symmetric_codisjoint : symmetric (codisjoint : α → α → Prop) := codisjoint.symm

@[simp] lemma codisjoint_top_left : codisjoint ⊤ a := λ x htop ha, htop
@[simp] lemma codisjoint_top_right : codisjoint a ⊤ := λ x ha htop, htop

lemma codisjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : codisjoint a c → codisjoint b d :=
λ h x ha hc, h (h₁.trans ha) (h₂.trans hc)

lemma codisjoint.mono_left (h : a ≤ b) : codisjoint a c → codisjoint b c :=
codisjoint.mono h le_rfl
lemma codisjoint.mono_right : b ≤ c → codisjoint a b → codisjoint a c :=
codisjoint.mono le_rfl

@[simp] lemma codisjoint_self : codisjoint a a ↔ a = ⊤ :=
⟨λ hd, top_unique $ hd le_rfl le_rfl, λ h x ha hb, h.symm.trans_le ha⟩

/- TODO: Rename `codisjoint.eq_top` to `codisjoint.sup_eq` and `codisjoint.eq_top_of_self` to
`codisjoint.eq_top` -/
alias codisjoint_self ↔ codisjoint.eq_top_of_self _

lemma codisjoint.ne (ha : a ≠ ⊤) (hab : codisjoint a b) : a ≠ b :=
λ h, ha $ codisjoint_self.1 $ by rwa ←h at hab

lemma codisjoint.eq_top_of_le (hab : codisjoint a b) (h : b ≤ a) : a = ⊤ :=
eq_top_iff.2 $ hab le_rfl h

lemma codisjoint.eq_top_of_ge (hab : codisjoint a b) : a ≤ b → b = ⊤ := hab.symm.eq_top_of_le

end partial_order_top

section partial_bounded_order
variables [partial_order α] [bounded_order α] {a : α}

@[simp] theorem codisjoint_bot : codisjoint a ⊥ ↔ a = ⊤ :=
⟨λ h, top_unique $ h le_rfl bot_le, λ h x ha htop, h.symm.trans_le ha⟩

@[simp] theorem bot_codisjoint : codisjoint ⊥ a ↔ a = ⊤ :=
⟨λ h, top_unique $ h bot_le le_rfl, λ h x htop ha, h.symm.trans_le ha⟩

end partial_bounded_order

section semilattice_sup_top
variables [semilattice_sup α] [order_top α] {a b c d : α}

lemma codisjoint_iff_le_sup : codisjoint a b ↔ ⊤ ≤ a ⊔ b := @disjoint_iff_inf_le αᵒᵈ _ _ _ _
lemma codisjoint_iff : codisjoint a b ↔ a ⊔ b = ⊤ := @disjoint_iff αᵒᵈ _ _ _ _
lemma codisjoint.top_le : codisjoint a b → ⊤ ≤ a ⊔ b := @disjoint.le_bot αᵒᵈ _ _ _ _
lemma codisjoint.eq_top : codisjoint a b → a ⊔ b = ⊤ := @disjoint.eq_bot αᵒᵈ _ _ _ _
lemma codisjoint_assoc : codisjoint (a ⊔ b) c ↔ codisjoint a (b ⊔ c) :=
@disjoint_assoc αᵒᵈ _ _ _ _ _
lemma codisjoint_left_comm : codisjoint a (b ⊔ c) ↔ codisjoint b (a ⊔ c) :=
@disjoint_left_comm αᵒᵈ _ _ _ _ _
lemma codisjoint_right_comm : codisjoint (a ⊔ b) c ↔ codisjoint (a ⊔ c) b :=
@disjoint_right_comm αᵒᵈ _ _ _ _ _

variables (c)

lemma codisjoint.sup_left (h : codisjoint a b) : codisjoint (a ⊔ c) b := h.mono_left le_sup_left
lemma codisjoint.sup_left' (h : codisjoint a b) : codisjoint (c ⊔ a) b := h.mono_left le_sup_right
lemma codisjoint.sup_right (h : codisjoint a b) : codisjoint a (b ⊔ c) := h.mono_right le_sup_left
lemma codisjoint.sup_right' (h : codisjoint a b) : codisjoint a (c ⊔ b) := h.mono_right le_sup_right

variables {c}

lemma codisjoint.of_codisjoint_sup_of_le (h : codisjoint (a ⊔ b) c) (hle : c ≤ a) :
  codisjoint a b :=
@disjoint.of_disjoint_inf_of_le αᵒᵈ _ _ _ _ _ h hle

lemma codisjoint.of_codisjoint_sup_of_le' (h : codisjoint (a ⊔ b) c) (hle : c ≤ b) :
  codisjoint a b :=
@disjoint.of_disjoint_inf_of_le' αᵒᵈ _ _ _ _ _ h hle

end semilattice_sup_top

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
@disjoint.left_le_of_le_sup_right αᵒᵈ _ _ _ _ _ h hd.symm

lemma codisjoint.left_le_of_le_inf_left (h : b ⊓ a ≤ c) (hd : codisjoint b c) : a ≤ c :=
hd.left_le_of_le_inf_right $ by rwa inf_comm

end distrib_lattice_top
end codisjoint

open order_dual

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
@[protect_proj] structure is_compl [partial_order α] [bounded_order α] (x y : α) : Prop :=
(disjoint : disjoint x y)
(codisjoint : codisjoint x y)

lemma is_compl_iff [partial_order α] [bounded_order α] {a b : α} :
  is_compl a b ↔ disjoint a b ∧ codisjoint a b := ⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

namespace is_compl

section bounded_partial_order
variables [partial_order α] [bounded_order α] {x y z : α}

@[symm] protected lemma symm (h : is_compl x y) : is_compl y x := ⟨h.1.symm, h.2.symm⟩

lemma dual (h : is_compl x y) : is_compl (to_dual x) (to_dual y) := ⟨h.2, h.1⟩
lemma of_dual {a b : αᵒᵈ} (h : is_compl a b) : is_compl (of_dual a) (of_dual b) := ⟨h.2, h.1⟩

end bounded_partial_order

section bounded_lattice
variables [lattice α] [bounded_order α] {x y z : α}

lemma of_le (h₁ : x ⊓ y ≤ ⊥) (h₂ : ⊤ ≤ x ⊔ y) : is_compl x y :=
⟨disjoint_iff_inf_le.mpr h₁, codisjoint_iff_le_sup.mpr h₂⟩

lemma of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : is_compl x y :=
⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr h₂⟩

lemma inf_eq_bot (h : is_compl x y) : x ⊓ y = ⊥ := h.disjoint.eq_bot
lemma sup_eq_top (h : is_compl x y) : x ⊔ y = ⊤ := h.codisjoint.eq_top

end bounded_lattice

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

lemma left_le_iff (h : is_compl x y) : x ≤ z ↔ codisjoint z y := h.dual.le_left_iff

lemma right_le_iff (h : is_compl x y) : y ≤ z ↔ codisjoint z x := h.symm.left_le_iff

protected lemma antitone {x' y'} (h : is_compl x y) (h' : is_compl x' y') (hx : x ≤ x') :
  y' ≤ y :=
h'.right_le_iff.2 $ h.symm.codisjoint.mono_right hx

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

namespace prod
variables {β : Type*} [partial_order α] [partial_order β]

protected lemma disjoint_iff [order_bot α] [order_bot β] {x y : α × β} :
  disjoint x y ↔ disjoint x.1 y.1 ∧ disjoint x.2 y.2 :=
begin
  split,
  { intros h,
    refine ⟨λ a hx hy, (@h (a, ⊥) ⟨hx, _⟩ ⟨hy, _⟩).1, λ b hx hy, (@h (⊥, b) ⟨_, hx⟩ ⟨_, hy⟩).2⟩,
    all_goals { exact bot_le }, },
  { rintros ⟨ha, hb⟩ z hza hzb,
    refine ⟨ha hza.1 hzb.1, hb hza.2 hzb.2⟩ },
end

protected lemma codisjoint_iff [order_top α] [order_top β] {x y : α × β} :
  codisjoint x y ↔ codisjoint x.1 y.1 ∧ codisjoint x.2 y.2 :=
@prod.disjoint_iff αᵒᵈ βᵒᵈ _ _ _ _ _ _

protected lemma is_compl_iff [bounded_order α] [bounded_order β]
  {x y : α × β} :
  is_compl x y ↔ is_compl x.1 y.1 ∧ is_compl x.2 y.2 :=
by simp_rw [is_compl_iff, prod.disjoint_iff, prod.codisjoint_iff, and_and_and_comm]

end prod

section
variables [lattice α] [bounded_order α] {a b x : α}

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

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
class complemented_lattice (α) [lattice α] [bounded_order α] : Prop :=
(exists_is_compl : ∀ (a : α), ∃ (b : α), is_compl a b)

export complemented_lattice (exists_is_compl)

namespace complemented_lattice
variables [lattice α] [bounded_order α] [complemented_lattice α]

instance : complemented_lattice αᵒᵈ :=
⟨λ a, let ⟨b, hb⟩ := exists_is_compl (show α, from a) in ⟨b, hb.dual⟩⟩

end complemented_lattice

end is_compl
