/-
Copyright (c) 2021 Yaël Dillies, Kendall Frey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kendall Frey
-/
import data.set.basic

class has_btw (α : Type*) :=
(btw : α → α → α → Prop)

export has_btw (btw)

class has_sbtw (α : Type*) :=
(sbtw : α → α → α → Prop)

export has_sbtw (sbtw)

/-alias lt_of_le_of_lt  ← has_le.le.trans_lt
alias btw_antisymm     ← has_btw.btw.antisymm
alias lt_of_le_of_ne  ← has_le.le.lt_of_ne
alias lt_of_le_not_le ← has_le.le.lt_of_not_le
alias lt_or_eq_of_le  ← has_le.le.lt_or_eq-/

/-! ### Circular preorders -/

class circular_preorder (α : Type*) extends has_btw α, has_sbtw α :=
(btw_refl : ∀ a b : α, btw a b b)
(btw_cyclic : ∀ a b c : α, btw a b c → a ≠ b → btw b c a)
(btw_trans : ∀ a b c d : α, btw a b c → btw a c d → btw a b d)
(sbtw := λ a b c, btw a b c ∧ ¬btw c b a)
(sbtw_iff_btw_not_btw : ∀ a b c : α, sbtw a b c ↔ (¬btw c b a) . order_laws_tac)

export circular_preorder (btw_refl) (btw_trans)

section circular_preorder
variables {α : Type*} [circular_preorder α]

lemma btw_rfl {a b : α} : btw a b b :=
btw_refl _ _

lemma btw_trans : ∀ {a b c d : α}, btw a b c → btw a c d → btw a b d :=
circular_preorder.btw_trans

--alias btw_trans        ← has_btw.btw.trans
lemma has_btw.btw.trans {a b c d : α} (h : btw a b c) : btw a c d → btw a b d :=
btw_trans h

/-- Circular interval closed-closed -/
def cIcc (a b : α) : set α := {x | btw a x b}

/-- Circular interval closed-open -/
def cIco (a b : α) : set α := {x | btw a x b ∧ ¬btw a b x}

/-- Circular interval open-closed -/
def cIoc (a b : α) : set α := {x | btw a x b ∧ ¬btw x a b}

/-- Circular interval open-open -/
def cIoo (a b : α) : set α := {x | btw a x b ∧ ¬btw a b x ∧ ¬btw x a b}

end circular_preorder

/-! ### Circular partial orders -/

class circular_partial_order (α : Type*) extends circular_preorder α :=
(btw_antisymm : ∀ a b c : α, btw a b c → btw a c b → b = c)

section circular_partial_order
variables {α : Type*} [circular_partial_order α]

lemma btw_antisymm : ∀ {a b c : α}, btw a b c → btw a c b → b = c :=
circular_partial_order.btw_antisymm

--alias btw_antisymm        ← has_btw.btw.antisymm
lemma has_btw.btw.antisymm {a b c : α} (h : btw a b c) : btw a c b → b = c :=
btw_antisymm h

end circular_partial_order

/-! ### Circular orders -/

class circular_order (α : Type*) extends circular_partial_order α :=
(btw_total : ∀ a b c : α, btw a b c ∨ btw a c b)

export circular_order (btw_total)

section circular_order
variables {α : Type*} [circular_order α]

end circular_order

section order_dual

instance (α : Type*) [has_btw α] : has_btw (order_dual α) := ⟨λ a b c : α, btw a c b⟩
instance (α : Type*) [has_sbtw α] : has_sbtw (order_dual α) := ⟨λ a b c : α, sbtw a c b⟩

instance (α : Type*) [h : circular_preorder α] : circular_preorder (order_dual α) :=
{ btw_refl := btw_refl,
  btw_cyclic := _,
  btw_trans := λ a b c d habc hacd, hacd.trans habc,
  sbtw_iff_btw_not_btw := λ _ _, sorry,
  .. order_dual.has_btw α,
  .. order_dual.has_sbtw α }

instance (α : Type*) [circular_partial_order α] : circular_partial_order (order_dual α) :=
{ btw_antisymm := λ a b c habc hacb, @btw_antisymm α _ _ _ _ hacb habc,
  .. order_dual.circular_preorder α }

instance (α : Type*) [circular_order α] : circular_order (order_dual α) :=
{ btw_total := λ a b c, btw_total a c b, .. order_dual.circular_partial_order α }


end order_dual
