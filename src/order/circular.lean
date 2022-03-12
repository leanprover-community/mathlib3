/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.basic

/-!
# Circular order hierarchy

This file defines circular preorders, circular partial orders and circular orders.

## Hierarchy

* A ternary "betweenness" relation `btw : α → α → α → Prop` forms a `circular_order` if it is
  - reflexive: `btw a a a`
  - cyclic: `btw a b c → btw b c a`
  - antisymmetric: `btw a b c → btw c b a → a = b ∨ b = c ∨ c = a`
  - total: `btw a b c ∨ btw c b a`
  along with a strict betweenness relation `sbtw : α → α → α → Prop` which respects
  `sbtw a b c ↔ btw a b c ∧ ¬ btw c b a`, analogously to how `<` and `≤` are related, and is
  - transitive: `sbtw a b c → sbtw b d c → sbtw a d c`.
* A `circular_partial_order` drops totality.
* A `circular_preorder` further drops antisymmetry.

The intuition is that a circular order is a circle and `btw a b c` means that going around
clockwise from `a` you reach `b` before `c` (`b` is between `a` and `c` is meaningless on an
unoriented circle). A circular partial order is several, potentially intersecting, circles. A
circular preorder is like a circular partial order, but several points can coexist.

Note that the relations between `circular_preorder`, `circular_partial_order` and `circular_order`
are subtler than between `preorder`, `partial_order`, `linear_order`. In particular, one cannot
simply extend the `btw` of a `circular_partial_order` to make it a `circular_order`.

One can translate from usual orders to circular ones by "closing the necklace at infinity". See
`has_le.to_has_btw` and `has_lt.to_has_sbtw`. Going the other way involves "cutting the necklace" or
"rolling the necklace open".

## Examples

Some concrete circular orders one encounters in the wild are `zmod n` for `0 < n`, `circle`,
`real.angle`...

## Main definitions

* `set.cIcc`: Closed-closed circular interval.
* `set.cIoo`: Open-open circular interval.

## Notes

There's an unsolved diamond here. The instances `has_le α → has_btw (order_dual α)` and
`has_lt α → has_sbtw (order_dual α)` can each be inferred in two ways:
* `has_le α` → `has_btw α` → `has_btw (order_dual α)` vs
  `has_le α` → `has_le (order_dual α)` → `has_btw (order_dual α)`
* `has_lt α` → `has_sbtw α` → `has_sbtw (order_dual α)` vs
  `has_lt α` → `has_lt (order_dual α)` → `has_sbtw (order_dual α)`
The fields are propeq, but not defeq. It is temporarily fixed by turning the circularizing instances
into definitions.

## TODO

Antisymmetry is quite weak in the sense that there's no way to discriminate which two points are
equal. This prevents defining closed-open intervals `cIco` and `cIoc` in the neat `=`-less way. We
currently haven't defined them at all.

What is the correct generality of "rolling the necklace" open? At least, this works for `α × β` and
`β × α` where `α` is a circular order and `β` is a linear order.

What's next is to define circular groups and provide instances for `zmod n`, the usual circle group
`circle`, `real.angle`, and `roots_of_unity M`. What conditions do we need on `M` for this last one
to work?

We should have circular order homomorphisms. The typical example is
`days_to_month : days_of_the_year →c months_of_the_year` which relates the circular order of days
and the circular order of months. Is `α →c β` a good notation?

## References

* https://en.wikipedia.org/wiki/Cyclic_order
* https://en.wikipedia.org/wiki/Partial_cyclic_order

## Tags

circular order, cyclic order, circularly ordered set, cyclically ordered set
-/

/-- Syntax typeclass for a betweenness relation. -/
class has_btw (α : Type*) :=
(btw : α → α → α → Prop)

export has_btw (btw)

/-- Syntax typeclass for a strict betweenness relation. -/
class has_sbtw (α : Type*) :=
(sbtw : α → α → α → Prop)

export has_sbtw (sbtw)

/-- A circular preorder is the analogue of a preorder where you can loop around. `≤` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive and cyclic. `sbtw` is transitive.
-/
class circular_preorder (α : Type*) extends has_btw α, has_sbtw α :=
(btw_refl (a : α) : btw a a a)
(btw_cyclic_left {a b c : α} : btw a b c → btw b c a)
(sbtw := λ a b c, btw a b c ∧ ¬btw c b a)
(sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ (btw a b c ∧ ¬btw c b a) . order_laws_tac)
(sbtw_trans_left {a b c d : α} : sbtw a b c → sbtw b d c → sbtw a d c)

export circular_preorder (btw_refl) (btw_cyclic_left) (sbtw_trans_left)

/-- A circular partial order is the analogue of a partial order where you can loop around. `≤` and
`<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic and
antisymmetric. `sbtw` is transitive. -/
class circular_partial_order (α : Type*) extends circular_preorder α :=
(btw_antisymm {a b c : α} : btw a b c → btw c b a → a = b ∨ b = c ∨ c = a)

export circular_partial_order (btw_antisymm)

/-- A circular order is the analogue of a linear order where you can loop around. `≤` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic, antisymmetric and total.
`sbtw` is transitive. -/
class circular_order (α : Type*) extends circular_partial_order α :=
(btw_total : ∀ a b c : α, btw a b c ∨ btw c b a)

export circular_order (btw_total)

/-! ### Circular preorders -/

section circular_preorder
variables {α : Type*} [circular_preorder α]

lemma btw_rfl {a : α} : btw a a a :=
btw_refl _

-- TODO: `alias` creates a def instead of a lemma.
-- alias btw_cyclic_left        ← has_btw.btw.cyclic_left
lemma has_btw.btw.cyclic_left {a b c : α} (h : btw a b c) : btw b c a :=
btw_cyclic_left h

lemma btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a b :=
h.cyclic_left.cyclic_left

alias btw_cyclic_right ← has_btw.btw.cyclic_right

/-- The order of the `↔` has been chosen so that `rw btw_cyclic` cycles to the right while
`rw ←btw_cyclic` cycles to the left (thus following the prepended arrow). -/
lemma btw_cyclic {a b c : α} : btw a b c ↔ btw c a b :=
⟨btw_cyclic_right, btw_cyclic_left⟩

lemma sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a :=
circular_preorder.sbtw_iff_btw_not_btw

lemma btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c :=
(sbtw_iff_btw_not_btw.1 h).1

alias btw_of_sbtw ← has_sbtw.sbtw.btw

lemma not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
(sbtw_iff_btw_not_btw.1 h).2

alias not_btw_of_sbtw ← has_sbtw.sbtw.not_btw

lemma not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a :=
λ h', h'.not_btw h

alias not_sbtw_of_btw ← has_btw.btw.not_sbtw

lemma sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩

alias sbtw_of_btw_not_btw ← has_btw.btw.sbtw_of_not_btw

lemma sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a :=
h.btw.cyclic_left.sbtw_of_not_btw (λ h', h.not_btw h'.cyclic_left)

alias sbtw_cyclic_left ← has_sbtw.sbtw.cyclic_left

lemma sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
h.cyclic_left.cyclic_left

alias sbtw_cyclic_right ← has_sbtw.sbtw.cyclic_right

/-- The order of the `↔` has been chosen so that `rw sbtw_cyclic` cycles to the right while
`rw ←sbtw_cyclic` cycles to the left (thus following the prepended arrow). -/
lemma sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b :=
⟨sbtw_cyclic_right, sbtw_cyclic_left⟩

-- TODO: `alias` creates a def instead of a lemma.
-- alias btw_trans_left        ← has_btw.btw.trans_left
lemma has_sbtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c) : sbtw b d c → sbtw a d c :=
sbtw_trans_left h

lemma sbtw_trans_right {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d) : sbtw a b d :=
(hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right

alias sbtw_trans_right ← has_sbtw.sbtw.trans_right

lemma sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬ sbtw c b a :=
h.btw.not_sbtw

alias sbtw_asymm ← has_sbtw.sbtw.not_sbtw

lemma sbtw_irrefl_left_right {a b : α} : ¬ sbtw a b a := λ h, h.not_btw h.btw
lemma sbtw_irrefl_left {a b : α} : ¬ sbtw a a b := λ h, sbtw_irrefl_left_right h.cyclic_left
lemma sbtw_irrefl_right {a b : α} : ¬ sbtw a b b := λ h, sbtw_irrefl_left_right h.cyclic_right
lemma sbtw_irrefl (a : α) : ¬ sbtw a a a := sbtw_irrefl_left_right

end circular_preorder

/-! ### Circular partial orders -/

section circular_partial_order
variables {α : Type*} [circular_partial_order α]

-- TODO: `alias` creates a def instead of a lemma.
-- alias btw_antisymm        ← has_btw.btw.antisymm
lemma has_btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a → a = b ∨ b = c ∨ c = a :=
btw_antisymm h

end circular_partial_order

/-! ### Circular orders -/

section circular_order
variables {α : Type*} [circular_order α]

lemma btw_refl_left_right (a b : α) : btw a b a :=
(or_self _).1 (btw_total a b a)

lemma btw_rfl_left_right {a b : α} : btw a b a :=
btw_refl_left_right _ _

lemma btw_refl_left (a b : α) : btw a a b :=
btw_rfl_left_right.cyclic_right

lemma btw_rfl_left {a b : α} : btw a a b :=
btw_refl_left _ _

lemma btw_refl_right (a b : α) : btw a b b :=
btw_rfl_left_right.cyclic_left

lemma btw_rfl_right {a b : α} : btw a b b :=
btw_refl_right _ _

lemma sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬ btw c b a :=
begin
  rw sbtw_iff_btw_not_btw,
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left,
end

lemma btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬ sbtw c b a :=
iff_not_comm.1 sbtw_iff_not_btw

end circular_order

/-! ### Circular intervals -/

namespace set

section circular_preorder
variables {α : Type*} [circular_preorder α]

/-- Closed-closed circular interval -/
def cIcc (a b : α) : set α := {x | btw a x b}

/-- Open-open circular interval -/
def cIoo (a b : α) : set α := {x | sbtw a x b}

@[simp] lemma mem_cIcc {a b x : α} : x ∈ cIcc a b ↔ btw a x b := iff.rfl
@[simp] lemma mem_cIoo {a b x : α} : x ∈ cIoo a b ↔ sbtw a x b := iff.rfl

end circular_preorder

section circular_order
variables {α : Type*} [circular_order α]

lemma left_mem_cIcc (a b : α) : a ∈ cIcc a b := btw_rfl_left
lemma right_mem_cIcc (a b : α) : b ∈ cIcc a b := btw_rfl_right

lemma compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a :=
begin
  ext,
  rw [set.mem_cIoo, sbtw_iff_not_btw],
  refl,
end

lemma compl_cIoo {a b : α} : (cIoo a b)ᶜ = cIcc b a :=
begin
  ext,
  rw [set.mem_cIcc, btw_iff_not_sbtw],
  refl,
end

end circular_order
end set

/-! ### Circularizing instances -/

/-- The betweenness relation obtained from "looping around" `≤`.
See note [reducible non-instances]. -/
@[reducible]
def has_le.to_has_btw (α : Type*) [has_le α] : has_btw α :=
{ btw := λ a b c, (a ≤ b ∧ b ≤ c) ∨ (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) }

/-- The strict betweenness relation obtained from "looping around" `<`.
See note [reducible non-instances]. -/
@[reducible]
def has_lt.to_has_sbtw (α : Type*) [has_lt α] : has_sbtw α :=
{ sbtw := λ a b c, (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) }

/-- The circular preorder obtained from "looping around" a preorder.
See note [reducible non-instances]. -/
@[reducible]
def preorder.to_circular_preorder (α : Type*) [preorder α] : circular_preorder α :=
{ btw := λ a b c, (a ≤ b ∧ b ≤ c) ∨ (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b),
  sbtw := λ a b c, (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b),
  btw_refl := λ a, or.inl ⟨le_rfl, le_rfl⟩,
  btw_cyclic_left := λ a b c h, begin
    unfold btw at ⊢ h,
    rwa [←or.assoc, or_comm],
  end,
  sbtw_trans_left := λ a b c d, begin
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩),
    { exact or.inl ⟨hab.trans hbd, hdc⟩ },
    { exact (hbc.not_lt hcb).elim },
    { exact (hbc.not_lt hcb).elim },
    { exact or.inr (or.inl ⟨hdc, hca⟩) },
    { exact or.inr (or.inl ⟨hdc, hca⟩) },
    { exact (hbc.not_lt hcb).elim },
    { exact or.inr (or.inl ⟨hdc, hca⟩) },
    { exact or.inr (or.inl ⟨hdc, hca⟩) },
    { exact or.inr (or.inr ⟨hca, hab.trans hbd⟩) }
  end,
  sbtw_iff_btw_not_btw := λ a b c, begin
    simp_rw lt_iff_le_not_le,
    set x₀ := a ≤ b,
    set x₁ := b ≤ c,
    set x₂ := c ≤ a,
    have : x₀ → x₁ → a ≤ c := le_trans,
    have : x₁ → x₂ → b ≤ a := le_trans,
    have : x₂ → x₀ → c ≤ b := le_trans,
    clear_value x₀ x₁ x₂,
    tauto!,
  end }

/-- The circular partial order obtained from "looping around" a partial order.
See note [reducible non-instances]. -/
@[reducible]
def partial_order.to_circular_partial_order (α : Type*) [partial_order α] :
  circular_partial_order α :=
{ btw_antisymm := λ a b c, begin
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩),
    { exact or.inl (hab.antisymm hba) },
    { exact or.inl (hab.antisymm hba) },
    { exact or.inr (or.inl $ hbc.antisymm hcb) },
    { exact or.inr (or.inl $ hbc.antisymm hcb) },
    { exact or.inr (or.inr $ hca.antisymm hac) },
    { exact or.inr (or.inl $ hbc.antisymm hcb) },
    { exact or.inl (hab.antisymm hba) },
    { exact or.inl (hab.antisymm hba) },
    { exact or.inr (or.inr $ hca.antisymm hac) }
  end,
  .. preorder.to_circular_preorder α }

/-- The circular order obtained from "looping around" a linear order.
See note [reducible non-instances]. -/
@[reducible]
def linear_order.to_circular_order (α : Type*) [linear_order α] :
  circular_order α :=
{ btw_total := λ a b c, begin
    cases le_total a b with hab hba; cases le_total b c with hbc hcb;
      cases le_total c a with hca hac,
    { exact or.inl (or.inl ⟨hab, hbc⟩) },
    { exact or.inl (or.inl ⟨hab, hbc⟩) },
    { exact or.inl (or.inr $ or.inr ⟨hca, hab⟩) },
    { exact or.inr (or.inr $ or.inr ⟨hac, hcb⟩) },
    { exact or.inl (or.inr $ or.inl ⟨hbc, hca⟩) },
    { exact or.inr (or.inr $ or.inl ⟨hba, hac⟩) },
    { exact or.inr (or.inl ⟨hcb, hba⟩) },
    { exact or.inr (or.inr $ or.inl ⟨hba, hac⟩) }
  end,
  .. partial_order.to_circular_partial_order α }

/-! ### Dual constructions -/

section order_dual

instance (α : Type*) [has_btw α] : has_btw (order_dual α) := ⟨λ a b c : α, btw c b a⟩
instance (α : Type*) [has_sbtw α] : has_sbtw (order_dual α) := ⟨λ a b c : α, sbtw c b a⟩

instance (α : Type*) [h : circular_preorder α] : circular_preorder (order_dual α) :=
{ btw_refl := btw_refl,
  btw_cyclic_left := λ a b c, btw_cyclic_right,
  sbtw_trans_left := λ a b c d habc hbdc, hbdc.trans_right habc,
  sbtw_iff_btw_not_btw := λ a b c, @sbtw_iff_btw_not_btw α _ c b a,
  .. order_dual.has_btw α,
  .. order_dual.has_sbtw α }

instance (α : Type*) [circular_partial_order α] : circular_partial_order (order_dual α) :=
{ btw_antisymm := λ a b c habc hcba, @btw_antisymm α _ _ _ _ hcba habc,
  .. order_dual.circular_preorder α }

instance (α : Type*) [circular_order α] : circular_order (order_dual α) :=
{ btw_total := λ a b c, btw_total c b a, .. order_dual.circular_partial_order α }

end order_dual
