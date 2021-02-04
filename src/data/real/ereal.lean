/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import data.real.basic

/-!
# The extended reals [-∞, ∞].

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. It is implemented as `with_top (with_bot ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.
An addition is derived, but `ereal` is not even a monoid (there is no identity).

`ereal` is a `complete_lattice`; this is now deduced by type class inference from
the fact that `with_top (with_bot L)` is a complete lattice if `L` is
a conditionally complete lattice.

## Tags

real, ereal, complete lattice

## TODO

abs : ereal → ennreal

In Isabelle they define + - * and / (making junk choices for things like -∞ + ∞)
and then prove whatever bits of the ordered ring/field axioms still hold. They
also do some limits stuff (liminf/limsup etc).
See https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Extended_Real.html
-/

/-- ereal : The type `[-∞, ∞]` -/
@[derive [linear_order, order_bot, order_top,
  has_Sup, has_Inf, complete_lattice, has_add]]
def ereal := with_top (with_bot ℝ)

namespace ereal
instance : has_coe ℝ ereal := ⟨some ∘ some⟩
@[simp, norm_cast] protected lemma coe_real_le {x y : ℝ} : (x : ereal) ≤ (y : ereal) ↔ x ≤ y :=
by { unfold_coes, norm_num }
@[simp, norm_cast] protected lemma coe_real_lt {x y : ℝ} : (x : ereal) < (y : ereal) ↔ x < y :=
by { unfold_coes, norm_num }
@[simp, norm_cast] protected lemma coe_real_inj' {x y : ℝ} : (x : ereal) = (y : ereal) ↔ x = y :=
by { unfold_coes, simp [option.some_inj] }

instance : has_zero ereal := ⟨(0 : ℝ)⟩
instance : inhabited ereal := ⟨0⟩

/-! ### Negation -/

/-- negation on ereal -/
protected def neg : ereal → ereal
| ⊥       := ⊤
| ⊤       := ⊥
| (x : ℝ) := (-x : ℝ)

instance : has_neg ereal := ⟨ereal.neg⟩

@[norm_cast] protected lemma neg_def (x : ℝ) : ((-x : ℝ) : ereal) = -x := rfl

/-- - -a = a on ereal -/
protected theorem neg_neg : ∀ (a : ereal), - (- a) = a
| ⊥ := rfl
| ⊤ := rfl
| (a : ℝ) := by { norm_cast, simp [neg_neg a] }

theorem neg_inj (a b : ereal) (h : -a = -b) : a = b := by rw [←ereal.neg_neg a, h, ereal.neg_neg b]

/-- Even though ereal is not an additive group, -a = b ↔ -b = a still holds -/
theorem neg_eq_iff_neg_eq {a b : ereal} : -a = b ↔ -b = a :=
⟨by {intro h, rw ←h, exact ereal.neg_neg a},
 by {intro h, rw ←h, exact ereal.neg_neg b}⟩

/-- if -a ≤ b then -b ≤ a on ereal -/
protected theorem neg_le_of_neg_le : ∀ {a b : ereal} (h : -a ≤ b), -b ≤ a
| ⊥ ⊥ h := h
| ⊥ (some b) h := by cases (top_le_iff.1 h)
| ⊤ l h := le_top
| (a : ℝ) ⊥ h := by cases (le_bot_iff.1 h)
| l ⊤ h := bot_le
| (a : ℝ) (b : ℝ) h := by { norm_cast at h ⊢, exact _root_.neg_le_of_neg_le h }

/-- -a ≤ b ↔ -b ≤ a on ereal-/
protected theorem neg_le {a b : ereal} : -a ≤ b ↔ -b ≤ a :=
⟨ereal.neg_le_of_neg_le, ereal.neg_le_of_neg_le⟩

/-- a ≤ -b → b ≤ -a on ereal -/
theorem le_neg_of_le_neg {a b : ereal} (h : a ≤ -b) : b ≤ -a :=
by rwa [←ereal.neg_neg b, ereal.neg_le, ereal.neg_neg]

end ereal
