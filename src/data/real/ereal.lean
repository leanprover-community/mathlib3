/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import data.real.basic

/-!
# The extended reals [-∞, ∞].

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥.

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.
`ereal` is a `complete_lattice`; this is now deduced by type class inference from
the fact that `with_top (with_bot L)` is a complete lattice if `L` is
a conditionally complete lattice

## Tags

real, ereal, complete lattice
-/

/-- ereal : The type $$[-\infty,+\infty]$$ or `[-∞, ∞]` -/
@[derive [linear_order, lattice.order_bot, lattice.order_top,
  lattice.has_Sup, lattice.complete_lattice]]
def ereal := with_top (with_bot ℝ)

namespace ereal
instance : has_coe ℝ ereal := ⟨some ∘ some⟩
@[simp, elim_cast] protected lemma coe_real_le {x y : ℝ} : (x : ereal) ≤ (y : ereal) ↔ x ≤ y :=
by { unfold_coes, norm_num }
@[simp, elim_cast] protected lemma coe_real_lt {x y : ℝ} : (x : ereal) < (y : ereal) ↔ x < y :=
by { unfold_coes, norm_num }
@[simp, elim_cast] protected lemma coe_real_inj' {x y : ℝ} : (x : ereal) = (y : ereal) ↔ x = y :=
by { unfold_coes, simp [option.some_inj] }

/- neg -/
/-- negation on ereal -/
protected def neg : ereal → ereal
| ⊥       := ⊤
| ⊤       := ⊥
| (x : ℝ) := (-x : ℝ)

instance : has_neg ereal := ⟨ereal.neg⟩

@[move_cast] protected lemma neg_def (x : ℝ) : ((-x : ℝ) : ereal) = -x := rfl

/-- if -a ≤ b then -b ≤ a on ereal -/
protected theorem neg_le_of_neg_le : ∀ {a b : ereal} (h : -a ≤ b), -b ≤ a
| ⊥ ⊥ h := h
| ⊥ (some b) h := by cases (lattice.top_le_iff.1 h)
| ⊤ l h := lattice.le_top
| (a : ℝ) ⊥ h := by cases (lattice.le_bot_iff.1 h)
| l ⊤ h := lattice.bot_le
| (a : ℝ) (b : ℝ) h := by { norm_cast at h ⊢, exact _root_.neg_le_of_neg_le h }

/-- -a ≤ b ↔ -b ≤ a on ereal-/
protected theorem neg_le {a b : ereal} : -a ≤ b ↔ -b ≤ a :=
⟨ereal.neg_le_of_neg_le, ereal.neg_le_of_neg_le⟩

/-- - -a = a on ereal -/
protected theorem neg_neg : ∀ (a : ereal), - (- a) = a
| ⊥ := rfl
| ⊤ := rfl
| (a : ℝ) := by { norm_cast, simp [neg_neg a] }

/-- a ≤ -b → b ≤ -a on ereal -/
theorem le_neg_of_le_neg {a b : ereal} (h : a ≤ -b) : b ≤ -a :=
by rwa [←ereal.neg_neg b, ereal.neg_le, ereal.neg_neg]

end ereal
