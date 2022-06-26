/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import set_theory.game.basic
import tactic.nth_rewrite.default

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/

universe u

open_locale pgame

variables {x y : pgame.{u}}

namespace pgame

/-- An impartial pre-game is equivalent to its negation, and all of its options are impartial too.

Note that this is **not** the standard definition of an impartial game, which requires the stronger
condition `x = -x`. However, this weaker notion of impartiality suffices to prove Sprague-Grundy.
-/
def impartial : pgame → Prop
| x := x ≈ -x ∧ (∀ i, impartial (x.move_left i)) ∧ ∀ j, impartial (x.move_right j)
using_well_founded { dec_tac := pgame_wf_tac }

theorem impartial_def :
  impartial x ↔ x ≈ -x ∧ (∀ i, impartial (x.move_left i)) ∧ ∀ j, impartial (x.move_right j) :=
by rw impartial

namespace impartial

theorem mk (h₁ : x ≈ -x) (h₂ : ∀ i, impartial (x.move_left i))
  (h₃ : ∀ j, impartial (x.move_right j)) : impartial x :=
impartial_def.2 ⟨h₁, h₂, h₃⟩

theorem equiv_neg (h : impartial x) : x ≈ -x :=
(impartial_def.1 h).1

theorem quot_neg (h : impartial x) : -⟦x⟧ = ⟦x⟧ :=
quot.sound h.equiv_neg.symm

theorem move_left (h : impartial x) : ∀ i, (x.move_left i).impartial :=
(impartial_def.1 h).2.1

theorem move_right (h : impartial x) : ∀ i, (x.move_right i).impartial :=
(impartial_def.1 h).2.2

end impartial

@[simp] theorem impartial_zero : impartial 0 :=
by { rw impartial, simp [is_empty.forall_iff] }

@[simp] theorem impartial_star : impartial star :=
by { rw impartial, simp }

namespace impartial

theorem neg : ∀ {x}, impartial x → impartial (-x)
| x := λ h, begin
  apply mk _ (λ i, _) (λ j, _),
  { rw neg_neg,
    exact h.equiv_neg.symm },
  { rw move_left_neg',
    exact (h.move_right _).neg },
  { rw move_right_neg',
    exact (h.move_left _).neg }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add : ∀ {x y : pgame}, impartial x → impartial y → impartial (x + y)
| x y hx hy := begin
  refine mk ((add_congr hx.equiv_neg hy.equiv_neg).trans
    (neg_add_relabelling _ _).equiv.symm) (λ k, _) (λ k, _),
  { apply left_moves_add_cases k,
    all_goals
    { intro i, simp only [add_move_left_inl, add_move_left_inr],
      apply add;
      solve_by_elim [impartial.move_left, impartial.move_right] } },
  { apply right_moves_add_cases k,
    all_goals
    { intro j, simp only [add_move_right_inl, add_move_right_inr],
      apply add;
      solve_by_elim [impartial.move_left, impartial.move_right] } }
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- A local tactic for proving impartiality of games. -/
meta def impartiality :=
`[solve_by_elim
  [impartial.move_left, impartial.move_right, impartial_zero, impartial_star,
    impartial.neg, impartial.add]
  { max_depth := 6 }]

section two_vars

variables (hx : impartial x . impartiality) (hy : impartial y . impartiality)
include hx hy

theorem le_of_ge (h : x ≤ y) : y ≤ x :=
by rwa [le_congr hx.equiv_neg hy.equiv_neg, neg_le_neg_iff] at h

theorem lf_of_gf (h : x ⧏ y) : y ⧏ x :=
by rwa [lf_congr hx.equiv_neg hy.equiv_neg, neg_lf_neg_iff] at h

theorem le_iff_ge : x ≤ y ↔ y ≤ x :=
⟨le_of_ge hx hy, le_of_ge hy hx⟩

theorem lf_iff_gf : x ⧏ y ↔ y ⧏ x :=
⟨lf_of_gf hx hy, lf_of_gf hy hx⟩

theorem equiv_of_le (h : x ≤ y) : x ≈ y :=
⟨h, le_of_ge hx hy h⟩

theorem fuzzy_of_lf (h : x ⧏ y) : x ∥ y :=
⟨h, lf_of_gf hx hy h⟩

theorem le_iff_equiv : x ≤ y ↔ x ≈ y :=
⟨equiv_of_le hx hy, equiv.le⟩

theorem lf_iff_fuzzy : x ⧏ y ↔ x ∥ y :=
⟨fuzzy_of_lf hx hy, fuzzy.lf⟩

theorem not_lt : ¬ x < y :=
λ h, h.le.not_gf $ lf_of_gf hx hy h.lf

theorem equiv_or_fuzzy : x ≈ y ∨ x ∥ y :=
begin
  rcases lt_or_equiv_or_gt_or_fuzzy x y with h | h | h | h,
  { exact (not_lt hx hy h).elim },
  { exact or.inl h },
  { exact (not_lt hy hx h).elim },
  { exact or.inr h }
end

/-! Having proven that all other order relations on impartial games are redundant, we build the API
on impartial games using only `≈` and `∥`. -/

theorem not_equiv_iff_fuzzy : ¬ x ≈ y ↔ x ∥ y :=
⟨(equiv_or_fuzzy hx hy).resolve_left, fuzzy.not_equiv⟩

theorem not_fuzzy_iff_equiv : ¬ x ∥ y ↔ x ≈ y :=
⟨(equiv_or_fuzzy hx hy).resolve_right, equiv.not_fuzzy⟩

theorem equiv_iff_equiv_iff_fuzzy_iff_fuzzy {w z : pgame} (hw : impartial w) (hz : impartial z) :
  x ≈ y ↔ w ≈ z ↔ (x ∥ y ↔ w ∥ z) :=
by rw [←not_equiv_iff_fuzzy, ←not_equiv_iff_fuzzy, not_iff_not]; assumption

theorem equiv_iff_forall_fuzzy :
  x ≈ y ↔ (∀ i, x.move_left i ∥ y) ∧ ∀ j, x ∥ y.move_right j :=
begin
  rw [←le_iff_equiv hx hy, le_iff_forall_lf],
  congr'; apply propext (forall_congr (λ i, _));
  rw lf_iff_fuzzy;
  impartiality
end

theorem equiv_of_forall_fuzzy (h₁ : ∀ i, x.move_left i ∥ y) (h₂ : ∀ j, x ∥ y.move_right j) :
  x ≈ y :=
(equiv_iff_forall_fuzzy hx hy).2 ⟨h₁, h₂⟩

theorem move_left_fuzzy_of_equiv (h : x ≈ y) : ∀ i, x.move_left i ∥ y :=
((equiv_iff_forall_fuzzy hx hy).1 h).1

theorem fuzzy_move_right_of_equiv (h : x ≈ y) : ∀ j, x ∥ y.move_right j :=
((equiv_iff_forall_fuzzy hx hy).1 h).2

theorem fuzzy_iff_exists_equiv : x ∥ y ↔ (∃ i, x ≈ y.move_left i) ∨ ∃ j, x.move_right j ≈ y :=
begin
  rw [←lf_iff_fuzzy hx hy, lf_iff_exists_le],
  congr' 2; apply propext (exists_congr (λ i, _));
  rw le_iff_equiv;
  impartiality
end

theorem fuzzy_of_equiv_move_left {i} (h : x ≈ y.move_left i) : x ∥ y :=
(fuzzy_iff_exists_equiv hx hy).2 $ or.inl ⟨i, h⟩

theorem fuzzy_of_move_right_equiv {j} (h : x.move_right j ≈ y) : x ∥ y :=
(fuzzy_iff_exists_equiv hx hy).2 $ or.inr ⟨j, h⟩

end two_vars

section one_var

variable (hx : impartial x)
include hx

/-- In an impartial game, either the first player always wins, or the second player always wins. -/
theorem equiv_or_fuzzy_zero : x ≈ 0 ∨ x ∥ 0 :=
equiv_or_fuzzy hx impartial_zero

theorem not_equiv_zero_iff : ¬ x ≈ 0 ↔ x ∥ 0 :=
not_equiv_iff_fuzzy hx impartial_zero

theorem not_fuzzy_zero_iff : ¬ x ∥ 0 ↔ x ≈ 0 :=
not_fuzzy_iff_equiv hx impartial_zero

theorem add_self_equiv : x + x ≈ 0 :=
(add_congr_left hx.equiv_neg).trans (add_left_neg_equiv x)

theorem quot_add_self : ⟦x⟧ + ⟦x⟧ = 0 := quot.sound hx.add_self_equiv

/-- This lemma doesn't require `y` to be impartial. -/
theorem quot_add_eq_zero_iff (y : pgame) : ⟦y⟧ + ⟦x⟧ = 0 ↔ ⟦y⟧ = ⟦x⟧ :=
by rw [←@add_neg_eq_zero _ _ ⟦y⟧, hx.quot_neg]

/-- This lemma doesn't require `y` to be impartial. -/
theorem quot_add_eq_zero_iff' (y : pgame) : ⟦x⟧ + ⟦y⟧ = 0 ↔ ⟦x⟧ = ⟦y⟧ :=
by rw [←@neg_add_eq_zero _ _ ⟦x⟧, hx.quot_neg]

/-- This lemma doesn't require `y` to be impartial. -/
theorem add_equiv_zero_iff (y : pgame) : y + x ≈ 0 ↔ y ≈ x :=
by { rw [equiv_iff_game_eq, equiv_iff_game_eq, ←quot_add_eq_zero_iff hx], refl }

/-- This lemma doesn't require `y` to be impartial. -/
theorem add_equiv_zero_iff' (y : pgame) : x + y ≈ 0 ↔ x ≈ y :=
by { rw [equiv_iff_game_eq, equiv_iff_game_eq, ←quot_add_eq_zero_iff' hx], refl }

theorem add_fuzzy_zero_iff {y : pgame} (hy : impartial y) : x + y ∥ 0 ↔ x ∥ y :=
begin
  rw [←equiv_iff_equiv_iff_fuzzy_iff_fuzzy], refl }

/-- This lemma doesn't require `y` to be impartial. -/
theorem add_equiv_zero_iff' (y : pgame) : x + y ≈ 0 ↔ x ≈ y :=
by { rw [equiv_iff_game_eq, equiv_iff_game_eq, ←quot_add_eq_zero_iff' hx], refl }

theorem equiv_zero_iff_forall_fuzzy : x ≈ 0 ↔ ∀ i, x.move_left i ∥ 0 :=
by { rw equiv_iff_forall_fuzzy hx impartial_zero, simp [is_empty.forall_iff] }

theorem equiv_zero_iff_forall_fuzzy' : x ≈ 0 ↔ ∀ j, x.move_right j ∥ 0 :=
begin
  rw [equiv.comm, equiv_iff_forall_fuzzy impartial_zero hx],
  simp [is_empty.forall_iff, fuzzy.comm]
end

theorem fuzzy_zero_iff_exists_equiv' : x ∥ 0 ↔ ∃ j, x.move_right j ≈ 0 :=
by { rw fuzzy_iff_exists_equiv hx impartial_zero, simp [is_empty.exists_iff] }

theorem fuzzy_zero_iff_exists_equiv : x ∥ 0 ↔ ∃ i, x.move_left i ≈ 0 :=
begin
  rw [fuzzy.comm, fuzzy_iff_exists_equiv impartial_zero hx],
  simp [is_empty.exists_iff, equiv.comm]
end

end one_var

end impartial

end pgame
