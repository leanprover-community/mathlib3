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

namespace pgame

/-- An impartial pre-game is equivalent to its negation, and all of its options are impartial too.

Note that this is **not** the standard definition of an impartial game, which requires the stronger
condition `x = -x`. However, this weaker notion of impartiality suffices to prove Sprague-Grundy.
-/
def impartial : pgame → Prop
| x := x ≈ -x ∧ (∀ i, impartial (x.move_left i)) ∧ ∀ j, impartial (x.move_right j)
using_well_founded { dec_tac := pgame_wf_tac }

theorem impartial_def {x} :
  impartial x ↔ x ≈ -x ∧ (∀ i, impartial (x.move_left i)) ∧ ∀ j, impartial (x.move_right j) :=
by rw impartial

namespace impartial

theorem mk {x} (h₁ : x ≈ -x) (h₂ : ∀ i, impartial (x.move_left i))
  (h₃ : ∀ j, impartial (x.move_right j)) : impartial x :=
impartial_def.2 ⟨h₁, h₂, h₃⟩

theorem neg_equiv_self {x} (h : impartial x) : x ≈ -x :=
(impartial_def.1 h).1

theorem mk_neg_eq_self {x} (h : impartial x) : -⟦x⟧ = ⟦x⟧ :=
quot.sound h.neg_equiv_self.symm

theorem move_left {x} (h : impartial x) : ∀ i, (x.move_left i).impartial :=
(impartial_def.1 h).2.1

theorem move_right {x} (h : impartial x) : ∀ i, (x.move_right i).impartial :=
(impartial_def.1 h).2.2

end impartial

theorem impartial_zero : impartial 0 :=
by { rw impartial, simp [is_empty.forall_iff] }

theorem impartial_star : impartial star :=
by { rw impartial, simpa using impartial_zero }

namespace relabelling

theorem impartial_imp : ∀ {x y : pgame} (r : x ≡r y) (h : impartial x), impartial y
| x y r := λ h, impartial.mk ((r.equiv'.trans h.neg_equiv_self).trans (neg_equiv_neg_iff.2 r.equiv))
  (λ i, impartial_imp (r.move_left_symm i) (h.move_left _))
  (λ j, impartial_imp (r.move_right j) (h.move_right _))
using_well_founded { dec_tac := pgame_wf_tac }

instance impartial_add : ∀ (G H : pgame) [G.impartial] [H.impartial], (G + H).impartial
| G H :=
begin
  introsI hG hH,
  rw impartial_def,
  refine ⟨(add_congr (neg_equiv_self _) (neg_equiv_self _)).trans
    (neg_add_relabelling _ _).equiv.symm, λ k, _, λ k, _⟩,
  { apply left_moves_add_cases k,
    all_goals
    { intro i, simp only [add_move_left_inl, add_move_left_inr],
      apply impartial_add } },
  { apply right_moves_add_cases k,
    all_goals
    { intro i, simp only [add_move_right_inl, add_move_right_inr],
      apply impartial_add } }
end
using_well_founded { dec_tac := pgame_wf_tac }

end relabelling

instance impartial_neg : ∀ (G : pgame) [G.impartial], (-G).impartial
| G :=
begin
  introI hG,
  rw impartial_def,
  refine ⟨_, λ i, _, λ i, _⟩,
  { rw neg_neg,
    exact (neg_equiv_self G).symm },
  { rw move_left_neg',
    apply impartial_neg },
  { rw move_right_neg',
    apply impartial_neg }
end
using_well_founded { dec_tac := pgame_wf_tac }

variables (G : pgame) [impartial G]

lemma nonpos : ¬ 0 < G :=
λ h, begin
  have h' := neg_lt_neg_iff.2 h,
  rw [pgame.neg_zero, lt_congr_left (neg_equiv_self G).symm] at h',
  exact (h.trans h').false
end

lemma nonneg : ¬ G < 0 :=
λ h, begin
  have h' := neg_lt_neg_iff.2 h,
  rw [pgame.neg_zero, lt_congr_right (neg_equiv_self G).symm] at h',
  exact (h.trans h').false
end

/-- In an impartial game, either the first player always wins, or the second player always wins. -/
lemma equiv_or_fuzzy_zero : G ≈ 0 ∨ G ∥ 0 :=
begin
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with h | h | h | h,
  { exact ((nonneg G) h).elim },
  { exact or.inl h },
  { exact ((nonpos G) h).elim },
  { exact or.inr h }
end

@[simp] lemma not_equiv_zero_iff : ¬ G ≈ 0 ↔ G ∥ 0 :=
⟨(equiv_or_fuzzy_zero G).resolve_left, fuzzy.not_equiv⟩

@[simp] lemma not_fuzzy_zero_iff : ¬ G ∥ 0 ↔ G ≈ 0 :=
⟨(equiv_or_fuzzy_zero G).resolve_right, equiv.not_fuzzy⟩

lemma add_self : G + G ≈ 0 :=
(add_congr_left (neg_equiv_self G)).trans (add_left_neg_equiv G)

@[simp] lemma mk_add_self : ⟦G⟧ + ⟦G⟧ = 0 := quot.sound (add_self G)

/-- This lemma doesn't require `H` to be impartial. -/
lemma equiv_iff_add_equiv_zero (H : pgame) : H ≈ G ↔ H + G ≈ 0 :=
by { rw [equiv_iff_game_eq, equiv_iff_game_eq, ←@add_right_cancel_iff _ _ (-⟦G⟧)], simpa }

/-- This lemma doesn't require `H` to be impartial. -/
lemma equiv_iff_add_equiv_zero' (H : pgame) : G ≈ H ↔ G + H ≈ 0 :=
by { rw [equiv_iff_game_eq, equiv_iff_game_eq, ←@add_left_cancel_iff _ _ (-⟦G⟧), eq_comm], simpa }

lemma le_zero_iff {G : pgame} [G.impartial] : G ≤ 0 ↔ 0 ≤ G :=
by rw [←zero_le_neg_iff, le_congr_right (neg_equiv_self G)]

lemma lf_zero_iff {G : pgame} [G.impartial] : G ⧏ 0 ↔ 0 ⧏ G :=
by rw [←zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]

lemma equiv_zero_iff_le: G ≈ 0 ↔ G ≤ 0 := ⟨and.left, λ h, ⟨h, le_zero_iff.1 h⟩⟩
lemma fuzzy_zero_iff_lf : G ∥ 0 ↔ G ⧏ 0 := ⟨and.left, λ h, ⟨h, lf_zero_iff.1 h⟩⟩
lemma equiv_zero_iff_ge : G ≈ 0 ↔ 0 ≤ G := ⟨and.right, λ h, ⟨le_zero_iff.2 h, h⟩⟩
lemma fuzzy_zero_iff_gf : G ∥ 0 ↔ 0 ⧏ G := ⟨and.right, λ h, ⟨lf_zero_iff.2 h, h⟩⟩

lemma forall_left_moves_fuzzy_iff_equiv_zero : (∀ i, G.move_left i ∥ 0) ↔ G ≈ 0 :=
begin
  refine ⟨λ hb, _, λ hp i, _⟩,
  { rw [equiv_zero_iff_le G, le_zero_lf],
    exact λ i, (hb i).1 },
  { rw fuzzy_zero_iff_lf,
    exact move_left_lf_of_le i hp.1 }
end

lemma forall_right_moves_fuzzy_iff_equiv_zero : (∀ j, G.move_right j ∥ 0) ↔ G ≈ 0 :=
begin
  refine ⟨λ hb, _, λ hp i, _⟩,
  { rw [equiv_zero_iff_ge G, zero_le_lf],
    exact λ i, (hb i).2 },
  { rw fuzzy_zero_iff_gf,
    exact lf_move_right_of_le i hp.2 }
end

lemma exists_left_move_equiv_iff_fuzzy_zero : (∃ i, G.move_left i ≈ 0) ↔ G ∥ 0 :=
begin
  refine ⟨λ ⟨i, hi⟩, (fuzzy_zero_iff_gf G).2 (lf_of_le_move_left hi.2), λ hn, _⟩,
  rw [fuzzy_zero_iff_gf G, zero_lf_le] at hn,
  cases hn with i hi,
  exact ⟨i, (equiv_zero_iff_ge _).2 hi⟩
end

lemma exists_right_move_equiv_iff_fuzzy_zero : (∃ j, G.move_right j ≈ 0) ↔ G ∥ 0 :=
begin
  refine ⟨λ ⟨i, hi⟩, (fuzzy_zero_iff_lf G).2 (lf_of_move_right_le hi.1), λ hn, _⟩,
  rw [fuzzy_zero_iff_lf G, lf_zero_le] at hn,
  cases hn with i hi,
  exact ⟨i, (equiv_zero_iff_le _).2 hi⟩
end

end impartial
end pgame
