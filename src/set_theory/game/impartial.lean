/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.game.winner
import tactic.nth_rewrite.default

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/

universe u

namespace pgame

local infix ` ≈ ` := equiv
local infix ` ⧏ `:50 := lf
local infix ` ∥ `:50 := fuzzy

/-- The definition for a impartial game, defined using Conway induction. -/
def impartial_aux : pgame → Prop
| G := G ≈ -G ∧ (∀ i, impartial_aux (G.move_left i)) ∧ ∀ j, impartial_aux (G.move_right j)
using_well_founded { dec_tac := pgame_wf_tac }

lemma impartial_aux_def {G : pgame} : G.impartial_aux ↔ G ≈ -G ∧
  (∀ i, impartial_aux (G.move_left i)) ∧ ∀ j, impartial_aux (G.move_right j) :=
by rw impartial_aux

/-- A typeclass on impartial games. -/
class impartial (G : pgame) : Prop := (out : impartial_aux G)

lemma impartial_iff_aux {G : pgame} : G.impartial ↔ G.impartial_aux :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma impartial_def {G : pgame} : G.impartial ↔ G ≈ -G ∧
  (∀ i, impartial (G.move_left i)) ∧ ∀ j, impartial (G.move_right j) :=
by simpa only [impartial_iff_aux] using impartial_aux_def

namespace impartial

instance impartial_zero : impartial 0 :=
by { rw impartial_def, dsimp, simp }

instance impartial_star : impartial star :=
by { rw impartial_def, simpa using impartial.impartial_zero }

lemma neg_equiv_self (G : pgame) [h : G.impartial] : G ≈ -G := (impartial_def.1 h).1

instance move_left_impartial {G : pgame} [h : G.impartial] (i : G.left_moves) :
  (G.move_left i).impartial :=
(impartial_def.1 h).2.1 i

instance move_right_impartial {G : pgame} [h : G.impartial] (j : G.right_moves) :
  (G.move_right j).impartial :=
(impartial_def.1 h).2.2 j

theorem impartial_congr : ∀ {G H : pgame} (e : relabelling G H) [G.impartial], H.impartial
| G H e := begin
  introI h,
  rw impartial_def,
  refine ⟨equiv_trans e.symm.equiv (equiv_trans (neg_equiv_self G) (neg_congr e.equiv)),
    λ i, _, λ j, _⟩;
  cases e with _ _ L R hL hR,
  { convert impartial_congr (hL (L.symm i)),
    rw equiv.apply_symm_apply },
  { exact impartial_congr (hR j) }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance impartial_add : ∀ (G H : pgame) [G.impartial] [H.impartial], (G + H).impartial
| G H :=
begin
  introsI hG hH,
  rw impartial_def,
  refine ⟨equiv_trans (add_congr (neg_equiv_self _) (neg_equiv_self _))
    (neg_add_relabelling _ _).equiv.symm, λ i, _, λ i, _⟩,
  { rcases left_moves_add_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩,
    all_goals
    { simp only [add_move_left_inl, add_move_left_inr],
      apply impartial_add } },
  { rcases right_moves_add_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩,
    all_goals
    { simp only [add_move_right_inl, add_move_right_inr],
      apply impartial_add } }
end
using_well_founded { dec_tac := pgame_wf_tac }

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

lemma nonpos (G : pgame) [G.impartial] : ¬ 0 < G :=
λ h, begin
  have h' := neg_lt_iff.2 h,
  rw [pgame.neg_zero, lt_congr_left (equiv_symm (neg_equiv_self G))] at h',
  exact (h.trans h').false
end

lemma nonneg (G : pgame) [G.impartial] : ¬ G < 0 :=
λ h, begin
  have h' := neg_lt_iff.2 h,
  rw [pgame.neg_zero, lt_congr_right (equiv_symm (neg_equiv_self G))] at h',
  exact (h.trans h').false
end

lemma equiv_or_fuzzy_zero (G : pgame) [G.impartial] : G ≈ 0 ∨ G ∥ 0 :=
begin
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with h | h | h | h,
  { exact ((nonneg G) h).elim },
  { exact or.inl h },
  { exact ((nonpos G) h).elim },
  { exact or.inr h }
end

@[simp] lemma not_equiv_zero_iff (G : pgame) [G.impartial] : ¬ G ≈ 0 ↔ G ∥ 0 :=
⟨(equiv_or_fuzzy_zero G).resolve_left, fuzzy.not_equiv⟩

@[simp] lemma not_fuzzy_zero_iff (G : pgame) [G.impartial] : ¬ G ∥ 0 ↔ G ≈ 0 :=
⟨(equiv_or_fuzzy_zero G).resolve_right, equiv.not_fuzzy⟩

lemma add_self (G : pgame) [G.impartial] : G + G ≈ 0 :=
equiv_trans (add_congr_left (neg_equiv_self G)) (add_left_neg_equiv G)

lemma equiv_iff_sum_equiv_zero (G H : pgame) [G.impartial] [H.impartial] :
  G ≈ H ↔ G + H ≈ 0 :=
begin
  rw @add_congr_iff_left G H (-H),
end

lemma le_zero_iff {G : pgame} [G.impartial] : G ≤ 0 ↔ 0 ≤ G :=
by rw [←zero_le_neg_iff, le_congr_right (neg_equiv_self G)]

lemma lf_zero_iff {G : pgame} [G.impartial] : G ⧏ 0 ↔ 0 ⧏ G :=
by rw [←zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]

lemma first_loses_symm (G : pgame) [G.impartial] : G.first_loses ↔ G ≤ 0 :=
⟨and.left, λ h, ⟨h, le_zero_iff.1 h⟩⟩

lemma first_wins_symm (G : pgame) [G.impartial] : G.first_wins ↔ G ⧏ 0 :=
⟨and.left, λ h, ⟨h, lf_zero_iff.1 h⟩⟩

lemma first_loses_symm' (G : pgame) [G.impartial] : G.first_loses ↔ 0 ≤ G :=
⟨and.right, λ h, ⟨le_zero_iff.2 h, h⟩⟩

lemma first_wins_symm' (G : pgame) [G.impartial] : G.first_wins ↔ 0 ⧏ G :=
⟨and.right, λ h, ⟨lf_zero_iff.2 h, h⟩⟩

lemma no_good_left_moves_iff_first_loses (G : pgame) [G.impartial] :
  (∀ (i : G.left_moves), (G.move_left i).first_wins) ↔ G.first_loses :=
begin
  refine ⟨λ hb, _, λ hp i, _⟩,
  { rw [first_loses_symm G, le_iff_forall_lf],
    exact ⟨λ i, (hb i).1, is_empty_elim⟩ },
  { rw first_wins_symm,
    exact (le_iff_forall_lf.1 $ (first_loses_symm G).1 hp).1 i }
end

lemma no_good_right_moves_iff_first_loses (G : pgame) [G.impartial] :
  (∀ (j : G.right_moves), (G.move_right j).first_wins) ↔ G.first_loses :=
begin
  rw [first_loses_of_equiv_iff (neg_equiv_self G), ←no_good_left_moves_iff_first_loses],
  refine ⟨λ h i, _, λ h i, _⟩,
  { rw [move_left_neg',
      ←first_wins_of_equiv_iff (neg_equiv_self (G.move_right (to_left_moves_neg.symm i)))],
    apply h },
  { rw [move_right_neg_symm',
      ←first_wins_of_equiv_iff (neg_equiv_self ((-G).move_left (to_left_moves_neg i)))],
    apply h }
end

lemma good_left_move_iff_first_wins (G : pgame) [G.impartial] :
  (∃ (i : G.left_moves), (G.move_left i).first_loses) ↔ G.first_wins :=
begin
  refine ⟨λ ⟨i, hi⟩, (first_wins_symm' G).2 (lf_of_forall_le $ or.inl ⟨i, hi.2⟩), λ hn, _⟩,
  rw [first_wins_symm' G, lf_iff_forall_le] at hn,
  rcases hn with ⟨i, hi⟩ | ⟨j, _⟩,
  { exact ⟨i, (first_loses_symm' _).2 hi⟩ },
  { exact pempty.elim j }
end

lemma good_right_move_iff_first_wins (G : pgame) [G.impartial] :
  (∃ j : G.right_moves, (G.move_right j).first_loses) ↔ G.first_wins :=
begin
  refine ⟨λ ⟨j, hj⟩, (first_wins_symm G).2 (lf_of_forall_le $ or.inr ⟨j, hj.1⟩), λ hn, _⟩,
  rw [first_wins_symm G, lf_iff_forall_le] at hn,
  rcases hn with ⟨i, _⟩ | ⟨j, hj⟩,
  { exact pempty.elim i },
  { exact ⟨j, (first_loses_symm _).2 hj⟩ }
end

end impartial
end pgame
