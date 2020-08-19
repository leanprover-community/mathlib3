/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.game.position
import tactic.nth_rewrite.default
import tactic

universe u

/-!
# Basic deinitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivilent to its negitve,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/

namespace pgame

local infix ` ≈ ` := equiv

/-- The definiton for a impartial game, defined using Conway induction -/
def impartial : pgame → Prop
| G := G ≈ -G ∧ (∀ i, impartial (G.move_left i)) ∧ (∀ j, impartial (G.move_right j))
using_well_founded {dec_tac := pgame_wf_tac}

lemma zero_impartial : impartial 0 := by tidy

lemma impartial_def {G : pgame} :
  G.impartial ↔ G ≈ -G ∧ (∀ i, impartial (G.move_left i)) ∧ (∀ j, impartial (G.move_right j)) :=
begin
  split,
  { intro hi,
    unfold1 impartial at hi,
    exact hi },
  { intro hi,
    unfold1 impartial,
    exact hi }
end

lemma impartial_neg_equiv_self {G : pgame} (h : G.impartial) : G ≈ -G := (impartial_def.1 h).1

lemma impartial_move_left_impartial {G : pgame} (h : G.impartial) (i : G.left_moves) :
  impartial (G.move_left i) :=
(impartial_def.1 h).2.1 i

lemma impartial_move_right_impartial {G : pgame} (h : G.impartial) (j : G.right_moves) :
  impartial (G.move_right j) :=
(impartial_def.1 h).2.2 j

lemma impartial_add : ∀ {G H : pgame}, G.impartial → H.impartial → (G + H).impartial
| G H :=
begin
  intros hG hH,
  rw impartial_def,
  split,
  { apply equiv_trans _ (equiv_of_relabelling (neg_add_relabelling G H)).symm,
    apply add_congr,
    exact impartial_neg_equiv_self hG,
    exact impartial_neg_equiv_self hH },
    split,
  { intro i,
    equiv_rw pgame.left_moves_add G H at i,
    cases i with iG iH,
    { rw add_move_left_inl,
      exact impartial_add (impartial_move_left_impartial hG _) hH },
    { rw add_move_left_inr,
      exact impartial_add hG (impartial_move_left_impartial hH _) } },
  { intro j,
    equiv_rw pgame.right_moves_add G H at j,
    cases j with jG jH,
    { rw add_move_right_inl,
      exact impartial_add (impartial_move_right_impartial hG _) hH },
    { rw add_move_right_inr,
      exact impartial_add hG (impartial_move_right_impartial hH _) } }
end
using_well_founded {dec_tac := pgame_wf_tac}

lemma impartial_neg : ∀ {G : pgame}, G.impartial → (-G).impartial
| G :=
begin
  intro hG,
  rw impartial_def,
  split,
  { rw neg_neg,
    symmetry,
    exact impartial_neg_equiv_self hG },
  split,
  { intro i,
    equiv_rw G.left_moves_neg at i,
    rw move_left_left_moves_neg_symm,
    exact impartial_neg (impartial_move_right_impartial hG _) },
  { intro j,
    equiv_rw G.right_moves_neg at j,
    rw move_right_right_moves_neg_symm,
    exact impartial_neg (impartial_move_left_impartial hG _) }
end
using_well_founded {dec_tac := pgame_wf_tac}

lemma impartial_position_cases {G : pgame} (hG : G.impartial) : G.p_position ∨ G.n_position :=
begin
  rcases G.position_cases with hl | hr | hp | hn,
  { cases hl with hpos hnonneg,
    rw ←not_lt at hnonneg,
    have hneg := lt_of_lt_of_equiv hpos (impartial_neg_equiv_self hG),
    rw [lt_iff_neg_gt, neg_neg, neg_zero] at hneg,
    contradiction },
  { cases hr with hnonpos hneg,
    rw ←not_lt at hnonpos,
    have hpos := lt_of_equiv_of_lt (impartial_neg_equiv_self hG).symm hneg,
    rw [lt_iff_neg_gt, neg_neg, neg_zero] at hpos,
    contradiction },
  { left, assumption },
  { right, assumption }
end

lemma impartial_add_self {G : pgame} (hG : G.impartial) : (G + G).p_position :=
p_position_is_zero.2 $ equiv_trans (add_congr (impartial_neg_equiv_self hG) G.equiv_refl) add_left_neg_equiv

lemma equiv_iff_sum_p_position {G H : pgame} (hG : G.impartial) (hH : H.impartial) :
  G ≈ H ↔ (G + H).p_position :=
begin
  split,
  { intro heq,
    exact p_position_of_equiv (add_congr (equiv_refl _) heq) (impartial_add_self hG) },
  { intro hGHp,
    split,
    { rw le_iff_sub_nonneg,
      exact le_trans hGHp.2
        (le_trans add_comm_le $ le_of_le_of_equiv (le_refl _) $ add_congr (equiv_refl _)
         (impartial_neg_equiv_self hG)) },
    { rw le_iff_sub_nonneg,
      exact le_trans hGHp.2
        (le_of_le_of_equiv (le_refl _) $ add_congr (equiv_refl _) (impartial_neg_equiv_self hH)) } }
end

lemma impartial_p_position_symm {G : pgame} (hG : G.impartial) : G.p_position ↔ G ≤ 0 :=
begin
  use and.left,
  { intro hneg,
    use hneg,
    exact zero_le_iff_neg_le_zero.2 (le_of_equiv_of_le (impartial_neg_equiv_self hG).symm hneg) }
end

lemma impartial_n_position_symm {G : pgame} (hG : G.impartial) : G.n_position ↔ G < 0 :=
begin
  use and.right,
  { intro hneg,
    split,
    rw lt_iff_neg_gt,
    rw neg_zero,
    exact lt_of_equiv_of_lt (impartial_neg_equiv_self hG).symm hneg,
    exact hneg }
end

lemma impartial_p_position_symm' {G : pgame} (hG : G.impartial) : G.p_position ↔ 0 ≤ G :=
begin
  use and.right,
  { intro hpos,
    use le_zero_iff_zero_le_neg.2 (le_of_le_of_equiv hpos $ impartial_neg_equiv_self hG),
    exact hpos }
end

lemma impartial_n_position_symm' {G : pgame} (hG : G.impartial) : G.n_position ↔ 0 < G :=
begin
  use and.left,
  { intro hpos,
    use hpos,
    rw lt_iff_neg_gt,
    rw neg_zero,
    exact lt_of_lt_of_equiv hpos (impartial_neg_equiv_self hG) }
end

lemma no_good_left_moves_iff_p_position {G : pgame} (hG : G.impartial) :
  (∀ (i : G.left_moves), (G.move_left i).n_position) ↔ G.p_position :=
begin
  split,
  { intro hbad,
    rw [impartial_p_position_symm hG, le_def_lt],
    split,
    { intro i,
      specialize hbad i,
      exact hbad.2 },
    { intro j,
      exact pempty.elim j } },
  { intros hp i,
    rw impartial_n_position_symm (impartial_move_left_impartial hG _),
    exact (le_def_lt.1 $ (impartial_p_position_symm hG).1 hp).1 i }
end

lemma no_good_right_moves_iff_p_position {G : pgame} (hG : G.impartial) :
  (∀ (j : G.right_moves), (G.move_right j).n_position) ↔ G.p_position :=
begin
  split,
  { intro hbad,
    rw [impartial_p_position_symm' hG, le_def_lt],
    split,
    { intro i,
      exact pempty.elim i },
    { intro j,
      specialize hbad j,
      exact hbad.1 } },
  { intros hp j,
    rw impartial_n_position_symm' (impartial_move_right_impartial hG _),
    exact ((le_def_lt.1 $ (impartial_p_position_symm' hG).1 hp).2 j) }
end

lemma good_left_move_iff_n_position {G : pgame} (hG : G.impartial) :
  (∃ (i : G.left_moves), (G.move_left i).p_position) ↔ G.n_position :=
begin
  split,
  { rintro ⟨ i, hi ⟩,
    exact (impartial_n_position_symm' hG).2 (lt_def_le.2 $ or.inl ⟨ i, hi.2 ⟩) },
  { intro hn,
    rw [impartial_n_position_symm' hG, lt_def_le] at hn,
    rcases hn with ⟨ i, hi ⟩ | ⟨ j, _ ⟩,
    { exact ⟨ i, (impartial_p_position_symm' $ impartial_move_left_impartial hG _).2 hi ⟩ },
    { exact pempty.elim j } }
end

lemma good_right_move_iff_n_position {G : pgame} (hG : G.impartial) :
  (∃ j : G.right_moves, (G.move_right j).p_position) ↔ G.n_position :=
begin
  split,
  { rintro ⟨ j, hj ⟩,
    exact (impartial_n_position_symm hG).2 (lt_def_le.2 $ or.inr ⟨ j, hj.1 ⟩) },
  { intro hn,
    rw [impartial_n_position_symm hG, lt_def_le] at hn,
    rcases hn with ⟨ i, _ ⟩ | ⟨ j, hj ⟩,
    { exact pempty.elim i },
    { exact ⟨ j, (impartial_p_position_symm $ impartial_move_right_impartial hG _).2 hj ⟩ } }
end

end pgame
