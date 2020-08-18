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
@[class] def impartial : pgame → Prop
| G := G ≈ -G ∧ (∀ i, impartial (G.move_left i)) ∧ (∀ j, impartial (G.move_right j))
using_well_founded {dec_tac := pgame_wf_tac}

@[instance] lemma zero_impartial : impartial 0 := by tidy

@[simp] lemma impartial_def {G : pgame} : G.impartial ↔ G ≈ -G ∧ (∀ i, impartial (G.move_left i)) ∧ (∀ j, impartial (G.move_right j)) :=
begin
	split,
	{	intro hi,
		unfold1 impartial at hi,
		exact hi },
	{	intro hi,
		unfold1 impartial,
		exact hi }
end

lemma impartial_neg_equiv_self (G : pgame) [h : G.impartial] : G ≈ -G := (impartial_def.1 h).1

@[instance] lemma impartial_move_left_impartial {G : pgame} [h : G.impartial] (i : G.left_moves) : impartial (G.move_left i) :=
(impartial_def.1 h).2.1 i

@[instance] lemma impartial_move_right_impartial {G : pgame} [h : G.impartial] (j : G.right_moves) : impartial (G.move_right j) :=
(impartial_def.1 h).2.2 j

@[instance] lemma impartial_add : ∀ (G H : pgame) [hG : G.impartial] [hH : H.impartial], (G + H).impartial
| G H :=
begin
	introsI hG hH,
	rw impartial_def,
	split,
	{	apply equiv_trans _ (equiv_of_relabelling (neg_add_relabelling G H)).symm,
		apply add_congr;
		exact impartial_neg_equiv_self _	},
	split,
	{ intro i,
		equiv_rw pgame.left_moves_add G H at i,
		cases i with iG iH,
		{	rw add_move_left_inl,
			exact impartial_add (G.move_left iG) H },
		{ rw add_move_left_inr,
			exact impartial_add G (H.move_left iH) } },
	{ intro j,
		equiv_rw pgame.right_moves_add G H at j,
		cases j with jG jH,
		{ rw add_move_right_inl,
			exact impartial_add (G.move_right jG) H },
		{ rw add_move_right_inr,
			exact impartial_add G (H.move_right jH) } }
end
using_well_founded {dec_tac := pgame_wf_tac}

@[instance] lemma impartial_neg : ∀ (G : pgame) [G.impartial], (-G).impartial
| G :=
begin
	introI,
	rw impartial_def,
	split,
	{	rw neg_neg,
		symmetry,
		exact impartial_neg_equiv_self G },
	split,
	{ intro i,
		equiv_rw G.left_moves_neg at i,
		rw move_left_left_moves_neg_symm,
		exact impartial_neg (G.move_right i) },
	{ intro j,
		equiv_rw G.right_moves_neg at j,
		rw move_right_right_moves_neg_symm,
		exact impartial_neg (G.move_left j) }
end
using_well_founded {dec_tac := pgame_wf_tac}

lemma impartial_position_cases (G : pgame) [G.impartial] : G.p_position ∨ G.n_position :=
begin
  rcases G.position_cases with hl | hr | hp | hn,
  { cases hl with hpos hnonneg,
		rw ←not_lt at hnonneg,
		have hneg := lt_of_lt_of_equiv hpos G.impartial_neg_equiv_self,
		rw [lt_iff_neg_gt, neg_neg, neg_zero] at hneg,
		contradiction },
	{ cases hr with hnonpos hneg,
		rw ←not_lt at hnonpos,
		have hpos := lt_of_equiv_of_lt G.impartial_neg_equiv_self.symm hneg,
		rw [lt_iff_neg_gt, neg_neg, neg_zero] at hpos,
		contradiction },
	{ left, assumption },
	{ right, assumption }
end

lemma impartial_add_self (G : pgame) [G.impartial] : (G + G).p_position :=
p_position_is_zero.2 $ equiv_trans (add_congr G.impartial_neg_equiv_self G.equiv_refl) add_left_neg_equiv

/-- A different way of viewing equivalence. -/
def additive_equiv (G H : pgame) [G.impartial] [H.impartial] : Prop :=
	∀ (F : pgame) [F.impartial], (G + F).p_position ↔ (H + F).p_position

lemma additive_equiv_equiv_equiv (G H : pgame) [hG : G.impartial] [hH : H.impartial] : G.additive_equiv H ↔ G ≈ H :=
begin
	split,
	{ intro heq,
		cases G.impartial_position_cases with hGp hGn,
		{ specialize heq 0,
			rw [p_position_of_equiv_iff G.add_zero_equiv, p_position_of_equiv_iff H.add_zero_equiv, p_position_is_zero, p_position_is_zero] at heq,
			rw p_position_is_zero at hGp,
			exact equiv_trans hGp (heq.1 hGp).symm },
		{ split,
			{ rw le_iff_sub_nonneg,
				specialize heq (-G),
				rw [p_position_of_equiv_iff add_comm_equiv, p_position_of_equiv_iff add_left_neg_equiv] at heq,
				exact (heq.1 zero_p_postition).2 },
			{ rw le_iff_sub_nonneg,
				specialize heq (-H),
				nth_rewrite 1 p_position_of_equiv_iff add_comm_equiv at heq,
				rw p_position_of_equiv_iff add_left_neg_equiv at heq,
				exact (heq.2 zero_p_postition).2 } } },
	{ intros heq F hf,
		rw [p_position_is_zero, p_position_is_zero],
		split,
		{ intro hGF,
			exact equiv_trans (add_congr heq.symm $ equiv_refl _) hGF },
		{ intro hHF,
			exact equiv_trans (add_congr heq $ equiv_refl _) hHF } }
end

lemma equiv_iff_sum_p_position (G H : pgame) [G.impartial] [H.impartial] : G ≈ H ↔ (G + H).p_position :=
begin
	split,
	{ intro heq,
		exact p_position_of_equiv (add_congr (equiv_refl _) heq) G.impartial_add_self },
	{ intro hGHp,
		split,
		{ rw le_iff_sub_nonneg,
			exact le_trans hGHp.2 (le_trans add_comm_le $ le_of_le_of_equiv (le_refl _) $ add_congr (equiv_refl _) G.impartial_neg_equiv_self) },
		{ rw le_iff_sub_nonneg,
			exact le_trans hGHp.2 (le_of_le_of_equiv (le_refl _) $ add_congr (equiv_refl _) H.impartial_neg_equiv_self) } }
end

lemma impartial_p_position_symm (G : pgame) [G.impartial] : G.p_position ↔ G ≤ 0 :=
begin
	use and.left,
	{ intro hneg,
		exact ⟨ hneg, zero_le_iff_neg_le_zero.2 (le_of_equiv_of_le (impartial_neg_equiv_self G).symm hneg) ⟩ }
end

lemma impartial_n_position_symm (G : pgame) [G.impartial] : G.n_position ↔ G < 0 :=
begin
	use and.right,
	{ intro hneg,
		split,
		rw lt_iff_neg_gt,
		rw neg_zero,
		exact lt_of_equiv_of_lt G.impartial_neg_equiv_self.symm hneg,
		exact hneg }
end

lemma impartial_p_position_symm' (G : pgame) [G.impartial] : G.p_position ↔ 0 ≤ G :=
begin
	use and.right,
	{ intro hpos,
		exact ⟨ le_zero_iff_zero_le_neg.2 $ le_of_le_of_equiv hpos G.impartial_neg_equiv_self, hpos ⟩ }
end

lemma impartial_n_position_symm' (G : pgame) [G.impartial] : G.n_position ↔ 0 < G :=
begin
	use and.left,
	{ intro hpos,
		use hpos,
		rw lt_iff_neg_gt,
		rw neg_zero,
		exact lt_of_lt_of_equiv hpos G.impartial_neg_equiv_self }
end

lemma no_good_left_moves_iff_p_position (G : pgame) [G.impartial] : (∀ (i : G.left_moves), (G.move_left i).n_position) ↔ G.p_position :=
begin
	split,
	{	intro hbad,
		rw [impartial_p_position_symm, le_def_lt],
		split,
		{ intro i,
			specialize hbad i,
			exact hbad.2 },
		{ intro j,
			exact pempty.elim j } },
	{ intros hp i,
		exact (G.move_left i).impartial_n_position_symm.2 ((le_def_lt.1 $ G.impartial_p_position_symm.1 hp).1 i) }
end

lemma no_good_right_moves_iff_p_position (G : pgame) [G.impartial] : (∀ (j : G.right_moves), (G.move_right j).n_position) ↔ G.p_position :=
begin
	split,
	{ intro hbad,
		rw [impartial_p_position_symm', le_def_lt],
		split,
		{ intro i,
			exact pempty.elim i },
		{ intro j,
			specialize hbad j,
			exact hbad.1 } },
	{ intros hp j,
		exact (G.move_right j).impartial_n_position_symm'.2 ((le_def_lt.1 $ G.impartial_p_position_symm'.1 hp).2 j) }
end

lemma good_left_move_iff_n_position (G : pgame) [G.impartial] : (∃ (i : G.left_moves), (G.move_left i).p_position) ↔ G.n_position :=
begin
	split,
	{ rintro ⟨ i, hi ⟩,
		exact G.impartial_n_position_symm'.2 (lt_def_le.2 $ or.inl ⟨ i, hi.2 ⟩) },
	{ intro hn,
		rw [impartial_n_position_symm', lt_def_le] at hn,
		rcases hn with ⟨ i, hi ⟩ | ⟨ j, _ ⟩,
		{ exact ⟨ i, (G.move_left i).impartial_p_position_symm'.2 hi ⟩ },
		{ exact pempty.elim j } }
end

lemma good_right_move_iff_n_position (G : pgame) [G.impartial] : (∃ j : G.right_moves,  (G.move_right j).p_position) ↔ G.n_position :=
begin
	split,
	{ rintro ⟨ j, hj ⟩,
		exact G.impartial_n_position_symm.2 (lt_def_le.2 $ or.inr ⟨ j, hj.1 ⟩) },
	{ intro hn,
		rw [impartial_n_position_symm, lt_def_le] at hn,
		rcases hn with ⟨ i, _ ⟩ | ⟨ j, hj ⟩,
		{ exact pempty.elim i },
		{ exact ⟨ j, (G.move_right j).impartial_p_position_symm.2 hj ⟩ } }
end

end pgame
