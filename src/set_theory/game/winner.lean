/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.game.pgame

/-!
# Basic definitions about who has a winning stratergy

We define `G.first_loses`, `G.first_wins`, `G.left_wins` and `G.right_wins` for a pgame `G`, which
means the second, first, left and right players have a winning strategy respectively.
These are defined by inequalities which can be unfolded with `pgame.lt_def` and `pgame.le_def`.
-/

namespace pgame

local infix ` ≈ ` := equiv
local infix ` ⧏ `:50 := lf
local infix ` ∥ `:50 := fuzzy

/-- The player who goes first loses -/
def first_loses (G : pgame) : Prop := G ≈ 0

/-- The player who goes first wins -/
def first_wins (G : pgame) : Prop := G ∥ 0

/-- The left player can always win -/
def left_wins (G : pgame) : Prop := 0 < G

/-- The right player can always win -/
def right_wins (G : pgame) : Prop := G < 0

theorem zero_first_loses : first_loses 0 := equiv_rfl
theorem one_left_wins : left_wins 1 := zero_lt_one

theorem star_first_wins : first_wins star := star_fuzzy_zero

lemma winner_cases (G : pgame) : G.right_wins ∨ G.first_loses ∨ G.left_wins ∨ G.first_wins :=
lt_or_equiv_or_gt_or_fuzzy G 0

lemma first_loses_is_zero {G : pgame} : G.first_loses ↔ G ≈ 0 := by refl

lemma first_loses_of_equiv {G H : pgame} (h : G ≈ H) : G.first_loses → H.first_loses :=
equiv_trans $ equiv_symm h
lemma first_wins_of_equiv {G H : pgame} (h : G ≈ H) : G.first_wins → H.first_wins :=
(fuzzy_congr_left h).1
lemma left_wins_of_equiv {G H : pgame} (h : G ≈ H) : G.left_wins → H.left_wins :=
(lt_congr_right h).1
lemma right_wins_of_equiv {G H : pgame} (h : G ≈ H) : G.right_wins → H.right_wins :=
(lt_congr_left h).1

lemma first_loses_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.first_loses ↔ H.first_loses :=
⟨first_loses_of_equiv h, equiv_trans h⟩
lemma first_wins_of_equiv_iff {G H : pgame} : G ≈ H → (G.first_wins ↔ H.first_wins) :=
fuzzy_congr_left
lemma left_wins_of_equiv_iff {G H : pgame} : G ≈ H → (G.left_wins ↔ H.left_wins) :=
lt_congr_right
lemma right_wins_of_equiv_iff {G H : pgame} : G ≈ H → (G.right_wins ↔ H.right_wins) :=
lt_congr_left

lemma not_first_wins_of_first_loses {G : pgame} : G.first_loses → ¬G.first_wins :=
equiv.not_fuzzy

lemma not_first_loses_of_first_wins {G : pgame} : G.first_wins → ¬G.first_loses :=
fuzzy.not_equiv

end pgame
