/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import set_theory.game.state

/-!
# Domineering as a combinatorial game.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/

namespace pgame

namespace domineering

open function

/-- The equivalence `(x, y) ↦ (x, y+1)`. -/
@[simps]
def shift_up : ℤ × ℤ ≃ ℤ × ℤ :=
(equiv.refl ℤ).prod_congr (equiv.add_right (1 : ℤ))
/-- The equivalence `(x, y) ↦ (x+1, y)`. -/
@[simps]
def shift_right : ℤ × ℤ ≃ ℤ × ℤ :=
(equiv.add_right (1 : ℤ)).prod_congr (equiv.refl ℤ)

/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
@[derive inhabited]
def board := finset (ℤ × ℤ)
local attribute [reducible] board

/-- Left can play anywhere that a square and the square below it are open. -/
def left  (b : board) : finset (ℤ × ℤ) := b ∩ b.map shift_up
/-- Right can play anywhere that a square and the square to the left are open. -/
def right (b : board) : finset (ℤ × ℤ) := b ∩ b.map shift_right

lemma mem_left {b : board} (x : ℤ × ℤ) : x ∈ left b ↔ x ∈ b ∧ (x.1, x.2 - 1) ∈ b :=
finset.mem_inter.trans (and_congr iff.rfl finset.mem_map_equiv)

lemma mem_right {b : board} (x : ℤ × ℤ) : x ∈ right b ↔ x ∈ b ∧ (x.1 - 1, x.2) ∈ b :=
finset.mem_inter.trans (and_congr iff.rfl finset.mem_map_equiv)

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def move_left (b : board) (m : ℤ × ℤ) : board :=
(b.erase m).erase (m.1, m.2 - 1)
/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def move_right (b : board) (m : ℤ × ℤ) : board :=
(b.erase m).erase (m.1 - 1, m.2)

lemma fst_pred_mem_erase_of_mem_right {b : board} {m : ℤ × ℤ} (h : m ∈ right b) :
  (m.1 - 1, m.2) ∈ b.erase m :=
begin
  rw mem_right at h,
  apply finset.mem_erase_of_ne_of_mem _ h.2,
  exact ne_of_apply_ne prod.fst (pred_ne_self m.1),
end

lemma snd_pred_mem_erase_of_mem_left {b : board} {m : ℤ × ℤ} (h : m ∈ left b) :
  (m.1, m.2 - 1) ∈ b.erase m :=
begin
  rw mem_left at h,
  apply finset.mem_erase_of_ne_of_mem _ h.2,
  exact ne_of_apply_ne prod.snd (pred_ne_self m.2),
end

lemma card_of_mem_left {b : board} {m : ℤ × ℤ} (h : m ∈ left b) : 2 ≤ finset.card b :=
begin
  have w₁ : m ∈ b := (finset.mem_inter.1 h).1,
  have w₂ : (m.1, m.2 - 1) ∈ b.erase m := snd_pred_mem_erase_of_mem_left h,
  have i₁ := finset.card_erase_lt_of_mem w₁,
  have i₂ := nat.lt_of_le_of_lt (nat.zero_le _) (finset.card_erase_lt_of_mem w₂),
  exact nat.lt_of_le_of_lt i₂ i₁,
end

lemma card_of_mem_right {b : board} {m : ℤ × ℤ} (h : m ∈ right b) : 2 ≤ finset.card b :=
begin
  have w₁ : m ∈ b := (finset.mem_inter.1 h).1,
  have w₂ := fst_pred_mem_erase_of_mem_right h,
  have i₁ := finset.card_erase_lt_of_mem w₁,
  have i₂ := nat.lt_of_le_of_lt (nat.zero_le _) (finset.card_erase_lt_of_mem w₂),
  exact nat.lt_of_le_of_lt i₂ i₁,
end

lemma move_left_card {b : board} {m : ℤ × ℤ} (h : m ∈ left b) :
  finset.card (move_left b m) + 2 = finset.card b :=
begin
  dsimp [move_left],
  rw finset.card_erase_of_mem (snd_pred_mem_erase_of_mem_left h),
  rw finset.card_erase_of_mem (finset.mem_of_mem_inter_left h),
  exact tsub_add_cancel_of_le (card_of_mem_left h),
end

lemma move_right_card {b : board} {m : ℤ × ℤ} (h : m ∈ right b) :
  finset.card (move_right b m) + 2 = finset.card b :=
begin
  dsimp [move_right],
  rw finset.card_erase_of_mem (fst_pred_mem_erase_of_mem_right h),
  rw finset.card_erase_of_mem (finset.mem_of_mem_inter_left h),
  exact tsub_add_cancel_of_le (card_of_mem_right h),
end

lemma move_left_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ left b) :
  finset.card (move_left b m) / 2 < finset.card b / 2 :=
by simp [←move_left_card h, lt_add_one]
lemma move_right_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ right b) :
  finset.card (move_right b m) / 2 < finset.card b / 2 :=
by simp [←move_right_card h, lt_add_one]

/-- The instance describing allowed moves on a Domineering board. -/
instance state : state board :=
{ turn_bound := λ s, s.card / 2,
  L := λ s, (left s).image (move_left s),
  R := λ s, (right s).image (move_right s),
  left_bound := λ s t m,
  begin
    simp only [finset.mem_image, prod.exists] at m,
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩,
    exact move_left_smaller h
  end,
  right_bound := λ s t m,
  begin
    simp only [finset.mem_image, prod.exists] at m,
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩,
    exact move_right_smaller h
  end, }

end domineering

/-- Construct a pre-game from a Domineering board. -/
def domineering (b : domineering.board) : pgame := pgame.of_state b

/-- All games of Domineering are short, because each move removes two squares. -/
instance short_domineering (b : domineering.board) : short (domineering b) :=
by { dsimp [domineering], apply_instance }

/-- The Domineering board with two squares arranged vertically, in which Left has the only move. -/
def domineering.one := domineering ([(0,0), (0,1)].to_finset)

/-- The `L` shaped Domineering board, in which Left is exactly half a move ahead. -/
def domineering.L := domineering ([(0,2), (0,1), (0,0), (1,0)].to_finset)

instance short_one : short domineering.one := by { dsimp [domineering.one], apply_instance }
instance short_L : short domineering.L := by { dsimp [domineering.L], apply_instance }

-- The VM can play small games successfully:
-- #eval to_bool (domineering.one ≈ 1)
-- #eval to_bool (domineering.L + domineering.L ≈ 1)

-- The following no longer works since Lean 3.29, since definitions by well-founded
-- recursion no longer reduce definitionally.

-- We can check that `decidable` instances reduce as expected,
-- and so our implementation of domineering is computable.
-- run_cmd tactic.whnf `(by apply_instance : decidable (domineering.one ≤ 1)) >>= tactic.trace

-- dec_trivial can handle most of the dictionary of small games described in [conway2001]
-- example : domineering.one ≈ 1 := dec_trivial
-- example : domineering.L + domineering.L ≈ 1 := dec_trivial
-- example : domineering.L ≈ pgame.of_lists [0] [1] := dec_trivial
-- example : (domineering ([(0,0), (0,1), (0,2), (0,3)].to_finset) ≈ 2) := dec_trivial
-- example : (domineering ([(0,0), (0,1), (1,0), (1,1)].to_finset) ≈ pgame.of_lists [1] [-1]) :=
--   dec_trivial.

-- The 3x3 grid is doable, but takes a minute...
-- example :
--   (domineering ([(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)].to_finset) ≈
--     pgame.of_lists [1] [-1]) := dec_trivial

-- The 5x5 grid is actually 0, but brute-forcing this is too challenging even for the VM.
-- #eval to_bool (domineering ([
--   (0,0), (0,1), (0,2), (0,3), (0,4),
--   (1,0), (1,1), (1,2), (1,3), (1,4),
--   (2,0), (2,1), (2,2), (2,3), (2,4),
--   (3,0), (3,1), (3,2), (3,3), (3,4),
--   (4,0), (4,1), (4,2), (4,3), (4,4)
--   ].to_finset) ≈ 0)


end pgame
