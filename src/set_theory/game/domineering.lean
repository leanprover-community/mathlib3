/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Domineering as a combinatorial game.
-/
import set_theory.game.short
import tactic.norm_num
import tactic.tidy

open pgame

namespace domineering_aux

def shift_up : ℤ × ℤ ↪ ℤ × ℤ := ⟨λ p : ℤ × ℤ, (p.1, p.2 + 1), sorry⟩
def shift_right : ℤ × ℤ ↪ ℤ × ℤ := ⟨λ p : ℤ × ℤ, (p.1 + 1, p.2), sorry⟩

def left_set  (b : finset (ℤ × ℤ)) : finset (ℤ × ℤ) := b ∩ b.map shift_up
def right_set (b : finset (ℤ × ℤ)) : finset (ℤ × ℤ) := b ∩ b.map shift_right

def left  (b : finset (ℤ × ℤ)) : Type := { p | p ∈ left_set b }
def right (b : finset (ℤ × ℤ)) : Type := { p | p ∈ right_set b }

instance fintype_left (b : finset (ℤ × ℤ)) : fintype (left b) :=
fintype.subtype _ (λ x, iff.refl _)

instance fintype_right (b : finset (ℤ × ℤ)) : fintype (right b) :=
fintype.subtype _ (λ x, iff.refl _)

def move_left (b : finset (ℤ × ℤ)) (m : left b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1, m.val.2 - 1)
def move_right (b : finset (ℤ × ℤ)) (m : right b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1 - 1, m.val.2)

lemma int.succ_ne_self {x : ℤ} : x + 1 ≠ x :=
begin
  sorry
end

lemma move_left_smaller (b : finset (ℤ × ℤ)) (m : left b) :
  finset.card (move_left b m) < finset.card b :=
begin
  dsimp [move_left],
  rcases m with ⟨⟨x,y⟩,p⟩,
  dsimp,
  dsimp [left_set] at p,
  simp at p,
  cases p with p₁ p₂,
  dsimp [shift_up] at p₂,
  simp at p₂,
  rcases p₂ with ⟨x,y,⟨p,rfl,rfl⟩⟩,
  rw finset.card_erase_of_mem,
  rw finset.card_erase_of_mem,
  { apply lt_of_le_of_lt (nat.pred_le _),
    exact nat.pred_lt (finset.card_ne_zero_of_mem p₁), },
  { exact p₁ },
  apply finset.mem_erase_of_ne_of_mem _ _,
  { intro h,
    replace h := congr_arg prod.snd h,
    dsimp at h,
    simp at h,
    apply (int.succ_ne_self h.symm), },
  { simpa using p },
end
lemma move_right_smaller (b : finset (ℤ × ℤ)) (m : right b) :
  finset.card (move_right b m) < finset.card b :=
begin
  dsimp [move_right],
  rcases m with ⟨⟨x,y⟩,p⟩,
  dsimp,
  dsimp [right_set] at p,
  simp at p,
  cases p with p₁ p₂,
  dsimp [shift_right] at p₂,
  simp at p₂,
  rcases p₂ with ⟨x,y,⟨p,rfl,rfl⟩⟩,
  rw finset.card_erase_of_mem,
  rw finset.card_erase_of_mem,
  { apply lt_of_le_of_lt (nat.pred_le _),
    exact nat.pred_lt (finset.card_ne_zero_of_mem p₁), },
  { exact p₁ },
  apply finset.mem_erase_of_ne_of_mem _ _,
  { intro h,
    replace h := congr_arg prod.fst h,
    dsimp at h,
    simp at h,
    apply (int.succ_ne_self h.symm), },
  { simpa using p },
end

end domineering_aux


section
open domineering_aux

instance : has_well_founded (finset (ℤ × ℤ)) := ⟨measure finset.card, measure_wf finset.card⟩

def domineering : finset (ℤ × ℤ) → pgame
| b := pgame.mk
    (left b) (right b)
    (λ m, have _, from move_left_smaller b m,  domineering (move_left b m))
    (λ m, have _, from move_right_smaller b m, domineering (move_right b m))

@[simp] lemma domineering_left_moves (b : finset (ℤ × ℤ)) :
  (domineering b).left_moves = left b :=
by { rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩; refl }
@[simp] lemma domineering_right_moves (b : finset (ℤ × ℤ)) :
  (domineering b).right_moves = right b :=
by { rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩; refl }
@[simp] lemma domineering_move_left (b : finset (ℤ × ℤ)) (i : left_moves (domineering b)):
  (domineering b).move_left i = domineering (move_left b (by { convert i, simp })) :=
begin
  rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩,
  { dsimp, rcases i with ⟨i, ⟨⟩⟩, },
  { refl }
end
@[simp] lemma domineering_move_right (b : finset (ℤ × ℤ)) (j : right_moves (domineering b)):
  (domineering b).move_right j = domineering (move_right b (by { convert j, simp })) :=
begin
  rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩,
  { dsimp, rcases j with ⟨j, ⟨⟩⟩, },
  { refl }
end

instance fintype_left_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).left_moves) :=
begin
  rw domineering_left_moves,
  exact domineering_aux.fintype_left b,
end
instance fintype_right_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).right_moves) :=
begin
  rw domineering_right_moves,
  exact domineering_aux.fintype_right b,
end

instance short_domineering : Π (b : finset (ℤ × ℤ)), short (domineering b)
| b :=
@short.mk (domineering b) (by apply_instance) (by apply_instance)
(λ i, begin
  simp only [domineering_move_left, domineering_left_moves],
  exact have _, from move_left_smaller b (by { convert i, simp }), short_domineering (move_left b _),
end)
(λ j, begin
  simp only [domineering_move_right, domineering_right_moves],
  exact have _, from move_right_smaller b (by { convert j, simp }), short_domineering (move_right b _),
end)

def domineering.L := domineering ([(0,2), (0,1), (0,0), (1,0)].to_finset)

instance : short domineering.L := by { dsimp [domineering.L], apply_instance}

-- The VM can play small games successfully:
-- #eval to_bool (domineering.L + domineering.L ≈ 1)

-- Unfortunately dec_trivial can't keep up:
-- example : domineering.L + domineering.L ≈ 1 := dec_trivial

instance : short (pgame.of_lists [0] [1]) :=
@pgame.short_of_lists [0] [1]
begin
 intros l h, simp at h, subst h, apply_instance
end
begin
 intros l h, simp at h, subst h, apply_instance
end

#eval to_bool (domineering.L ≈ pgame.of_lists [0] [1])

theorem L_left_moves : domineering.L.left_moves = { p | p ∈ [(0, 2), (0, 1)].to_finset } := sorry
theorem L_right_moves : domineering.L.right_moves = { p | p ∈ [(1, 0)].to_finset } := sorry

local infix ` ≈ ` := pgame.equiv

theorem L_move_left_0_2 : domineering.L.move_left ⟨(0, 2), sorry⟩ ≈ -1 :=
calc domineering.L.move_left ⟨(0, 2), sorry⟩ ≈ domineering ([(0,0), (1,0)].to_finset) : sorry
     ... ≈ -1 : sorry
theorem L_move_left_0_1 : domineering.L.move_left ⟨(0, 1), sorry⟩ ≈ 0 := sorry
theorem L_move_right_1_0 : domineering.L.move_right ⟨(1, 0), sorry⟩ ≈ 1 := sorry

theorem domineering.L_eq_half' : domineering.L ≈ pgame.of_lists [-1, 0] [1] :=
sorry

theorem domineering.L_eq_half : domineering.L ≈ pgame.of_lists [0] [1] :=
sorry
end

end
