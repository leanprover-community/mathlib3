/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.arithmetic
import set_theory.game.pgame

/-!
# Birthdays of games

We define the birthday of a pre-game recursively, as the least ordinal larger than the birthdays of
its left and right games. We prove the basic properties about these.

# Todo

- Define the birthdays of `game`s and `surreal`s.
- Characterize the birthdays of basic arithmetical operations.
-/

universe u

/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def birthday : pgame.{u} → ordinal.{u}
| ⟨xl, xr, xL, xR⟩ :=
    max (ordinal.lsub.{u u} $ λ i, birthday (xL i)) (ordinal.lsub.{u u} $ λ i, birthday (xR i))

theorem birthday_def (x : pgame) : birthday x = max
  (ordinal.lsub.{u u} (λ i, birthday (x.move_left i)))
  (ordinal.lsub.{u u} (λ i, birthday (x.move_right i))) :=
by { cases x, rw birthday, refl }

theorem birthday_move_left_lt {x : pgame} (i : x.left_moves) :
  (x.move_left i).birthday < x.birthday :=
by { cases x, rw birthday, exact lt_max_of_lt_left (ordinal.lt_lsub _ i) }

theorem birthday_move_right_lt {x : pgame} (i : x.right_moves) :
  (x.move_right i).birthday < x.birthday :=
by { cases x, rw birthday, exact lt_max_of_lt_right (ordinal.lt_lsub _ i) }

theorem lt_birthday_iff {x : pgame} {o : ordinal} : o < x.birthday ↔
  (∃ i : x.left_moves, o ≤ (x.move_left i).birthday) ∨
  (∃ i : x.right_moves, o ≤ (x.move_right i).birthday) :=
begin
  split,
  { rw birthday_def,
    intro h,
    cases lt_max_iff.1 h with h' h',
    { left,
      rwa ordinal.lt_lsub_iff at h' },
    { right,
      rwa ordinal.lt_lsub_iff at h' } },
  { rintro (⟨i, hi⟩ | ⟨i, hi⟩),
    { exact hi.trans_lt (birthday_move_left_lt i) },
    { exact hi.trans_lt (birthday_move_right_lt i) } }
end

theorem relabelling.birthday_congr : ∀ {x y : pgame.{u}}, relabelling x y → birthday x = birthday y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨L, R, hL, hR⟩ := begin
  rw [birthday, birthday],
  congr' 1,
  all_goals
  { apply ordinal.lsub_eq_of_range_eq.{u u u},
    ext i,
    split },
  { rintro ⟨j, rfl⟩,
    exact ⟨L j, (relabelling.birthday_congr (hL j)).symm⟩ },
  { rintro ⟨j, rfl⟩,
    refine ⟨L.symm j, relabelling.birthday_congr _⟩,
    convert hL (L.symm j),
    rw L.apply_symm_apply },
  { rintro ⟨j, rfl⟩,
    refine ⟨R j, (relabelling.birthday_congr _).symm⟩,
    convert hR (R j),
    rw R.symm_apply_apply },
  { rintro ⟨j, rfl⟩,
    exact ⟨R.symm j, relabelling.birthday_congr (hR j)⟩ }
end
using_well_founded { dec_tac := pgame_wf_tac }

@[simp] theorem birthday_zero : birthday 0 = 0 :=
by rw [birthday_def, ordinal.lsub_empty, ordinal.lsub_empty, max_self]
