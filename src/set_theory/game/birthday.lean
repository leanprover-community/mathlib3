/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.game.ordinal
import set_theory.ordinal.natural_ops

/-!
# Birthdays of games

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The birthday of a game is an ordinal that represents at which "step" the game was constructed. We
define it recursively as the least ordinal larger than the birthdays of its left and right games. We
prove the basic properties about these.

# Main declarations

- `pgame.birthday`: The birthday of a pre-game.

# Todo

- Define the birthdays of `game`s and `surreal`s.
- Characterize the birthdays of basic arithmetical operations.
-/

universe u

open ordinal

open_locale natural_ops pgame

namespace pgame

/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def birthday : pgame.{u} → ordinal.{u}
| ⟨xl, xr, xL, xR⟩ :=
    max (lsub.{u u} $ λ i, birthday (xL i)) (lsub.{u u} $ λ i, birthday (xR i))

theorem birthday_def (x : pgame) : birthday x = max
  (lsub.{u u} (λ i, birthday (x.move_left i)))
  (lsub.{u u} (λ i, birthday (x.move_right i))) :=
by { cases x, rw birthday, refl }

theorem birthday_move_left_lt {x : pgame} (i : x.left_moves) :
  (x.move_left i).birthday < x.birthday :=
by { cases x, rw birthday, exact lt_max_of_lt_left (lt_lsub _ i) }

theorem birthday_move_right_lt {x : pgame} (i : x.right_moves) :
  (x.move_right i).birthday < x.birthday :=
by { cases x, rw birthday, exact lt_max_of_lt_right (lt_lsub _ i) }

theorem lt_birthday_iff {x : pgame} {o : ordinal} : o < x.birthday ↔
  (∃ i : x.left_moves, o ≤ (x.move_left i).birthday) ∨
  (∃ i : x.right_moves, o ≤ (x.move_right i).birthday) :=
begin
  split,
  { rw birthday_def,
    intro h,
    cases lt_max_iff.1 h with h' h',
    { left,
      rwa lt_lsub_iff at h' },
    { right,
      rwa lt_lsub_iff at h' } },
  { rintro (⟨i, hi⟩ | ⟨i, hi⟩),
    { exact hi.trans_lt (birthday_move_left_lt i) },
    { exact hi.trans_lt (birthday_move_right_lt i) } }
end

theorem relabelling.birthday_congr : ∀ {x y : pgame.{u}}, x ≡r y → birthday x = birthday y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ r := begin
  unfold birthday,
  congr' 1,
  all_goals
  { apply lsub_eq_of_range_eq.{u u u},
    ext i, split },
  all_goals { rintro ⟨j, rfl⟩ },
  { exact ⟨_, (r.move_left j).birthday_congr.symm⟩ },
  { exact ⟨_, (r.move_left_symm j).birthday_congr⟩ },
  { exact ⟨_, (r.move_right j).birthday_congr.symm⟩ },
  { exact ⟨_, (r.move_right_symm j).birthday_congr⟩ }
end
using_well_founded { dec_tac := pgame_wf_tac }

@[simp] theorem birthday_eq_zero {x : pgame} :
  birthday x = 0 ↔ is_empty x.left_moves ∧ is_empty x.right_moves :=
by rw [birthday_def, max_eq_zero, lsub_eq_zero_iff, lsub_eq_zero_iff]

@[simp] theorem birthday_zero : birthday 0 = 0 :=
by simp [pempty.is_empty]

@[simp] theorem birthday_one : birthday 1 = 1 :=
by { rw birthday_def, simp }

@[simp] theorem birthday_star : birthday star = 1 :=
by { rw birthday_def, simp }

@[simp] theorem neg_birthday : ∀ x : pgame, (-x).birthday = x.birthday
| ⟨xl, xr, xL, xR⟩ := begin
  rw [birthday_def, birthday_def, max_comm],
  congr; funext; apply neg_birthday
end

@[simp] theorem to_pgame_birthday (o : ordinal) : o.to_pgame.birthday = o :=
begin
  induction o using ordinal.induction with o IH,
  rw [to_pgame_def, pgame.birthday],
  simp only [lsub_empty, max_zero_right],
  nth_rewrite 0 ←lsub_typein o,
  congr' with x,
  exact IH _ (typein_lt_self x)
end

theorem le_birthday : ∀ x : pgame, x ≤ x.birthday.to_pgame
| ⟨xl, _, xL, _⟩ :=
le_def.2 ⟨λ i, or.inl ⟨to_left_moves_to_pgame ⟨_, birthday_move_left_lt i⟩,
  by simp [le_birthday (xL i)]⟩, is_empty_elim⟩

variables (a b x : pgame.{u})

theorem neg_birthday_le : -x.birthday.to_pgame ≤ x :=
by simpa only [neg_birthday, ←neg_le_iff] using le_birthday (-x)

@[simp] theorem birthday_add : ∀ x y : pgame.{u}, (x + y).birthday = x.birthday ♯ y.birthday
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ := begin
  rw [birthday_def, nadd_def],
  simp only [birthday_add, lsub_sum, mk_add_move_left_inl, move_left_mk, mk_add_move_left_inr,
    mk_add_move_right_inl, move_right_mk, mk_add_move_right_inr],
  rw max_max_max_comm,
  congr; apply le_antisymm,
  any_goals
  { exact max_le_iff.2 ⟨lsub_le_iff.2 (λ i, lt_blsub _ _ (birthday_move_left_lt i)),
      lsub_le_iff.2 (λ i, lt_blsub _ _ (birthday_move_right_lt i))⟩ },
  all_goals
  { apply blsub_le_iff.2 (λ i hi, _),
    rcases lt_birthday_iff.1 hi with ⟨j, hj⟩ | ⟨j, hj⟩ },
  { exact lt_max_of_lt_left ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _)) },
  { exact lt_max_of_lt_right ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _)) },
  { exact lt_max_of_lt_left ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _)) },
  { exact lt_max_of_lt_right ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _)) }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem birthday_add_zero : (a + 0).birthday = a.birthday := by simp
theorem birthday_zero_add : (0 + a).birthday = a.birthday := by simp
theorem birthday_add_one  : (a + 1).birthday = order.succ a.birthday := by simp
theorem birthday_one_add  : (1 + a).birthday = order.succ a.birthday := by simp

@[simp] theorem birthday_nat_cast : ∀ n : ℕ, birthday n = n
| 0 := birthday_zero
| (n + 1) := by simp [birthday_nat_cast]

theorem birthday_add_nat (n : ℕ) : (a + n).birthday = a.birthday + n := by simp
theorem birthday_nat_add (n : ℕ) : (↑n + a).birthday = a.birthday + n := by simp

end pgame
