/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.game.pgame
import set_theory.ordinal.basic

/-!
# Ordinals as games

We define the canonical map `ordinal → pgame`, where every ordinal is mapped to the game whose left
set consists of all previous ordinals.

# Main declarations

- `ordinal.to_pgame`: The canonical map between ordinals and pre-games.
- `ordinal.to_pgame_embedding`: The order embedding version of the previous map.

# Todo

- Extend this map to `game` and `surreal`.
-/

local infix ` ≈ ` := pgame.equiv

universe u

namespace ordinal

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable! def to_pgame : Π o : ordinal.{u}, pgame.{u}
| o := ⟨o.out.α, pempty, λ x, let hwf := ordinal.typein_lt_self x in
        (typein (<) x).to_pgame, pempty.elim⟩
using_well_founded { dec_tac := tactic.assumption }

theorem to_pgame_def (o : ordinal) :
  o.to_pgame = ⟨o.out.α, pempty, λ x, (typein (<) x).to_pgame, pempty.elim⟩ :=
by rw to_pgame

@[simp] theorem to_pgame_left_moves (o : ordinal) : o.to_pgame.left_moves = o.out.α :=
by rw [to_pgame, pgame.left_moves]

@[simp] theorem to_pgame_right_moves (o : ordinal) : o.to_pgame.right_moves = pempty :=
by rw [to_pgame, pgame.right_moves]

instance : is_empty (to_pgame 0).left_moves :=
by { rw to_pgame_left_moves, apply_instance }

instance (o : ordinal) : is_empty o.to_pgame.right_moves :=
by { rw to_pgame_right_moves, apply_instance }

/-- Converts an ordinal less than `o` into a move for the `pgame` corresponding to `o`, and vice
versa. -/
noncomputable def to_left_moves_to_pgame {o : ordinal} : set.Iio o ≃ o.to_pgame.left_moves :=
(enum_iso_out o).to_equiv.trans (equiv.cast (to_pgame_left_moves o).symm)

@[simp] theorem to_left_moves_to_pgame_symm_lt {o : ordinal} (i : o.to_pgame.left_moves) :
  ↑(to_left_moves_to_pgame.symm i) < o :=
(to_left_moves_to_pgame.symm i).prop

theorem to_pgame_move_left_heq {o : ordinal} :
  o.to_pgame.move_left == λ x : o.out.α, (typein (<) x).to_pgame :=
by { rw to_pgame, refl }

@[simp] theorem to_pgame_move_left' {o : ordinal} (i) :
  o.to_pgame.move_left i = (to_left_moves_to_pgame.symm i).val.to_pgame :=
(congr_heq to_pgame_move_left_heq.symm (cast_heq _ i)).symm

theorem to_pgame_move_left {o : ordinal} (i) :
  o.to_pgame.move_left (to_left_moves_to_pgame i) = i.val.to_pgame :=
by simp

theorem to_pgame_lt {a b : ordinal} (h : a < b) : a.to_pgame < b.to_pgame :=
by { convert pgame.move_left_lt (to_left_moves_to_pgame ⟨a, h⟩), rw to_pgame_move_left }

theorem to_pgame_le {a b : ordinal} (h : a ≤ b) : a.to_pgame ≤ b.to_pgame :=
pgame.le_def.2 ⟨λ i, or.inl ⟨to_left_moves_to_pgame
  ⟨(to_left_moves_to_pgame.symm i).val, (to_left_moves_to_pgame_symm_lt i).trans_le h⟩, by simp⟩,
  is_empty_elim⟩

@[simp] theorem to_pgame_lt_iff {a b : ordinal} : a.to_pgame < b.to_pgame ↔ a < b :=
⟨by { contrapose, rw [not_lt, pgame.not_lt], exact to_pgame_le }, to_pgame_lt⟩

@[simp] theorem to_pgame_le_iff {a b : ordinal} : a.to_pgame ≤ b.to_pgame ↔ a ≤ b :=
⟨by { contrapose, rw [not_le, pgame.not_le], exact to_pgame_lt }, to_pgame_le⟩

@[simp] theorem to_pgame_equiv_iff {a b : ordinal} : a.to_pgame ≈ b.to_pgame ↔ a = b :=
by rw [pgame.equiv, le_antisymm_iff, to_pgame_le_iff, to_pgame_le_iff]

theorem to_pgame_injective : function.injective ordinal.to_pgame :=
λ a b h, begin
  by_contra hne,
  cases lt_or_gt_of_ne hne with hlt hlt;
  { have := to_pgame_lt hlt,
    rw h at this,
    exact pgame.lt_irrefl _ this }
end

/-- The order embedding version of `to_pgame`. -/
@[simps] noncomputable def to_pgame_embedding : ordinal.{u} ↪o pgame.{u} :=
{ to_fun := ordinal.to_pgame,
  inj' := to_pgame_injective,
  map_rel_iff' := @to_pgame_le_iff }

end ordinal
