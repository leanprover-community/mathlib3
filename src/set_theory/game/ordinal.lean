/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.game.birthday
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

instance : is_empty (0 : ordinal).to_pgame.left_moves :=
by { rw to_pgame_left_moves, apply_instance }

instance (o : ordinal) : is_empty o.to_pgame.right_moves :=
by { rw to_pgame_right_moves, apply_instance }

/-- Converts a member of `o.out.α` into a move for the `pgame` corresponding to `o`, and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def to_left_moves_to_pgame {o : ordinal} : o.out.α ≃ o.to_pgame.left_moves :=
equiv.cast (to_pgame_left_moves o).symm

theorem to_pgame_move_left_heq {o : ordinal} :
  o.to_pgame.move_left == λ x : o.out.α, (typein (<) x).to_pgame :=
by { rw to_pgame, refl }

@[simp] theorem to_pgame_move_left {o : ordinal} (i : o.out.α) :
  o.to_pgame.move_left (to_left_moves_to_pgame i) = (typein (<) i).to_pgame :=
by { rw to_left_moves_to_pgame, exact congr_fun_heq _ to_pgame_move_left_heq i }

theorem to_pgame_lt {a b : ordinal} (h : a < b) : a.to_pgame < b.to_pgame :=
begin
  convert pgame.move_left_lt (to_left_moves_to_pgame (enum (<) a _)),
  { rw [to_pgame_move_left, typein_enum] },
  { rwa type_lt }
end

theorem to_pgame_le {a b : ordinal} (h : a ≤ b) : a.to_pgame ≤ b.to_pgame :=
begin
  rw pgame.le_def,
  refine ⟨λ i, or.inl ⟨to_left_moves_to_pgame
    (enum (<) (typein (<) (to_left_moves_to_pgame.symm i)) _), _⟩, is_empty_elim⟩,
  { rw type_lt,
    apply lt_of_lt_of_le _ h,
    simp_rw ←type_lt a,
    apply typein_lt_type },
  { rw [←to_left_moves_to_pgame.apply_symm_apply i, to_pgame_move_left],
    simp }
end

@[simp] theorem to_pgame_lt_iff {a b : ordinal} : a.to_pgame < b.to_pgame ↔ a < b :=
⟨by { contrapose, rw [not_lt, pgame.not_lt], exact to_pgame_le }, to_pgame_lt⟩

@[simp] theorem to_pgame_le_iff {a b : ordinal} : a.to_pgame ≤ b.to_pgame ↔ a ≤ b :=
⟨by { contrapose, rw [not_le, pgame.not_le], exact to_pgame_lt }, to_pgame_le⟩

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

theorem to_pgame_birthday (o : ordinal) : o.to_pgame.birthday = o :=
begin
  induction o using ordinal.induction with o IH,
  rw pgame.birthday_def,
  convert max_eq_left_iff.2 (ordinal.zero_le _),
  { apply lsub_empty },
  { nth_rewrite_lhs 0 ←lsub_typein o,
    congr,
    { exact (to_pgame_left_moves o).symm },
    { apply function.hfunext (to_pgame_left_moves o).symm,
      rintro a b h,
      have hwf := typein_lt_self a,
      have : to_left_moves_to_pgame a = b := cast_eq_iff_heq.2 h,
      rw [←this, to_pgame_move_left, IH _ (typein_lt_self a)] } }
end

end ordinal
