/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import algebra.order.hom.monoid
import set_theory.game.basic
import set_theory.ordinal.natural_ops

/-!
# Ordinals as games

We define the canonical maps `ordinal → pgame` and `ordinal → game`, where every ordinal is mapped
to the game whose left set consists of all previous ordinals.

The map to surreals is defined in `ordinal.to_surreal`.

# Main declarations

- `ordinal.to_pgame`: The canonical map between ordinals and pre-games.
- `ordinal.to_pgame_embedding`: The order embedding version of the previous map.
- `ordinal.to_game`: The composition of `ordinal.to_pgame` with `quot.mk` as an order embedding.

# Todo

Prove that `nat_ordinal.to_game` preserves multiplication.
-/

universe u

open pgame

open_locale natural_ops pgame

namespace ordinal

/-! ### Ordinals to `pgame` -/

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable! def to_pgame : ordinal.{u} → pgame.{u}
| o := ⟨o.out.α, pempty, λ x, let hwf := ordinal.typein_lt_self x in
        (typein (<) x).to_pgame, pempty.elim⟩
using_well_founded { dec_tac := tactic.assumption }

theorem to_pgame_def (o : ordinal) :
  o.to_pgame = ⟨o.out.α, pempty, λ x, (typein (<) x).to_pgame, pempty.elim⟩ :=
by rw to_pgame

@[simp] theorem to_pgame_left_moves (o : ordinal) : o.to_pgame.left_moves = o.out.α :=
by rw [to_pgame, left_moves]

@[simp] theorem to_pgame_right_moves (o : ordinal) : o.to_pgame.right_moves = pempty :=
by rw [to_pgame, right_moves]

instance is_empty_zero_to_pgame_left_moves : is_empty (to_pgame 0).left_moves :=
by { rw to_pgame_left_moves, apply_instance }

instance is_empty_to_pgame_right_moves (o : ordinal) : is_empty o.to_pgame.right_moves :=
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

/-- `0.to_pgame` has the same moves as `0`. -/
noncomputable def zero_to_pgame_relabelling : to_pgame 0 ≡r 0 :=
relabelling.is_empty _

theorem zero_to_pgame_equiv : to_pgame 0 ≈ 0 :=
zero_to_pgame_relabelling.equiv

noncomputable instance unique_one_to_pgame_left_moves : unique (to_pgame 1).left_moves :=
(equiv.cast $ to_pgame_left_moves 1).unique

@[simp] theorem one_to_pgame_left_moves_default_eq :
  (default : (to_pgame 1).left_moves) = @to_left_moves_to_pgame 1 ⟨0, zero_lt_one⟩ :=
rfl

@[simp] theorem to_left_moves_one_to_pgame_symm (i) :
  (@to_left_moves_to_pgame 1).symm i = ⟨0, zero_lt_one⟩ :=
by simp

theorem one_to_pgame_move_left (x) : (to_pgame 1).move_left x = to_pgame 0 :=
by simp

/-- `1.to_pgame` has the same moves as `1`. -/
noncomputable def one_to_pgame_relabelling : to_pgame 1 ≡r 1 :=
⟨equiv.equiv_of_unique _ _, equiv.equiv_of_is_empty _ _,
  λ i, by simpa using zero_to_pgame_relabelling, is_empty_elim⟩

theorem one_to_pgame_equiv : to_pgame 1 ≈ 1 :=
one_to_pgame_relabelling.equiv

theorem to_pgame_lf {a b : ordinal} (h : a < b) : a.to_pgame ⧏ b.to_pgame :=
by { convert move_left_lf (to_left_moves_to_pgame ⟨a, h⟩), rw to_pgame_move_left }

theorem to_pgame_le {a b : ordinal} (h : a ≤ b) : a.to_pgame ≤ b.to_pgame :=
begin
  refine le_of_forall_lf (λ i, _) is_empty_elim,
  rw to_pgame_move_left',
  exact to_pgame_lf ((to_left_moves_to_pgame_symm_lt i).trans_le h)
end

theorem to_pgame_lt {a b : ordinal} (h : a < b) : a.to_pgame < b.to_pgame :=
⟨to_pgame_le h.le, to_pgame_lf h⟩

theorem to_pgame_nonneg (a : ordinal) : 0 ≤ a.to_pgame :=
zero_to_pgame_relabelling.ge.trans $ to_pgame_le $ ordinal.zero_le a

theorem to_pgame_strict_mono : strict_mono to_pgame :=
@to_pgame_lt

@[simp] theorem to_pgame_lf_iff {a b : ordinal} : a.to_pgame ⧏ b.to_pgame ↔ a < b :=
⟨by { contrapose, rw [not_lt, not_lf], exact to_pgame_le }, to_pgame_lf⟩

@[simp] theorem to_pgame_le_iff {a b : ordinal} : a.to_pgame ≤ b.to_pgame ↔ a ≤ b :=
⟨by { contrapose, rw [not_le, pgame.not_le], exact to_pgame_lf }, to_pgame_le⟩

@[simp] theorem to_pgame_lt_iff {a b : ordinal} : a.to_pgame < b.to_pgame ↔ a < b :=
⟨by { contrapose, rw not_lt, exact λ h, not_lt_of_le (to_pgame_le h) }, to_pgame_lt⟩

@[simp] theorem to_pgame_equiv_iff {a b : ordinal} : a.to_pgame ≈ b.to_pgame ↔ a = b :=
by rw [pgame.equiv, le_antisymm_iff, to_pgame_le_iff, to_pgame_le_iff]

theorem to_pgame_injective : function.injective ordinal.to_pgame :=
λ a b h, to_pgame_equiv_iff.1 $ equiv_of_eq h

@[simp] theorem to_pgame_eq_iff {a b : ordinal} : a.to_pgame = b.to_pgame ↔ a = b :=
to_pgame_injective.eq_iff

/-- The order embedding version of `to_pgame`. -/
@[simps] noncomputable def to_pgame_embedding : ordinal ↪o pgame :=
{ to_fun := ordinal.to_pgame,
  inj' := to_pgame_injective,
  map_rel_iff' := @to_pgame_le_iff }

/-- The sum of ordinals as games corresponds to natural addition of ordinals. -/
theorem to_pgame_add : ∀ a b : ordinal.{u}, a.to_pgame + b.to_pgame ≈ (a ♯ b).to_pgame
| a b := begin
  refine ⟨le_of_forall_lf (λ i, _) is_empty_elim, le_of_forall_lf (λ i, _) is_empty_elim⟩,
  { apply left_moves_add_cases i;
    intro i;
    let wf := to_left_moves_to_pgame_symm_lt i;
    try { rw add_move_left_inl }; try { rw add_move_left_inr };
    rw [to_pgame_move_left', lf_congr_left (to_pgame_add _ _), to_pgame_lf_iff],
    { exact nadd_lt_nadd_right wf _ },
    { exact nadd_lt_nadd_left wf _ } },
  { rw to_pgame_move_left',
    rcases lt_nadd_iff.1 (to_left_moves_to_pgame_symm_lt i) with ⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩;
    rw [←to_pgame_le_iff, ←le_congr_right (to_pgame_add _ _)] at hc';
    apply lf_of_le_of_lf hc',
    { apply add_lf_add_right,
      rwa to_pgame_lf_iff },
    { apply add_lf_add_left,
      rwa to_pgame_lf_iff } }
end
using_well_founded { dec_tac := `[solve_by_elim [psigma.lex.left, psigma.lex.right]] }

/-! ### Ordinals to `game` -/

/-- Converts an `ordinal` into a `pgame`. -/
noncomputable def to_game : ordinal ↪o game :=
{ to_fun := λ o, ⟦o.to_pgame⟧,
  inj' := λ a b h, by rwa [←equiv_iff_game_eq, to_pgame_equiv_iff] at h,
  map_rel_iff' := @to_pgame_le_iff }

@[simp] theorem quot_to_pgame (o : ordinal) : ⟦o.to_pgame⟧ = o.to_game := rfl

theorem to_game_strict_mono : strict_mono to_game :=
to_pgame_strict_mono

@[simp] theorem zero_to_game : to_game 0 = 0 :=
quot.sound zero_to_pgame_equiv

@[simp] theorem one_to_game : to_game 1 = 1 :=
quot.sound one_to_pgame_equiv

@[simp] theorem to_game_add (a b : ordinal) : a.to_game + b.to_game = (a ♯ b).to_game :=
quot.sound (to_pgame_add a b)

@[simp] theorem to_game_add_one (a : ordinal) : a.to_game + 1 = (order.succ a).to_game :=
by rw [←one_to_game, to_game_add, nadd_one]

theorem to_pgame_add_one (a : ordinal) : a.to_pgame + 1 ≈ (order.succ a).to_pgame :=
quotient.exact (to_game_add_one a)

@[simp] theorem to_game_one_add (a : ordinal) : 1 + a.to_game = (order.succ a).to_game :=
by rw [add_comm, to_game_add_one]

theorem to_pgame_one_add (a : ordinal) : 1 + a.to_pgame ≈ (order.succ a).to_pgame :=
quotient.exact (to_game_one_add a)

@[simp] theorem nat_cast_to_game : ∀ n : ℕ, to_game n = n
| 0       := by simp
| (n + 1) := begin
  rw [nat.cast_add, nat.cast_one, add_one_eq_succ, ←to_game_add_one, nat_cast_to_game],
  refl
end

theorem nat_cast_to_pgame (n : ℕ) : to_pgame n ≈ n :=
@quotient.exact pgame _ _ _ $ by simp

@[simp] theorem to_game_add_nat (a : ordinal) (n : ℕ) : a.to_game + n = (a + n).to_game :=
by rw [←nat_cast_to_game, to_game_add, nadd_nat]

theorem to_pgame_add_nat (a : ordinal) (n : ℕ) : a.to_pgame + n ≈ (a + n).to_pgame :=
@quotient.exact pgame _ _ _ $ by simp

@[simp] theorem to_game_nat_add (a : ordinal) (n : ℕ) : ↑n + a.to_game = (a + n).to_game :=
by rw [add_comm, to_game_add_nat]

theorem to_pgame_nat_add (a : ordinal) (n : ℕ) : ↑n + a.to_pgame ≈ (a + n).to_pgame :=
@quotient.exact pgame _ _ _ $ by simp

end ordinal

/-- The cast from `nat_ordinal` to `game` preserves addition. -/
noncomputable def nat_ordinal.to_game : nat_ordinal →+o game :=
{ to_fun := λ o, o.to_ordinal.to_game,
  map_zero' := ordinal.zero_to_game,
  map_add' := λ a b, (ordinal.to_game_add _ _).symm,
  monotone' := ordinal.to_game_strict_mono.monotone }
