/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import set_theory.game.short

/-!
# Games described via "the state of the board".

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `dec_trivial`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `set_theory/game/domineering` for an example using this construction.
-/

universe u

namespace pgame

/--
`pgame_state S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `pgame.of_state s` or `game.of_state s` to construct the game.

`pgame_state.L : S → finset S` and `pgame_state.R : S → finset S` describe the states reachable
by a move by Left or Right. `pgame_state.turn_bound : S → ℕ` gives an upper bound on the number of
possible turns remaining from this state.
-/
class state (S : Type u) :=
(turn_bound : S → ℕ)
(L : S → finset S)
(R : S → finset S)
(left_bound : ∀ {s t : S} (m : t ∈ L s), turn_bound t < turn_bound s)
(right_bound : ∀ {s t : S} (m : t ∈ R s), turn_bound t < turn_bound s)

open state

variables {S : Type u} [state S]

lemma turn_bound_ne_zero_of_left_move {s t : S} (m : t ∈ L s) : turn_bound s ≠ 0 :=
begin
  intro h,
  have t := state.left_bound m,
  rw h at t,
  exact nat.not_succ_le_zero _ t,
end
lemma turn_bound_ne_zero_of_right_move {s t : S} (m : t ∈ R s) : turn_bound s ≠ 0 :=
begin
  intro h,
  have t := state.right_bound m,
  rw h at t,
  exact nat.not_succ_le_zero _ t,
end

lemma turn_bound_of_left {s t : S} (m : t ∈ L s) (n : ℕ) (h : turn_bound s ≤ n + 1) :
  turn_bound t ≤ n :=
nat.le_of_lt_succ (nat.lt_of_lt_of_le (left_bound m) h)
lemma turn_bound_of_right {s t : S} (m : t ∈ R s) (n : ℕ) (h : turn_bound s ≤ n + 1) :
  turn_bound t ≤ n :=
nat.le_of_lt_succ (nat.lt_of_lt_of_le (right_bound m) h)

/--
Construct a `pgame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def of_state_aux : Π (n : ℕ) (s : S) (h : turn_bound s ≤ n), pgame
| 0 s h     := pgame.mk {t // t ∈ L s} {t // t ∈ R s}
    (λ t, begin exfalso, exact turn_bound_ne_zero_of_left_move t.2 (nonpos_iff_eq_zero.mp h) end)
    (λ t, begin exfalso, exact turn_bound_ne_zero_of_right_move t.2 (nonpos_iff_eq_zero.mp h) end)
| (n+1) s h :=
  pgame.mk {t // t ∈ L s} {t // t ∈ R s}
    (λ t, of_state_aux n t (turn_bound_of_left t.2 n h))
    (λ t, of_state_aux n t (turn_bound_of_right t.2 n h))

/-- Two different (valid) turn bounds give equivalent games. -/
def of_state_aux_relabelling : Π (s : S) (n m : ℕ) (hn : turn_bound s ≤ n) (hm : turn_bound s ≤ m),
  relabelling (of_state_aux n s hn) (of_state_aux m s hm)
| s 0 0 hn hm :=
  begin
    dsimp [pgame.of_state_aux],
    fsplit, refl, refl,
    { intro i, dsimp at i, exfalso,
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn) },
    { intro j, dsimp at j, exfalso,
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm) }
  end
| s 0 (m+1) hn hm :=
  begin
    dsimp [pgame.of_state_aux],
    fsplit, refl, refl,
    { intro i, dsimp at i, exfalso,
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn) },
    { intro j, dsimp at j, exfalso,
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hn) }
  end
| s (n+1) 0 hn hm :=
  begin
    dsimp [pgame.of_state_aux],
    fsplit, refl, refl,
    { intro i, dsimp at i, exfalso,
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hm) },
    { intro j, dsimp at j, exfalso,
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm) }
  end
| s (n+1) (m+1) hn hm :=
  begin
    dsimp [pgame.of_state_aux],
    fsplit, refl, refl,
    { intro i,
      apply of_state_aux_relabelling, },
    { intro j,
      apply of_state_aux_relabelling, }
  end

/-- Construct a combinatorial `pgame` from a state. -/
def of_state (s : S) : pgame := of_state_aux (turn_bound s) s (refl _)

/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`L s`. -/
def left_moves_of_state_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n) :
  left_moves (of_state_aux n s h) ≃ {t // t ∈ L s} :=
by induction n; refl

/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state s`, and `L s`. -/
def left_moves_of_state (s : S) : left_moves (of_state s) ≃ {t // t ∈ L s} :=
left_moves_of_state_aux _ _

/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`R s`. -/
def right_moves_of_state_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n) :
  right_moves (of_state_aux n s h) ≃ {t // t ∈ R s} :=
by induction n; refl

/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state s`, and
`R s`. -/
def right_moves_of_state (s : S) : right_moves (of_state s) ≃ {t // t ∈ R s} :=
right_moves_of_state_aux _ _

/--
The relabelling showing `move_left` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def relabelling_move_left_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n)
  (t : left_moves (of_state_aux n s h)) :
  relabelling
    (move_left (of_state_aux n s h) t)
    (of_state_aux (n-1) (((left_moves_of_state_aux n h) t) : S)
      ((turn_bound_of_left ((left_moves_of_state_aux n h) t).2 (n-1)
        (nat.le_trans h le_tsub_add)))) :=
begin
  induction n,
  { have t' := (left_moves_of_state_aux 0 h) t,
    exfalso, exact turn_bound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h), },
  { refl },
end
/--
The relabelling showing `move_left` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabelling_move_left (s : S) (t : left_moves (of_state s)) :
  relabelling
    (move_left (of_state s) t)
    (of_state (((left_moves_of_state s).to_fun t) : S)) :=
begin
  transitivity,
  apply relabelling_move_left_aux,
  apply of_state_aux_relabelling,
end
/--
The relabelling showing `move_right` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def relabelling_move_right_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n)
  (t : right_moves (of_state_aux n s h)) :
  relabelling
    (move_right (of_state_aux n s h) t)
    (of_state_aux (n-1) (((right_moves_of_state_aux n h) t) : S)
      ((turn_bound_of_right ((right_moves_of_state_aux n h) t).2 (n-1)
        (nat.le_trans h le_tsub_add)))) :=
begin
  induction n,
  { have t' := (right_moves_of_state_aux 0 h) t,
    exfalso, exact turn_bound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h), },
  { refl },
end
/--
The relabelling showing `move_right` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabelling_move_right (s : S) (t : right_moves (of_state s)) :
  relabelling
    (move_right (of_state s) t)
    (of_state (((right_moves_of_state s).to_fun t) : S)) :=
begin
  transitivity,
  apply relabelling_move_right_aux,
  apply of_state_aux_relabelling,
end

instance fintype_left_moves_of_state_aux (n : ℕ) (s : S) (h : turn_bound s ≤ n) :
  fintype (left_moves (of_state_aux n s h)) :=
begin
  apply fintype.of_equiv _ (left_moves_of_state_aux _ _).symm,
  apply_instance,
end
instance fintype_right_moves_of_state_aux (n : ℕ) (s : S) (h : turn_bound s ≤ n) :
  fintype (right_moves (of_state_aux n s h)) :=
begin
  apply fintype.of_equiv _ (right_moves_of_state_aux _ _).symm,
  apply_instance,
end

instance short_of_state_aux : Π (n : ℕ) {s : S} (h : turn_bound s ≤ n), short (of_state_aux n s h)
| 0 s h :=
  short.mk'
  (λ i, begin
    have i := (left_moves_of_state_aux _ _).to_fun i,
    exfalso,
    exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h),
  end)
  (λ j, begin
    have j := (right_moves_of_state_aux _ _).to_fun j,
    exfalso,
    exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h),
  end)
| (n+1) s h :=
  short.mk'
  (λ i, short_of_relabelling (relabelling_move_left_aux (n+1) h i).symm (short_of_state_aux n _))
  (λ j, short_of_relabelling (relabelling_move_right_aux (n+1) h j).symm (short_of_state_aux n _))

instance short_of_state (s : S) : short (of_state s) :=
begin
  dsimp [pgame.of_state],
  apply_instance
end

end pgame

namespace game

/-- Construct a combinatorial `game` from a state. -/
def of_state {S : Type u} [pgame.state S] (s : S) : game := ⟦pgame.of_state s⟧

end game
