/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Combinatorial games with a finite set of moves at every point.
-/
import set_theory.game
import data.fintype

universes u

namespace pgame

/-- A short game is a game with a finite set of moves at every turn. -/
inductive short : pgame.{u} → Type (u+1)
| mk : Π (x : pgame) [fintype x.left_moves] [fintype x.right_moves]
         [∀ i : x.left_moves, short (x.move_left i)] [∀ j : x.right_moves, short (x.move_right j)], short x

attribute [class] short

instance fintype_left_moves (x : pgame) [S : short x] : fintype (x.left_moves) :=
begin
  tactic.unfreeze_local_instances,
  induction S with _ F _ _ _,
  apply F
end
instance fintype_right_moves (x : pgame) [S : short x] : fintype (x.right_moves) :=
begin
  tactic.unfreeze_local_instances,
  induction S with _ _ F _ _,
  apply F
end
instance move_left_short (x : pgame) [S : short x] (i : x.left_moves) : short (x.move_left i) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ L _,
  apply L
end
instance move_left_short' {xl xr xL xR} [S : short (mk xl xr xL xR)] (i : xl) : short (xL i) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ L _,
  apply L
end
instance move_right_short (x : pgame) [S : short x] (j : x.right_moves) : short (x.move_right j) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ _ R,
  apply R
end
instance move_right_short' {xl xr xL xR} [S : short (mk xl xr xL xR)] (j : xr) : short (xR j) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ _ R,
  apply R
end

instance short_0 : short 0 :=
@short.mk 0 pempty.fintype pempty.fintype (λ i, by cases i) (λ j, by cases j)

instance short_1 : short 1 :=
@short.mk 1 punit.fintype pempty.fintype (λ i, begin cases i, dsimp, apply_instance, end) (λ j, by cases j)

instance short_of_lists (L R : list pgame) [sL : ∀ l ∈ L, short l] [sR : ∀ r ∈ R, short r] :
  short (pgame.of_lists L R) :=
@short.mk (pgame.of_lists L R) (fin.fintype _) (fin.fintype _)
(λ i, sL _ (list.nth_le_mem _ _ _))
(λ j, sR _ (list.nth_le_mem _ _ _))

instance short_neg : Π (x : pgame.{u}) [short x], short (-x)
| (mk xl xr xL xR) _ :=
begin
  resetI,
  apply @short.mk _ _ _ _ _,
  { apply fintype.of_equiv _ ((left_moves_neg _).symm),
    apply_instance },
  { apply fintype.of_equiv _ ((right_moves_neg _).symm),
    apply_instance },
  { rintro i,
    dsimp,
    dsimp at i,
    apply short_neg _,
    apply_instance, },
  { rintro j,
    dsimp,
    dsimp at j,
    apply short_neg _,
    apply_instance, },
end
using_well_founded { dec_tac := pgame_wf_tac }

instance short_add : Π (x y : pgame.{u}) [short x] [short y], short (x + y)
| (mk xl xr xL xR) (mk yl yr yL yR) _ _ :=
begin
  resetI,
  apply @short.mk _ _ _ _ _,
  { apply fintype.of_equiv _ (left_moves_add.symm),
    apply sum.fintype },
  { apply fintype.of_equiv _ (right_moves_add.symm),
    apply sum.fintype },
  { rintro ⟨i⟩,
    { apply short_add, },
    { change short (mk xl xr xL xR + yL i), apply short_add, } },
  { rintro ⟨j⟩,
    { apply short_add, },
    { change short (mk xl xr xL xR + yR j), apply short_add, } },
end
using_well_founded { dec_tac := pgame_wf_tac }

instance le_decidable : Π (x y : pgame.{u}) [short x] [short y], decidable (x ≤ y)
| x y _ _ :=
begin
  resetI,
  rw le_def,
  apply @and.decidable _ _ _ _,
  { apply @fintype.decidable_forall_fintype (left_moves x) (by apply_instance) _ _,
    intro i,
    apply @or.decidable _ _ _ _,
    { apply @fintype.decidable_exists_fintype (right_moves (move_left x i)) (by apply_instance) _ _,
      intro j,
      apply le_decidable },
    { apply @fintype.decidable_exists_fintype (left_moves y) (by apply_instance) _ _,
      intro j,
      apply le_decidable }, },
  { apply @fintype.decidable_forall_fintype (right_moves y) (by apply_instance) _ _,
    intro i,
    apply @or.decidable _ _ _ _,
    { apply @fintype.decidable_exists_fintype (right_moves x) (by apply_instance) _ _,
      intro j,
      apply le_decidable },
    { apply @fintype.decidable_exists_fintype (left_moves (move_right y i)) (by apply_instance) _ _,
      intro j,
      apply le_decidable }, },
end
using_well_founded { dec_tac := pgame_wf_tac }

instance equiv_decidable (x y : pgame.{u}) [short x] [short y] : decidable (x ≈ y) :=
and.decidable

example : short 0 := by apply_instance
example : short 1 := by apply_instance
example : short (0 + 0) := by apply_instance

example : decidable ((1 : pgame) ≤ 1) := by apply_instance

#eval to_bool ((1 : pgame) ≤ 0)
#eval to_bool ((0 : pgame) ≤ 1)
#eval to_bool ((1 : pgame) ≤ 1)

#eval to_bool ((1 : pgame) + 1 + 1 ≤ (1 + 0 + 1))

-- TODO but this doesn't work?
-- example : (0 : pgame) ≤ 0 := dec_trivial
-- example : (1 : pgame) ≤ 1 := by exact dec_trivial

end pgame
