/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import data.fin.basic
import data.list.basic
import logic.relation

/-!
# Combinatorial (pre-)games.

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`. We
construct "pregames", define an ordering and arithmetic operations on them, then show that the
operations descend to "games", defined via the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a quotient of a subtype of pregames.

A pregame (`pgame` below) is axiomatised via an inductive type, whose sole constructor takes two
types (thought of as indexing the possible moves for the players Left and Right), and a pair of
functions out of these types to `pgame` (thought of as describing the resulting game after making a
move).

Combinatorial games themselves, as a quotient of pregames, are constructed in `game.lean`.

## Conway induction

By construction, the induction principle for pregames is exactly "Conway induction". That is, to
prove some predicate `pgame → Prop` holds for all pregames, it suffices to prove that for every
pregame `g`, if the predicate holds for every game resulting from making a move, then it also holds
for `g`.

While it is often convenient to work "by induction" on pregames, in some situations this becomes
awkward, so we also define accessor functions `pgame.left_moves`, `pgame.right_moves`,
`pgame.move_left` and `pgame.move_right`. There is a relation `pgame.subsequent p q`, saying that
`p` can be reached by playing some non-empty sequence of moves starting from `q`, an instance
`well_founded subsequent`, and a local tactic `pgame_wf_tac` which is helpful for discharging proof
obligations in inductive proofs relying on this relation.

## Order properties

Pregames have both a `≤` and a `<` relation, which are related in quite a subtle way. In particular,
it is worth noting that in Lean's (perhaps unfortunate?) definition of a `preorder`, we have
`lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`, but this is _not_ satisfied by the usual
`≤` and `<` relations on pregames. (It is satisfied once we restrict to the surreal numbers.) In
particular, `<` is not transitive; there is an example below showing `0 < star ∧ star < 0`.

We do have
```
theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := ...
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := ...
```

The statement `0 ≤ x` means that Left has a good response to any move by Right; in particular, the
theorem `zero_le` below states
```
0 ≤ x ↔ ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i
```
On the other hand the statement `0 < x` means that Left has a good move right now; in particular the
theorem `zero_lt` below states
```
0 < x ↔ ∃ i : left_moves x, ∀ j : right_moves (x.move_left i), 0 < (x.move_left i).move_right j
```

The theorems `le_def`, `lt_def`, give a recursive characterisation of each relation, in terms of
themselves two moves later. The theorems `le_def_lt` and `lt_def_lt` give recursive
characterisations of each relation in terms of the other relation one move later.

We define an equivalence relation `equiv p q ↔ p ≤ q ∧ q ≤ p`. Later, games will be defined as the
quotient by this relation.

## Algebraic structures

We next turn to defining the operations necessary to make games into a commutative additive group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by $x + y = \{xL + y, x + yL | xR +
y, x + yR\}$. Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$.

The order structures interact in the expected way with addition, so we have
```
theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry
theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x := sorry
```

We show that these operations respect the equivalence relation, and hence descend to games. At the
level of games, these operations satisfy all the laws of a commutative group. To prove the necessary
equivalence relations at the level of pregames, we introduce the notion of a `relabelling` of a
game, and show, for example, that there is a relabelling between `x + (y + z)` and `(x + y) + z`.

## Future work
* The theory of dominated and reversible positions, and unique normal form for short games.
* Analysis of basic domineering positions.
* Hex.
* Temperature.
* The development of surreal numbers, based on this development of combinatorial games, is still
  quite incomplete.

## References

The material here is all drawn from
* [Conway, *On numbers and games*][conway2001]

An interested reader may like to formalise some of the material from
* [Andreas Blass, *A game semantics for linear logic*][MR1167694]
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1997]
-/

open function relation

universes u

/-- The type of pre-games, before we have quotiented
  by equivalence (`pgame.setoid`). In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive pgame : Type (u+1)
| mk : ∀ α β : Type u, (α → pgame) → (β → pgame) → pgame

namespace pgame

/-- The indexing type for allowable moves by Left. -/
def left_moves : pgame → Type u
| (mk l _ _ _) := l
/-- The indexing type for allowable moves by Right. -/
def right_moves : pgame → Type u
| (mk _ r _ _) := r

/-- The new game after Left makes an allowed move. -/
def move_left : Π (g : pgame), left_moves g → pgame
| (mk l _ L _) := L
/-- The new game after Right makes an allowed move. -/
def move_right : Π (g : pgame), right_moves g → pgame
| (mk _ r _ R) := R

@[simp] lemma left_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).left_moves = xl := rfl
@[simp] lemma move_left_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).move_left = xL := rfl
@[simp] lemma right_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).right_moves = xr := rfl
@[simp] lemma move_right_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).move_right = xR := rfl

/--
Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
def of_lists (L R : list pgame.{u}) : pgame.{u} :=
mk (ulift (fin L.length)) (ulift (fin R.length))
  (λ i, L.nth_le i.down i.down.is_lt) (λ j, R.nth_le j.down j.down.prop)

lemma left_moves_of_lists (L R : list pgame) : (of_lists L R).left_moves = ulift (fin L.length) :=
rfl
lemma right_moves_of_lists (L R : list pgame) : (of_lists L R).right_moves = ulift (fin R.length) :=
rfl

/-- Converts a number into a left move for `of_lists`. -/
def to_of_lists_left_moves {L R : list pgame} : fin L.length ≃ (of_lists L R).left_moves :=
((equiv.cast (left_moves_of_lists L R).symm).trans equiv.ulift).symm

/-- Converts a number into a right move for `of_lists`. -/
def to_of_lists_right_moves {L R : list pgame} : fin R.length ≃ (of_lists L R).right_moves :=
((equiv.cast (right_moves_of_lists L R).symm).trans equiv.ulift).symm

theorem of_lists_move_left {L R : list pgame} (i : fin L.length) :
  (of_lists L R).move_left (to_of_lists_left_moves i) = L.nth_le i i.is_lt :=
rfl

@[simp] theorem of_lists_move_left' {L R : list pgame} (i : (of_lists L R).left_moves) :
  (of_lists L R).move_left i =
  L.nth_le (to_of_lists_left_moves.symm i) (to_of_lists_left_moves.symm i).is_lt :=
rfl

theorem of_lists_move_right {L R : list pgame} (i : fin R.length) :
  (of_lists L R).move_right (to_of_lists_right_moves i) = R.nth_le i i.is_lt :=
rfl

@[simp] theorem of_lists_move_right' {L R : list pgame} (i : (of_lists L R).right_moves) :
  (of_lists L R).move_right i =
  R.nth_le (to_of_lists_right_moves.symm i) (to_of_lists_right_moves.symm i).is_lt :=
rfl

/-- A variant of `pgame.rec_on` expressed in terms of `pgame.move_left` and `pgame.move_right`.

Both this and `pgame.rec_on` describe Conway induction on games. -/
@[elab_as_eliminator] def move_rec_on {C : pgame → Sort*} (x : pgame)
  (IH : ∀ (y : pgame), (∀ i, C (y.move_left i)) → (∀ j, C (y.move_right j)) → C y) : C x :=
x.rec_on $ λ yl yr yL yR, IH (mk yl yr yL yR)

/-- `is_option x y` means that `x` is either a left or right option for `y`. -/
@[mk_iff] inductive is_option : pgame → pgame → Prop
| move_left {x : pgame} (i : x.left_moves) : is_option (x.move_left i) x
| move_right {x : pgame} (i : x.right_moves) : is_option (x.move_right i) x

theorem is_option.mk_left {xl xr : Type u} (xL : xl → pgame) (xR : xr → pgame) (i : xl) :
  (xL i).is_option (mk xl xr xL xR) :=
@is_option.move_left (mk _ _ _ _) i

theorem is_option.mk_right {xl xr : Type u} (xL : xl → pgame) (xR : xr → pgame) (i : xr) :
  (xR i).is_option (mk xl xr xL xR) :=
@is_option.move_right (mk _ _ _ _) i

theorem wf_is_option : well_founded is_option :=
⟨λ x, move_rec_on x $ λ x IHl IHr, acc.intro x $ λ y h, begin
  induction h with _ i _ j,
  { exact IHl i },
  { exact IHr j }
end⟩

/-- `subsequent x y` says that `x` can be obtained by playing some nonempty sequence of moves from
`y`. It is the transitive closure of `is_option`. -/
def subsequent : pgame → pgame → Prop :=
trans_gen is_option

instance : is_trans _ subsequent := trans_gen.is_trans

@[trans] theorem subsequent.trans : ∀ {x y z}, subsequent x y → subsequent y z → subsequent x z :=
@trans_gen.trans _ _

theorem wf_subsequent : well_founded subsequent := wf_is_option.trans_gen

instance : has_well_founded pgame := ⟨_, wf_subsequent⟩

lemma subsequent.move_left {x : pgame} (i : x.left_moves) : subsequent (x.move_left i) x :=
trans_gen.single (is_option.move_left i)

lemma subsequent.move_right {x : pgame} (j : x.right_moves) : subsequent (x.move_right j) x :=
trans_gen.single (is_option.move_right j)

lemma subsequent.mk_left {xl xr} (xL : xl → pgame) (xR : xr → pgame) (i : xl) :
  subsequent (xL i) (mk xl xr xL xR) :=
@subsequent.move_left (mk _ _ _ _) i

lemma subsequent.mk_right {xl xr} (xL : xl → pgame) (xR : xr → pgame) (j : xr) :
  subsequent (xR j) (mk xl xr xL xR) :=
@subsequent.move_right (mk _ _ _ _) j

/-- A local tactic for proving well-foundedness of recursive definitions involving pregames. -/
meta def pgame_wf_tac :=
`[solve_by_elim
  [psigma.lex.left, psigma.lex.right, subsequent.move_left, subsequent.move_right,
   subsequent.mk_left, subsequent.mk_right, subsequent.trans]
  { max_depth := 6 }]

/-- The pre-game `zero` is defined by `0 = { | }`. -/
instance : has_zero pgame := ⟨⟨pempty, pempty, pempty.elim, pempty.elim⟩⟩

@[simp] lemma zero_left_moves : left_moves 0 = pempty := rfl
@[simp] lemma zero_right_moves : right_moves 0 = pempty := rfl

instance is_empty_zero_left_moves : is_empty (left_moves 0) := pempty.is_empty
instance is_empty_zero_right_moves : is_empty (right_moves 0) := pempty.is_empty

instance : inhabited pgame := ⟨0⟩

/-- The pre-game `one` is defined by `1 = { 0 | }`. -/
instance : has_one pgame := ⟨⟨punit, pempty, λ _, 0, pempty.elim⟩⟩

@[simp] lemma one_left_moves : left_moves 1 = punit := rfl
@[simp] lemma one_move_left (x) : move_left 1 x = 0 := rfl
@[simp] lemma one_right_moves : right_moves 1 = pempty := rfl

instance unique_one_left_moves : unique (left_moves 1) := punit.unique
instance is_empty_one_right_moves : is_empty (right_moves 1) := pempty.is_empty

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on pre-games. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  The solution is to define `x < y` and `x <= y` simultaneously. -/
def le_lt : Π (x y : pgame), Prop × Prop
| (mk xl xr xL xR) (mk yl yr yL yR) :=
  -- the orderings of the clauses here are carefully chosen so that
  --   and.left/or.inl refer to moves by Left, and
  --   and.right/or.inr refer to moves by Right.
((∀ i : xl, (le_lt (xL i) ⟨yl, yr, yL, yR⟩).2) ∧ (∀ j : yr, (le_lt ⟨xl, xr, xL, xR⟩ (yR j)).2),
  (∃ i : yl, (le_lt ⟨xl, xr, xL, xR⟩ (yL i)).1) ∨ (∃ j : xr, (le_lt (xR j) ⟨yl, yr, yL, yR⟩).1))
using_well_founded { dec_tac := pgame_wf_tac }

instance : has_le pgame := ⟨λ x y, (le_lt x y).1⟩
instance : has_lt pgame := ⟨λ x y, (le_lt x y).2⟩

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ ⟨yl, yr, yL, yR⟩ ↔
  (∀ i, xL i < ⟨yl, yr, yL, yR⟩) ∧
  (∀ j, (⟨xl, xr, xL, xR⟩ : pgame) < yR j) :=
show (le_lt _ _).1 ↔ _, by { rw le_lt, refl }

/-- Definition of `x ≤ y` on pre-games, in terms of `<` -/
theorem le_def_lt {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves, x.move_left i < y) ∧
  (∀ j : y.right_moves, x < y.move_right j) :=
by { cases x, cases y, rw mk_le_mk, refl }

/-- Definition of `x < y` on pre-games built using the constructor. -/
@[simp] theorem mk_lt_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) < ⟨yl, yr, yL, yR⟩ ↔
  (∃ i, (⟨xl, xr, xL, xR⟩ : pgame) ≤ yL i) ∨
  (∃ j, xR j ≤ ⟨yl, yr, yL, yR⟩) :=
show (le_lt _ _).2 ↔ _, by { rw le_lt, refl }

/-- Definition of `x < y` on pre-games, in terms of `≤` -/
theorem lt_def_le {x y : pgame} : x < y ↔
  (∃ i : y.left_moves, x ≤ y.move_left i) ∨
  (∃ j : x.right_moves, x.move_right j ≤ y) :=
by { cases x, cases y, rw mk_lt_mk, refl }

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves,
   (∃ i' : y.left_moves, x.move_left i ≤ y.move_left i') ∨
   (∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ y)) ∧
  (∀ j : y.right_moves,
   (∃ i : (y.move_right j).left_moves, x ≤ (y.move_right j).move_left i) ∨
   (∃ j' : x.right_moves, x.move_right j' ≤ y.move_right j)) :=
begin
  rw [le_def_lt],
  conv { to_lhs, simp only [lt_def_le] },
end

/-- The definition of `x < y` on pre-games, in terms of `<` two moves later. -/
theorem lt_def {x y : pgame} : x < y ↔
  (∃ i : y.left_moves,
    (∀ i' : x.left_moves, x.move_left i' < y.move_left i) ∧
    (∀ j : (y.move_left i).right_moves, x < (y.move_left i).move_right j)) ∨
  (∃ j : x.right_moves,
    (∀ i : (x.move_right j).left_moves, (x.move_right j).move_left i < y) ∧
    (∀ j' : y.right_moves, x.move_right j < y.move_right j')) :=
begin
  rw [lt_def_le],
  conv { to_lhs, simp only [le_def_lt] },
end

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : pgame} : x ≤ 0 ↔
  ∀ i : x.left_moves, ∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ 0 :=
by { rw le_def, dsimp, simp [forall_pempty, exists_pempty] }

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : pgame} : 0 ≤ x ↔
  ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i :=
by { rw le_def, dsimp, simp [forall_pempty, exists_pempty] }

/-- The definition of `x < 0` on pre-games, in terms of `< 0` two moves later. -/
theorem lt_zero {x : pgame} : x < 0 ↔
  ∃ j : x.right_moves, ∀ i : (x.move_right j).left_moves, (x.move_right j).move_left i < 0 :=
by { rw lt_def, dsimp, simp [forall_pempty, exists_pempty] }

/-- The definition of `0 < x` on pre-games, in terms of `< x` two moves later. -/
theorem zero_lt {x : pgame} : 0 < x ↔
  ∃ i : x.left_moves, ∀ j : (x.move_left i).right_moves, 0 < (x.move_left i).move_right j :=
by { rw lt_def, dsimp, simp [forall_pempty, exists_pempty] }

@[simp] theorem le_zero_of_is_empty_left_moves (x : pgame) [is_empty x.left_moves] : x ≤ 0 :=
le_zero.2 is_empty_elim

@[simp] theorem zero_le_of_is_empty_right_moves (x : pgame) [is_empty x.right_moves] : 0 ≤ x :=
zero_le.2 is_empty_elim

/-- Given a right-player-wins game, provide a response to any move by left. -/
noncomputable def right_response {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).right_moves :=
classical.some $ (le_zero.1 h) i

/-- Show that the response for right provided by `right_response`
    preserves the right-player-wins condition. -/
lemma right_response_spec {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).move_right (right_response h i) ≤ 0 :=
classical.some_spec $ (le_zero.1 h) i

/-- Given a left-player-wins game, provide a response to any move by right. -/
noncomputable def left_response {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  (x.move_right j).left_moves :=
classical.some $ (zero_le.1 h) j

/-- Show that the response for left provided by `left_response`
    preserves the left-player-wins condition. -/
lemma left_response_spec {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  0 ≤ (x.move_right j).move_left (left_response h j) :=
classical.some_spec $ (zero_le.1 h) j

theorem lt_of_le_mk {xl xr xL xR y i} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ y → xL i < y :=
by { cases y, rw mk_le_mk, tauto }

theorem lt_of_mk_le {x : pgame} {yl yr yL yR i} :
  x ≤ ⟨yl, yr, yL, yR⟩ → x < yR i :=
by { cases x, rw mk_le_mk, tauto }

theorem mk_lt_of_le {xl xr xL xR y i} :
  ((xR : xr → pgame) i ≤ y) → (⟨xl, xr, xL, xR⟩ : pgame) < y :=
by { cases y, rw mk_lt_mk, tauto }

theorem lt_mk_of_le {x : pgame} {yl yr : Type*} {yL : yl → pgame} {yR i} :
  (x ≤ yL i) → x < ⟨yl, yr, yL, yR⟩ :=
by { cases x, rw mk_lt_mk, exact λ h, or.inl ⟨_, h⟩ }

theorem move_left_lt_of_le {x y : pgame} {i} :
  x ≤ y → x.move_left i < y :=
by { cases x, exact lt_of_le_mk }

theorem lt_move_right_of_le {x y : pgame} {i} :
  x ≤ y → x < y.move_right i :=
by { cases y, exact lt_of_mk_le }

theorem lt_of_move_right_le {x y : pgame} {i} :
  x.move_right i ≤ y → x < y :=
by { cases x, rw move_right_mk, exact mk_lt_of_le }

theorem lt_of_le_move_left {x y : pgame} {i} :
  x ≤ y.move_left i → x < y :=
by { cases y, rw move_left_mk, exact lt_mk_of_le }

private theorem not_le_lt {x y : pgame} :
  (¬ x ≤ y ↔ y < x) ∧ (¬ x < y ↔ y ≤ x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  classical,
  simp only [mk_le_mk, mk_lt_mk,
    not_and_distrib, not_or_distrib, not_forall, not_exists,
    and_comm, or_comm, IHxl, IHxr, IHyl, IHyr, iff_self, and_self]
end

@[simp] theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := not_le_lt.1
@[simp] theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := not_le_lt.2

@[refl] protected theorem le_rfl : ∀ {x : pgame}, x ≤ x
| ⟨l, r, L, R⟩ := by rw mk_le_mk; exact
⟨λ i, lt_mk_of_le le_rfl, λ i, mk_lt_of_le le_rfl⟩

protected theorem le_refl (x : pgame) : x ≤ x :=
pgame.le_rfl

protected theorem lt_irrefl (x : pgame) : ¬ x < x :=
not_lt.2 pgame.le_rfl

protected theorem ne_of_lt : ∀ {x y : pgame}, x < y → x ≠ y
| x _ h rfl := pgame.lt_irrefl x h

/-- In general, `xL i ≤ x` isn't true. It is true however for `numeric` games, see
`numeric.move_left_le`. -/
theorem lt_mk {xl xr : Type u} {xL : xl → pgame} {xR : xr → pgame} (i) : xL i < mk xl xr xL xR :=
lt_mk_of_le pgame.le_rfl

/-- In general, `x ≤ xR i` isn't true. It is true however for `numeric` games, see
`numeric.move_right_le`. -/
theorem mk_lt {xl xr : Type u} {xL : xl → pgame} {xR : xr → pgame} (i) : mk xl xr xL xR < xR i :=
mk_lt_of_le pgame.le_rfl

/-- In general, `x.move_left i ≤ x` isn't true. It is true however for `numeric` games, see
`numeric.move_left_le`. -/
theorem move_left_lt {x : pgame} (i) : x.move_left i < x :=
move_left_lt_of_le pgame.le_rfl

/-- In general, `x ≤ x.move_right i` isn't true. It is true however for `numeric` games, see
`numeric.move_right_le`. -/
theorem lt_move_right {x : pgame} (i) : x < x.move_right i :=
lt_move_right_of_le pgame.le_rfl

theorem le_trans_aux
  {xl xr} {xL : xl → pgame} {xR : xr → pgame}
  {yl yr} {yL : yl → pgame} {yR : yr → pgame}
  {zl zr} {zL : zl → pgame} {zR : zr → pgame}
  (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
  (h₂ : ∀ i, zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) :
  mk xl xr xL xR ≤ mk yl yr yL yR →
  mk yl yr yL yR ≤ mk zl zr zL zR →
  mk xl xr xL xR ≤ mk zl zr zL zR :=
by simp only [mk_le_mk] at *; exact
λ ⟨xLy, xyR⟩ ⟨yLz, yzR⟩, ⟨
  λ i, not_le.1 (λ h, not_lt.2 (h₁ _ ⟨yLz, yzR⟩ h) (xLy _)),
  λ i, not_le.1 (λ h, not_lt.2 (h₂ _ h ⟨xLy, xyR⟩) (yzR _))⟩

@[trans] theorem le_trans {x y z : pgame} : x ≤ y → y ≤ z → x ≤ z :=
suffices ∀ {x y z : pgame},
  (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y),
from this.1, begin
  clear x y z, intros,
  induction x with xl xr xL xR IHxl IHxr generalizing y z,
  induction y with yl yr yL yR IHyl IHyr generalizing z,
  induction z with zl zr zL zR IHzl IHzr,
  exact ⟨
    le_trans_aux (λ i, (IHxl _).2.1) (λ i, (IHzr _).2.2),
    le_trans_aux (λ i, (IHyl _).2.2) (λ i, (IHxr _).1),
    le_trans_aux (λ i, (IHzl _).1) (λ i, (IHyr _).2.1)⟩,
end

@[trans] theorem lt_of_le_of_lt {x y z : pgame} (hxy : x ≤ y) (hyz : y < z) : x < z :=
begin
  rw ←not_le at ⊢ hyz,
  exact mt (λ H, le_trans H hxy) hyz
end

@[trans] theorem lt_of_lt_of_le {x y z : pgame} (hxy : x < y) (hyz : y ≤ z) : x < z :=
begin
  rw ←not_le at ⊢ hxy,
  exact mt (λ H, le_trans hyz H) hxy
end

/-- Define the equivalence relation on pre-games. Two pre-games
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def equiv (x y : pgame) : Prop := x ≤ y ∧ y ≤ x

local infix ` ≈ ` := pgame.equiv

@[refl, simp] theorem equiv_rfl {x} : x ≈ x := ⟨pgame.le_rfl, pgame.le_rfl⟩
theorem equiv_refl (x) : x ≈ x := equiv_rfl
@[symm] theorem equiv_symm {x y} : x ≈ y → y ≈ x | ⟨xy, yx⟩ := ⟨yx, xy⟩
@[trans] theorem equiv_trans {x y z} : x ≈ y → y ≈ z → x ≈ z
| ⟨xy, yx⟩ ⟨yz, zy⟩ := ⟨le_trans xy yz, le_trans zy yx⟩

@[trans]
theorem lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z := lt_of_lt_of_le h₁ h₂.1
@[trans]
theorem le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z := le_trans h₁ h₂.1
@[trans]
theorem lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) (h₂ : y < z) : x < z := lt_of_le_of_lt h₁.1 h₂
@[trans]
theorem le_of_equiv_of_le {x y z} (h₁ : x ≈ y) (h₂ : y ≤ z) : x ≤ z := le_trans h₁.1 h₂

theorem le_congr {x₁ y₁ x₂ y₂} : x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ≤ y₁ ↔ x₂ ≤ y₂)
| ⟨x12, x21⟩ ⟨y12, y21⟩ := ⟨λ h, le_trans x21 (le_trans h y12), λ h, le_trans x12 (le_trans h y21)⟩

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
not_le.symm.trans $ (not_congr (le_congr hy hx)).trans not_le

theorem lt_or_equiv_of_le {x y : pgame} (h : x ≤ y) : x < y ∨ x ≈ y :=
or_iff_not_imp_left.2 $ λ h', ⟨h, not_lt.1 h'⟩

theorem lt_or_equiv_or_gt (x y : pgame) : x < y ∨ x ≈ y ∨ y < x :=
begin
  by_cases h : x < y,
  { exact or.inl h },
  { right,
    cases (lt_or_equiv_of_le (not_lt.1 h)) with h' h',
    { exact or.inr h' },
    { exact or.inl h'.symm } }
end

theorem equiv_congr_left {y₁ y₂} : y₁ ≈ y₂ ↔ ∀ x₁, x₁ ≈ y₁ ↔ x₁ ≈ y₂ :=
⟨λ h x₁, ⟨λ h', equiv_trans h' h, λ h', equiv_trans h' (equiv_symm h)⟩,
 λ h, (h y₁).1 $ equiv_refl _⟩

theorem equiv_congr_right {x₁ x₂} : x₁ ≈ x₂ ↔ ∀ y₁, x₁ ≈ y₁ ↔ x₂ ≈ y₁ :=
⟨λ h y₁, ⟨λ h', equiv_trans (equiv_symm h) h', λ h', equiv_trans h h'⟩,
 λ h, (h x₂).2 $ equiv_refl _⟩

theorem equiv_of_mk_equiv {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ (i : x.left_moves), x.move_left i ≈ y.move_left (L i))
  (hr : ∀ (j : y.right_moves), x.move_right (R.symm j) ≈ y.move_right j) :
  x ≈ y :=
begin
  fsplit; rw le_def,
  { exact ⟨λ i, or.inl ⟨L i, (hl i).1⟩, λ j, or.inr ⟨R.symm j, (hr j).1⟩⟩ },
  { fsplit,
    { intro i,
      left,
      specialize hl (L.symm i),
      simp only [move_left_mk, equiv.apply_symm_apply] at hl,
      use ⟨L.symm i, hl.2⟩ },
    { intro j,
      right,
      specialize hr (R j),
      simp only [move_right_mk, equiv.symm_apply_apply] at hr,
      use ⟨R j, hr.2⟩ } }
end

/-- `restricted x y` says that Left always has no more moves in `x` than in `y`,
     and Right always has no more moves in `y` than in `x` -/
inductive restricted : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π {x y : pgame} (L : x.left_moves → y.left_moves) (R : y.right_moves → x.right_moves),
         (∀ (i : x.left_moves), restricted (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), restricted (x.move_right (R j)) (y.move_right j)) → restricted x y

/-- The identity restriction. -/
@[refl] def restricted.refl : Π (x : pgame), restricted x x
| (mk xl xr xL xR) :=
  restricted.mk
    id id
    (λ i, restricted.refl _) (λ j, restricted.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

instance (x : pgame) : inhabited (restricted x x) := ⟨restricted.refl _⟩

-- TODO trans for restricted

theorem restricted.le : Π {x y : pgame} (r : restricted x y), x ≤ y
| (mk xl xr xL xR) (mk yl yr yL yR)
  (restricted.mk L_embedding R_embedding L_restriction R_restriction) :=
begin
  rw le_def,
  exact
    ⟨λ i, or.inl ⟨L_embedding i, (L_restriction i).le⟩,
     λ i, or.inr ⟨R_embedding i, (R_restriction i).le⟩⟩
end

/--
`relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `relabelling`s for the consequent games.

In ZFC, relabellings would indeed be the same games.
-/
inductive relabelling : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π {x y : pgame} (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ (i : x.left_moves), relabelling (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), relabelling (x.move_right (R.symm j)) (y.move_right j)) →
       relabelling x y

/-- If `x` is a relabelling of `y`, then Left and Right have the same moves in either game,
    so `x` is a restriction of `y`. -/
def relabelling.restricted : Π {x y : pgame} (r : relabelling x y), restricted x y
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk L_equiv R_equiv L_relabelling R_relabelling) :=
restricted.mk L_equiv.to_embedding R_equiv.symm.to_embedding
  (λ i, (L_relabelling i).restricted)
  (λ j, (R_relabelling j).restricted)

-- It's not the case that `restricted x y → restricted y x → relabelling x y`,
-- but if we insisted that the maps in a restriction were injective, then one
-- could use Schröder-Bernstein for do this.

/-- The identity relabelling. -/
@[refl] def relabelling.refl : Π (x : pgame), relabelling x x
| (mk xl xr xL xR) :=
  relabelling.mk (equiv.refl _) (equiv.refl _)
    (λ i, relabelling.refl _) (λ j, relabelling.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

instance (x : pgame) : inhabited (relabelling x x) := ⟨relabelling.refl _⟩

/-- Reverse a relabelling. -/
@[symm] def relabelling.symm : Π {x y : pgame}, relabelling x y → relabelling y x
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk L_equiv R_equiv L_relabelling R_relabelling) :=
begin
  refine relabelling.mk L_equiv.symm R_equiv.symm _ _,
  { intro i, simpa using (L_relabelling (L_equiv.symm i)).symm },
  { intro j, simpa using (R_relabelling (R_equiv j)).symm }
end

/-- Transitivity of relabelling -/
@[trans] def relabelling.trans :
  Π {x y z : pgame}, relabelling x y → relabelling y z → relabelling x z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR)
  (relabelling.mk L_equiv₁ R_equiv₁ L_relabelling₁ R_relabelling₁)
  (relabelling.mk L_equiv₂ R_equiv₂ L_relabelling₂ R_relabelling₂) :=
begin
  refine relabelling.mk (L_equiv₁.trans L_equiv₂) (R_equiv₁.trans R_equiv₂) _ _,
  { intro i, simpa using (L_relabelling₁ _).trans (L_relabelling₂ _) },
  { intro j, simpa using (R_relabelling₁ _).trans (R_relabelling₂ _) },
end

/-- Any game without left or right moves is a relabelling of 0. -/
def relabelling.is_empty (x : pgame) [is_empty (x.left_moves)] [is_empty (x.right_moves)] :
  relabelling x 0 :=
⟨equiv.equiv_pempty _, equiv.equiv_pempty _, is_empty_elim, is_empty_elim⟩

theorem relabelling.le {x y : pgame} (r : relabelling x y) : x ≤ y :=
r.restricted.le

/-- A relabelling lets us prove equivalence of games. -/
theorem relabelling.equiv {x y : pgame} (r : relabelling x y) : x ≈ y :=
⟨r.le, r.symm.le⟩

instance {x y : pgame} : has_coe (relabelling x y) (x ≈ y) := ⟨relabelling.equiv⟩

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : pgame} {xl' xr'} (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') :=
pgame.mk xl' xr' (λ i, x.move_left (el.symm i)) (λ j, x.move_right (er.symm j))

@[simp] lemma relabel_move_left' {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (i : xl') :
  move_left (relabel el er) i = x.move_left (el.symm i) :=
rfl
@[simp] lemma relabel_move_left {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (i : x.left_moves) :
  move_left (relabel el er) (el i) = x.move_left i :=
by simp

@[simp] lemma relabel_move_right' {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (j : xr') :
  move_right (relabel el er) j = x.move_right (er.symm j) :=
rfl
@[simp] lemma relabel_move_right {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (j : x.right_moves) :
  move_right (relabel el er) (er j) = x.move_right j :=
by simp

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabel_relabelling {x : pgame} {xl' xr'} (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') :
  relabelling x (relabel el er) :=
relabelling.mk el er (λ i, by simp) (λ j, by simp)

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : pgame → pgame
| ⟨l, r, L, R⟩ := ⟨r, l, λ i, neg (R i), λ i, neg (L i)⟩

instance : has_neg pgame := ⟨neg⟩

@[simp] lemma neg_def {xl xr xL xR} : -(mk xl xr xL xR) = mk xr xl (λ j, -(xR j)) (λ i, -(xL i)) :=
rfl

instance : has_involutive_neg pgame :=
{ neg_neg := λ x, begin
    induction x with xl xr xL xR ihL ihR,
    simp_rw [neg_def, ihL, ihR],
    exact ⟨rfl, rfl, heq.rfl, heq.rfl⟩,
  end,
  ..pgame.has_neg }

@[simp] protected lemma neg_zero : -(0 : pgame) = 0 :=
begin
  dsimp [has_zero.zero, has_neg.neg, neg],
  congr; funext i; cases i
end

@[simp] lemma neg_of_lists (L R : list pgame) :
  -of_lists L R = of_lists (R.map (λ x, -x)) (L.map (λ x, -x)) :=
begin
  simp only [of_lists, neg_def, list.length_map, list.nth_le_map', eq_self_iff_true, true_and],
  split, all_goals
  { apply hfunext,
    { simp },
    { intros a a' ha,
      congr' 2,
      have : ∀ {m n} (h₁ : m = n) {b : ulift (fin m)} {c : ulift (fin n)} (h₂ : b == c),
        (b.down : ℕ) = ↑c.down,
      { rintros m n rfl b c rfl, refl },
      exact this (list.length_map _ _).symm ha } }
end

theorem left_moves_neg : ∀ x : pgame, (-x).left_moves = x.right_moves
| ⟨_, _, _, _⟩ := rfl

theorem right_moves_neg : ∀ x : pgame, (-x).right_moves = x.left_moves
| ⟨_, _, _, _⟩ := rfl

/-- Turns a right move for `x` into a left move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def to_left_moves_neg {x : pgame} : x.right_moves ≃ (-x).left_moves :=
equiv.cast (left_moves_neg x).symm

/-- Turns a left move for `x` into a right move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def to_right_moves_neg {x : pgame} : x.left_moves ≃ (-x).right_moves :=
equiv.cast (right_moves_neg x).symm

lemma move_left_neg {x : pgame} (i) :
  (-x).move_left (to_left_moves_neg i) = -x.move_right i :=
by { cases x, refl }

@[simp] lemma move_left_neg' {x : pgame} (i) :
  (-x).move_left i = -x.move_right (to_left_moves_neg.symm i) :=
by { cases x, refl }

lemma move_right_neg {x : pgame} (i) :
  (-x).move_right (to_right_moves_neg i) = -(x.move_left i) :=
by { cases x, refl }

@[simp] lemma move_right_neg' {x : pgame} (i) :
  (-x).move_right i = -x.move_left (to_right_moves_neg.symm i) :=
by { cases x, refl }

lemma move_left_neg_symm {x : pgame} (i) :
  x.move_left (to_right_moves_neg.symm i) = -(-x).move_right i :=
by simp

lemma move_left_neg_symm' {x : pgame} (i) :
  x.move_left i = -(-x).move_right (to_right_moves_neg i) :=
by simp

lemma move_right_neg_symm {x : pgame} (i) :
  x.move_right (to_left_moves_neg.symm i) = -(-x).move_left i :=
by simp

lemma move_right_neg_symm' {x : pgame} (i) :
  x.move_right i = -(-x).move_left (to_left_moves_neg i) :=
by simp

/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
def relabelling.neg_congr : ∀ {x y : pgame}, x.relabelling y → (-x).relabelling (-y)
| (mk xl xr xL xR) (mk yl yr yL yR) ⟨L_equiv, R_equiv, L_relabelling, R_relabelling⟩ :=
  ⟨R_equiv, L_equiv,
    λ i, relabelling.neg_congr (by simpa using R_relabelling (R_equiv i)),
    λ i, relabelling.neg_congr (by simpa using L_relabelling (L_equiv.symm i))⟩

theorem le_iff_neg_ge : Π {x y : pgame}, x ≤ y ↔ -y ≤ -x
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  rw [le_def, le_def],
  dsimp [neg],
  refine ⟨λ h, ⟨λ i, _, λ j, _⟩, λ h, ⟨λ i, _, λ j, _⟩⟩,
  { rcases h.right i with ⟨w, h⟩ | ⟨w, h⟩,
    { refine or.inr ⟨to_right_moves_neg w, _⟩,
      convert le_iff_neg_ge.1 h,
      rw move_right_neg },
    { exact or.inl ⟨w, le_iff_neg_ge.1 h⟩ } },
  { rcases h.left j with ⟨w, h⟩ | ⟨w, h⟩,
    { exact or.inr ⟨w, le_iff_neg_ge.1 h⟩ },
    { refine or.inl ⟨to_left_moves_neg w, _⟩,
      convert le_iff_neg_ge.1 h,
      rw move_left_neg } },
  { rcases h.right i with ⟨w, h⟩ | ⟨w, h⟩,
    { refine or.inr ⟨to_left_moves_neg.symm w, le_iff_neg_ge.2 _⟩,
      rwa [move_right_neg_symm, neg_neg] },
    { exact or.inl ⟨w, le_iff_neg_ge.2 h⟩ } },
  { rcases h.left j with ⟨w, h⟩ | ⟨w, h⟩,
    { exact or.inr ⟨w, le_iff_neg_ge.2 h⟩ },
    { refine or.inl ⟨to_right_moves_neg.symm w, le_iff_neg_ge.2 _⟩,
      rwa [move_left_neg_symm, neg_neg] } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_congr {x y : pgame} (h : x ≈ y) : -x ≈ -y :=
⟨le_iff_neg_ge.1 h.2, le_iff_neg_ge.1 h.1⟩

theorem lt_iff_neg_gt : Π {x y : pgame}, x < y ↔ -y < -x :=
begin
  classical,
  intros,
  rw [←not_le, ←not_le, not_iff_not],
  apply le_iff_neg_ge
end

theorem zero_le_iff_neg_le_zero {x : pgame} : 0 ≤ x ↔ -x ≤ 0 :=
begin
  convert le_iff_neg_ge,
  rw pgame.neg_zero
end

theorem le_zero_iff_zero_le_neg {x : pgame} : x ≤ 0 ↔ 0 ≤ -x :=
begin
  convert le_iff_neg_ge,
  rw pgame.neg_zero
end

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add (x y : pgame) : pgame :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
  { exact λ i, IHxl i y },
  { exact λ i, IHyl i },
  { exact λ i, IHxr i y },
  { exact λ i, IHyr i }
end

instance : has_add pgame := ⟨add⟩

@[simp] theorem nat_one : ((1 : ℕ) : pgame) = 0 + 1 := rfl

/-- `x + 0` has exactly the same moves as `x`. -/
def add_zero_relabelling : Π (x : pgame.{u}), relabelling (x + 0) x
| (mk xl xr xL xR) :=
begin
  refine ⟨equiv.sum_empty xl pempty, equiv.sum_empty xr pempty, _, _⟩,
  { rintro (⟨i⟩|⟨⟨⟩⟩),
    apply add_zero_relabelling, },
  { rintro j,
    apply add_zero_relabelling, }
end

/-- `x + 0` is equivalent to `x`. -/
lemma add_zero_equiv (x : pgame.{u}) : x + 0 ≈ x :=
(add_zero_relabelling x).equiv

/-- `0 + x` has exactly the same moves as `x`. -/
def zero_add_relabelling : Π (x : pgame.{u}), relabelling (0 + x) x
| (mk xl xr xL xR) :=
begin
  refine ⟨equiv.empty_sum pempty xl, equiv.empty_sum pempty xr, _, _⟩,
  { rintro (⟨⟨⟩⟩|⟨i⟩),
    apply zero_add_relabelling, },
  { rintro j,
    apply zero_add_relabelling, }
end

/-- `0 + x` is equivalent to `x`. -/
lemma zero_add_equiv (x : pgame.{u}) : 0 + x ≈ x :=
(zero_add_relabelling x).equiv

/-- An explicit equivalence between the moves for Left in `x + y` and the type-theory sum
    of the moves for Left in `x` and in `y`. -/
def left_moves_add (x y : pgame) : (x + y).left_moves ≃ x.left_moves ⊕ y.left_moves :=
by { cases x, cases y, refl, }

/-- An explicit equivalence between the moves for Right in `x + y` and the type-theory sum
    of the moves for Right in `x` and in `y`. -/
def right_moves_add (x y : pgame) : (x + y).right_moves ≃ x.right_moves ⊕ y.right_moves :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inl i) =
    (mk xl xr xL xR).move_left i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_left_inl {x y : pgame} {i} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inl i)) = x.move_left i + y :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inl i) =
    (mk xl xr xL xR).move_right i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_right_inl {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inl i)) = x.move_right i + y :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_left i :=
rfl
@[simp] lemma add_move_left_inr {x y : pgame} {i : y.left_moves} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inr i)) = x + y.move_left i :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_right i :=
rfl
@[simp] lemma add_move_right_inr {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inr i)) = x + y.move_right i :=
by { cases x, cases y, refl, }

instance is_empty_nat_right_moves : ∀ n : ℕ, is_empty (right_moves n)
| 0 := pempty.is_empty
| (n + 1) := begin
  haveI := is_empty_nat_right_moves n,
  rw nat.cast_succ,
  exact (right_moves_add _ _).is_empty
end

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def relabelling.add_congr : ∀ {w x y z : pgame.{u}},
  w.relabelling x → y.relabelling z → (w + y).relabelling (x + z)
| (mk wl wr wL wR) (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR)
  ⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩
  ⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩ :=
begin
  refine ⟨equiv.sum_congr L_equiv₁ L_equiv₂, equiv.sum_congr R_equiv₁ R_equiv₂, _, _⟩,
  { rintro (i|j),
    { exact relabelling.add_congr
        (L_relabelling₁ i)
        (⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩) },
    { exact relabelling.add_congr
        (⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩)
        (L_relabelling₂ j) }},
  { rintro (i|j),
    { exact relabelling.add_congr
        (R_relabelling₁ i)
        (⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩) },
    { exact relabelling.add_congr
        (⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩)
        (R_relabelling₂ j) }}
end
using_well_founded { dec_tac := pgame_wf_tac }

instance : has_sub pgame := ⟨λ x y, x + -y⟩

@[simp] theorem sub_zero (x : pgame) : x - 0 = x + 0 :=
show x + -0 = x + 0, by rw pgame.neg_zero

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def relabelling.sub_congr {w x y z : pgame}
  (h₁ : w.relabelling x) (h₂ : y.relabelling z) : (w - y).relabelling (x - z) :=
h₁.add_congr h₂.neg_congr

/-- `-(x+y)` has exactly the same moves as `-x + -y`. -/
def neg_add_relabelling : Π (x y : pgame), relabelling (-(x + y)) (-x + -y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
⟨equiv.refl _, equiv.refl _,
 λ j, sum.cases_on j
   (λ j, neg_add_relabelling (xR j) (mk yl yr yL yR))
   (λ j, neg_add_relabelling (mk xl xr xL xR) (yR j)),
 λ i, sum.cases_on i
   (λ i, neg_add_relabelling (xL i) (mk yl yr yL yR))
   (λ i, neg_add_relabelling (mk xl xr xL xR) (yL i))⟩
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_add_le {x y : pgame} : -(x + y) ≤ -x + -y :=
(neg_add_relabelling x y).le

/-- `x + y` has exactly the same moves as `y + x`. -/
def add_comm_relabelling : Π (x y : pgame.{u}), relabelling (x + y) (y + x)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  refine ⟨equiv.sum_comm _ _, equiv.sum_comm _ _, _, _⟩;
  rintros (_|_);
  { simp [left_moves_add, right_moves_add], apply add_comm_relabelling }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_comm_le {x y : pgame} : x + y ≤ y + x :=
(add_comm_relabelling x y).le

theorem add_comm_equiv {x y : pgame} : x + y ≈ y + x :=
(add_comm_relabelling x y).equiv

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def add_assoc_relabelling : Π (x y z : pgame.{u}), relabelling ((x + y) + z) (x + (y + z))
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  refine ⟨equiv.sum_assoc _ _ _, equiv.sum_assoc _ _ _, _, _⟩,
  { rintro (⟨i|i⟩|i),
    { apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + yL i + mk zl zr zL zR) (mk xl xr xL xR + (yL i + mk zl zr zL zR)),
      apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + mk yl yr yL yR + zL i) (mk xl xr xL xR + (mk yl yr yL yR + zL i)),
      apply add_assoc_relabelling, } },
  { rintro (j|⟨j|j⟩),
    { apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + yR j + mk zl zr zL zR) (mk xl xr xL xR + (yR j + mk zl zr zL zR)),
      apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + mk yl yr yL yR + zR j) (mk xl xr xL xR + (mk yl yr yL yR + zR j)),
      apply add_assoc_relabelling, } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_assoc_equiv {x y z : pgame} : (x + y) + z ≈ x + (y + z) :=
(add_assoc_relabelling x y z).equiv

private lemma add_le_add_right : ∀ {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  intros h,
  rw le_def,
  split,
  { -- if Left plays first
    intros i,
    change xl ⊕ zl at i,
    cases i,
    { -- either they play in x
      rw le_def at h,
      cases h,
      have t := h_left i,
      rcases t with ⟨i', ih⟩ | ⟨j, jh⟩,
      { left,
        refine ⟨(left_moves_add _ _).inv_fun (sum.inl i'), _⟩,
        exact add_le_add_right ih, },
      { right,
        refine ⟨(right_moves_add _ _).inv_fun (sum.inl j), _⟩,
        convert add_le_add_right jh,
        apply add_move_right_inl } },
    { -- or play in z
      left,
      refine ⟨(left_moves_add _ _).inv_fun (sum.inr i), _⟩,
      exact add_le_add_right h, }, },
  { -- if Right plays first
    intros j,
    change yr ⊕ zr at j,
    cases j,
    { -- either they play in y
      rw le_def at h,
      cases h,
      have t := h_right j,
      rcases t with ⟨i, ih⟩ | ⟨j', jh⟩,
      { left,
        refine ⟨(left_moves_add _ _).inv_fun (sum.inl i), _⟩,
        convert add_le_add_right ih,
        apply add_move_left_inl },
      { right,
        refine ⟨(right_moves_add _ _).inv_fun (sum.inl j'), _⟩,
        exact add_le_add_right jh } },
    { -- or play in z
      right,
      refine ⟨(right_moves_add _ _).inv_fun (sum.inr j), _⟩,
      exact add_le_add_right h } }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance covariant_class_swap_add_le : covariant_class pgame pgame (swap (+)) (≤) :=
⟨λ x y z, add_le_add_right⟩

instance covariant_class_add_le : covariant_class pgame pgame (+) (≤) :=
⟨λ x y z h, calc x + y ≤ y + x : add_comm_le
                   ... ≤ z + x : add_le_add_right h _
                   ... ≤ x + z : add_comm_le⟩

theorem add_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
⟨le_trans (add_le_add_left h₂.1 w) (add_le_add_right h₁.1 z),
  le_trans (add_le_add_left h₂.2 x) (add_le_add_right h₁.2 y)⟩

theorem add_congr_left {x y z : pgame} (h : x ≈ y) : x + z ≈ y + z :=
add_congr h equiv_rfl

theorem add_congr_right {x y z : pgame} : y ≈ z → x + y ≈ x + z :=
add_congr equiv_rfl

theorem sub_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
add_congr h₁ (neg_congr h₂)

theorem sub_congr_left {x y z : pgame} (h : x ≈ y) : x - z ≈ y - z :=
sub_congr h equiv_rfl

theorem sub_congr_right {x y z : pgame} : y ≈ z → x - y ≈ x - z :=
sub_congr equiv_rfl

theorem add_left_neg_le_zero : ∀ (x : pgame), -x + x ≤ 0
| ⟨xl, xr, xL, xR⟩ :=
begin
  rw [le_def],
  split,
  { intro i,
    change xr ⊕ xl at i,
    cases i,
    { -- If Left played in -x, Right responds with the same move in x.
      right,
      refine ⟨(right_moves_add _ _).inv_fun (sum.inr i), _⟩,
      convert @add_left_neg_le_zero (xR i),
      exact add_move_right_inr },
    { -- If Left in x, Right responds with the same move in -x.
      right,
      dsimp,
      refine ⟨(right_moves_add _ _).inv_fun (sum.inl i), _⟩,
      convert @add_left_neg_le_zero (xL i),
      exact add_move_right_inl }, },
  { rintro ⟨⟩, }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem zero_le_add_left_neg (x : pgame) : 0 ≤ -x + x :=
begin
  rw [le_iff_neg_ge, pgame.neg_zero],
  exact le_trans neg_add_le (add_left_neg_le_zero _)
end

theorem add_left_neg_equiv (x : pgame) : -x + x ≈ 0 :=
⟨add_left_neg_le_zero x, zero_le_add_left_neg x⟩

theorem add_right_neg_le_zero (x : pgame) : x + -x ≤ 0 :=
le_trans add_comm_le (add_left_neg_le_zero x)

theorem zero_le_add_right_neg (x : pgame) : 0 ≤ x + -x :=
le_trans (zero_le_add_left_neg x) add_comm_le

theorem add_right_neg_equiv (x : pgame) : x + -x ≈ 0 :=
⟨add_right_neg_le_zero x, zero_le_add_right_neg x⟩

instance covariant_class_swap_add_lt : covariant_class pgame pgame (swap (+)) (<) :=
⟨λ x y z h, suffices z + x ≤ y + x → z ≤ y, by { rw ←not_le at ⊢ h, exact mt this h }, λ w,
  calc z ≤ z + 0        : (add_zero_relabelling _).symm.le
     ... ≤ z + (x + -x) : add_le_add_left (zero_le_add_right_neg x) _
     ... ≤ z + x + -x   : (add_assoc_relabelling _ _ _).symm.le
     ... ≤ y + x + -x   : add_le_add_right w _
     ... ≤ y + (x + -x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0        : add_le_add_left (add_right_neg_le_zero x) _
     ... ≤ y            : (add_zero_relabelling _).le⟩

instance covariant_class_add_lt : covariant_class pgame pgame (+) (<) :=
⟨λ x y z h, calc x + y ≤ y + x : add_comm_le
                   ... < z + x   : add_lt_add_right h _
                   ... ≤ x + z   : add_comm_le⟩

theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x :=
⟨λ h, le_trans (zero_le_add_right_neg x) (add_le_add_right h _),
 λ h,
  calc x ≤ 0 + x : (zero_add_relabelling x).symm.le
     ... ≤ y - x + x : add_le_add_right h _
     ... ≤ y + (-x + x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero x) _
     ... ≤ y : (add_zero_relabelling y).le⟩
theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x :=
⟨λ h, lt_of_le_of_lt (zero_le_add_right_neg x) (add_lt_add_right h _),
 λ h,
  calc x ≤ 0 + x : (zero_add_relabelling x).symm.le
     ... < y - x + x : add_lt_add_right h _
     ... ≤ y + (-x + x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero x) _
     ... ≤ y : (add_zero_relabelling y).le⟩

/-- The pre-game `star`, which is fuzzy/confused with zero. -/
def star : pgame.{u} := ⟨punit, punit, λ _, 0, λ _, 0⟩

@[simp] theorem star_left_moves : star.left_moves = punit := rfl
@[simp] theorem star_right_moves : star.right_moves = punit := rfl

@[simp] theorem star_move_left (x) : star.move_left x = 0 := rfl
@[simp] theorem star_move_right (x) : star.move_right x = 0 := rfl

instance unique_star_left_moves : unique star.left_moves := punit.unique
instance unique_star_right_moves : unique star.right_moves := punit.unique

theorem star_lt_zero : star < 0 :=
by { rw lt_zero, use default, rintros ⟨⟩ }
theorem zero_lt_star : 0 < star :=
by { rw zero_lt, use default, rintros ⟨⟩ }

@[simp] theorem neg_star : -star = star :=
by simp [star]

@[simp] theorem zero_lt_one : (0 : pgame) < 1 :=
by { rw zero_lt, use default, rintro ⟨⟩ }

theorem zero_le_one : (0 : pgame) ≤ 1 :=
zero_le_of_is_empty_right_moves 1

/-- The pre-game `half` is defined as `{0 | 1}`. -/
def half : pgame := ⟨punit, punit, 0, 1⟩

@[simp] theorem half_left_moves : half.left_moves = punit := rfl
@[simp] theorem half_right_moves : half.right_moves = punit := rfl
@[simp] lemma half_move_left (x) : half.move_left x = 0 := rfl
@[simp] lemma half_move_right (x) : half.move_right x = 1 := rfl

instance unique_half_left_moves : unique half.left_moves := punit.unique
instance unique_half_right_moves : unique half.right_moves := punit.unique

protected theorem zero_lt_half : 0 < half :=
by { rw zero_lt, use default, rintro ⟨⟩ }

theorem half_lt_one : half < 1 :=
begin
  rw lt_def,
  right,
  use default,
  split; rintro ⟨⟩,
  exact zero_lt_one
end

end pgame
