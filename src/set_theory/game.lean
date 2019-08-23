/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import data.equiv.basic logic.embedding
import data.nat.cast
import data.finset data.fintype

/-!
# Combinatorial games.

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`. We
construct "pregames", define an ordering and arithmetic operations on them, then show that the
operations descend to "games", defined via the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a subtype.

A pregame (`pgame` below) is axiomatised via an inductive type, whose sole constructor takes two
types (thought of as indexing the the possible moves for the players Left and Right), and a pair of
functions out of these types to `pgame` (thought of as describing the resulting game after making a
move).

## Conway induction

By construction, the induction principle for pregames is exactly "Conway induction". That is, to
prove some predicate `pgame → Prop` holds for all pregames, it suffices to prove that for every
pregame `g`, if the predicate holds for every game resulting from making a move, then it also holds
for `g`.

While it is often convenient to work "by induction" on pregames, in some situations this becomes
awkward, so we also define accessor functions `left_moves`, `right_moves`, `move_left` and
`move_right`. There is a relation `subsequent p q`, saying that `p` can be reached by playing some
sequence of moves starting from `q`, an instance `well_founded subsequent`, and a local tactic
`pgame_wf_tac` which is helpful for discharging proof obligations in inductive proofs relying on this
relation.

## Order properties

Pregames have both a `≤` and a `<` relation, which are related in quite a subtle way. In
particular, it is worth noting that they _do not_ satisfy the axioms of a partial order.

The statement `0 ≤ x` means that Left has a good response to any move by Right; in particular,
the theorem `zero_le` below states
```
0 ≤ x ↔ ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i
```
On the other hand the statement `0 < x` means that Left has a good move; in particular
the theorem `zero_lt` below states
```
0 < x ↔ ∃ i : left_moves x, ∀ j : right_moves (x.move_left i), 0 < (x.move_left i).move_right j
```
The theorems `le_def`, `lt_def`, `le_def_lt` and `lt_def_lt` give recursive characterisations of the
two relations.

We define an equivalence relation `equiv p q ↔ p ≤ q ∧ q ≤ p`. Later, games will be defined as the
quotient by this relation.

## Algebraic structures

We next turn to defining the operations necessary to make games into a commutative additive group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by
$x + y = \{xL + y, x + yL | xR + y, x + yR\}$.
Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$. We show that these operations respect the
equivalence relation, and hence descend to games.
At the level of games, these operations satisfy all the laws of a commutative group. To prove
the necessary equivalence relations at the level of pregames, we introduce the notion of a `relabelling`
of a game, and show, for example, that there is a relabelling between `x + (y + z)` and `(x + y) + z`.

## References

The material here is all drawn from
* [Conway, *On numbers and games*][conway2001]

An interested reader may like to formalise some of the material from
* [Andreas Blass, *A game semantics for linear logic*][MR1167694]
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1997]
-/

universes u

/-- The type of pre-games, before we have quotiented
  by extensionality. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive pgame : Type (u+1)
| mk : ∀ α β : Type u, (α → pgame) → (β → pgame) → pgame

namespace pgame

/-- Construct a pre-game from list of pre-games describing the available moves for Left and Right. -/
-- TODO provide some API describing the interaction with `left_moves`, `right_moves`, `move_left` and `move_right` below.
-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
def of_lists (L R : list pgame.{0}) : pgame.{0} :=
pgame.mk (fin L.length) (fin R.length) (λ i, L.nth_le i.val i.is_lt) (λ j, R.nth_le j.val j.is_lt)

/-- The indexing type for allowable moves by Left. -/
def left_moves : pgame → Type u
| (mk l _ _ _) := l
/-- The indexing type for allowable moves by Right. -/
def right_moves : pgame → Type u
| (mk _ r _ _) := r

/-- The new game after Left makes an allowed move. -/
def move_left : Π (g : pgame), left_moves g → pgame
| (mk l _ L _) i := L i
/-- The new game after Right makes an allowed move. -/
def move_right : Π (g : pgame), right_moves g → pgame
| (mk _ r _ R) j := R j

@[simp] lemma left_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).left_moves = xl := rfl
@[simp] lemma move_left_mk {xl xr xL xR i} : (⟨xl, xr, xL, xR⟩ : pgame).move_left i = xL i := rfl
@[simp] lemma right_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).right_moves = xr := rfl
@[simp] lemma move_right_mk {xl xr xL xR j} : (⟨xl, xr, xL, xR⟩ : pgame).move_right j = xR j := rfl

/-- `subsequent p q` says that `p` can be obtained by playing some sequence of moves from `q`. -/
inductive subsequent : pgame → pgame → Prop
| left : Π (x : pgame) (i : x.left_moves), subsequent (x.move_left i) x
| right : Π (x : pgame) (j : x.right_moves), subsequent (x.move_right j) x
| trans : Π (x y z : pgame), subsequent x y → subsequent y z → subsequent x z

theorem wf_subsequent : well_founded subsequent :=
⟨λ x, begin
  induction x with l r L R IHl IHr,
  refine ⟨_, λ y h, _⟩,
  generalize_hyp e : mk l r L R = x at h,
  induction h with _ i _ j a b _ h1 h2 IH1 IH2; subst e,
  { apply IHl },
  { apply IHr },
  { exact acc.inv (IH2 rfl) h1 }
end⟩

instance : has_well_founded pgame :=
{ r := subsequent,
  wf := wf_subsequent }

/-- A move by Left produces a subsequent game. -/
def subsequent.left_move {xl xr} {xL : xl → pgame} {xR : xr → pgame} {i : xl} :
  subsequent (xL i) (mk xl xr xL xR) :=
subsequent.left (mk xl xr xL xR) (by { convert i, refl })
/-- A move by Right produces a subsequent game. -/
def subsequent.right_move {xl xr} {xL : xl → pgame} {xR : xr → pgame} {j : xr} :
  subsequent (xR j) (mk xl xr xL xR) :=
subsequent.right (mk xl xr xL xR) (by { convert j, refl })

/-- A local tactic for proving well-foundedness of recursive definitions involving pregames. -/
meta def pgame_wf_tac :=
`[solve_by_elim
  [psigma.lex.left, psigma.lex.right,
   subsequent.left_move, subsequent.right_move,
   subsequent.left, subsequent.right, subsequent.trans]
  { max_rep := 6 }]

/-- The pre-game `zero` is defined by `0 = { | }`. -/
instance : has_zero pgame := ⟨⟨pempty, pempty, pempty.elim, pempty.elim⟩⟩

@[simp] lemma zero_left_moves : (0 : pgame).left_moves = pempty := rfl
@[simp] lemma zero_right_moves : (0 : pgame).right_moves = pempty := rfl

/-- The pre-game `one` is defined by `1 = { 0 | }`. -/
instance : has_one pgame := ⟨⟨punit, pempty, λ _, 0, pempty.elim⟩⟩

@[simp] lemma one_left_moves : (1 : pgame).left_moves = punit := rfl
@[simp] lemma one_move_left : (1 : pgame).move_left punit.star = 0 := rfl
@[simp] lemma one_right_moves : (1 : pgame).right_moves = pempty := rfl

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on pre-games. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  The solution is to define `x < y` and `x <= y` simultaneously. -/
def le_lt (x y : pgame) : Prop × Prop :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  -- the orderings of the clauses here are carefully chosen so that
  --   and.left/or.inl refer to moves by Left, and
  --   and.right/or.inr refer to moves by Right.
  exact ((∀ i, (IHxl i ⟨yl, yr, yL, yR⟩).2) ∧ (∀ j, (IHyr j).2),
         (∃ i, (IHyl i).1) ∨ (∃ j, (IHxr j ⟨yl, yr, yL, yR⟩).1))
end

instance : has_le pgame := ⟨λ x y, (le_lt x y).1⟩
instance : has_lt pgame := ⟨λ x y, (le_lt x y).2⟩

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ ⟨yl, yr, yL, yR⟩ ↔
  (∀ i, xL i < ⟨yl, yr, yL, yR⟩) ∧
  (∀ j, (⟨xl, xr, xL, xR⟩ : pgame) < yR j) := iff.rfl

/-- Definition of `x ≤ y` on pre-games, in terms of `<` -/
theorem le_def_lt {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves, x.move_left i < y) ∧
  (∀ j : y.right_moves, x < y.move_right j) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  simp,
  refl,
end

/-- Definition of `x < y` on pre-games built using the constructor. -/
@[simp] theorem mk_lt_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) < ⟨yl, yr, yL, yR⟩ ↔
  (∃ i, (⟨xl, xr, xL, xR⟩ : pgame) ≤ yL i) ∨
  (∃ j, xR j ≤ ⟨yl, yr, yL, yR⟩) := iff.rfl

/-- Definition of `x < y` on pre-games, in terms of `≤` -/
theorem lt_def_le {x y : pgame} : x < y ↔
  (∃ i : y.left_moves, x ≤ y.move_left i) ∨
  (∃ j : x.right_moves, x.move_right j ≤ y) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  simp,
  refl,
end

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves,
   (∃ i' : y.left_moves, (x.move_left i) ≤ (y.move_left i')) ∨
   (∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ y)) ∧
  (∀ j : y.right_moves,
   (∃ i : (y.move_right j).left_moves, x ≤ (y.move_right j).move_left i) ∨
   (∃ j' : x.right_moves, x.move_right j' ≤ (y.move_right j))) :=
begin
  rw [le_def_lt],
  conv { to_lhs, simp [lt_def_le] },
end

/-- The definition of `x < y` on pre-games, in terms of `<` two moves later. -/
theorem lt_def {x y : pgame} : x < y ↔
  (∃ (i : left_moves y),
    (∀ (i' : left_moves x), move_left x i' < move_left y i) ∧
    (∀ (j : right_moves (move_left y i)), x < move_right (move_left y i) j)) ∨
  (∃ (j : right_moves x),
    (∀ (i : left_moves (move_right x j)), move_left (move_right x j) i < y) ∧
    (∀ (j' : right_moves y), move_right x j < move_right y j')) :=
begin
  rw [lt_def_le],
  conv { to_lhs, simp [le_def_lt] },
end

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : pgame} : x ≤ 0 ↔
  ∀ i : x.left_moves, ∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ 0 :=
begin
  rw le_def,
  conv { to_lhs, congr, skip, erw [forall_pempty], },
  rw [and_true],
  constructor,
  { intros h i,
    have hi := h i,
    erw exists_pempty at hi,
    simpa using hi, },
  { intros h i,
    erw exists_pempty,
    rw [false_or],
    exact h i }
end

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : pgame} : 0 ≤ x ↔
  ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i :=
begin
  rw le_def,
  conv { to_lhs, congr, erw [forall_pempty], },
  rw [true_and],
  constructor,
  { intros h j,
    have hj := h j,
    erw exists_pempty at hj,
    simpa using hj, },
  { intros h j,
    erw exists_pempty,
    rw [or_false],
    exact h j }
end

/-- The definition of `x < 0` on pre-games, in terms of `< 0` two moves later. -/
theorem lt_zero {x : pgame} : x < 0 ↔
  ∃ j : right_moves x, ∀ i : left_moves (x.move_right j), (x.move_right j).move_left i < 0 :=
begin
  rw lt_def,
  conv { to_lhs, congr, erw [exists_pempty], },
  rw [false_or],
  constructor,
  { rintros ⟨j, ⟨h₁, h₂⟩⟩,
    use j,
    exact h₁ },
  { rintros ⟨j, h⟩,
    use j,
    split,
    { exact h, },
    { rintros ⟨⟩, } }
end

/-- The definition of `0 < x` on pre-games, in terms of `< x` two moves later. -/
theorem zero_lt {x : pgame} : 0 < x ↔
  ∃ i : left_moves x, ∀ j : right_moves (x.move_left i), 0 < (x.move_left i).move_right j :=
begin
  rw lt_def,
  conv { to_lhs, congr, skip, erw [exists_pempty], },
  rw [or_false],
  constructor,
  { rintros ⟨j, ⟨h₁, h₂⟩⟩,
    use j,
    exact h₂ },
  { rintros ⟨j, h⟩,
    use j,
    split,
    { rintros ⟨⟩, },
    { exact h, } }
end

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
by cases y; exact λ h, h.1 i

theorem lt_of_mk_le {x : pgame} {yl yr yL yR i} :
  x ≤ ⟨yl, yr, yL, yR⟩ → x < yR i :=
by cases x; exact λ h, h.2 i

theorem mk_lt_of_le {xl xr xL xR y i} :
  (by exact xR i ≤ y) → (⟨xl, xr, xL, xR⟩ : pgame) < y :=
by cases y; exact λ h, or.inr ⟨i, h⟩

theorem lt_mk_of_le {x : pgame} {yl yr yL yR i} :
  (by exact x ≤ yL i) → x < ⟨yl, yr, yL, yR⟩ :=
by cases x; exact λ h, or.inl ⟨i, h⟩

theorem not_le_lt {x y : pgame} :
  (¬ x ≤ y ↔ y < x) ∧ (¬ x < y ↔ y ≤ x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  classical,
  simp [not_and_distrib, not_or_distrib, not_forall, not_exists,
    and_comm, or_comm, IHxl, IHxr, IHyl, IHyr]
end

theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := not_le_lt.1
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := not_le_lt.2

@[refl] theorem le_refl : ∀ x : pgame, x ≤ x
| ⟨l, r, L, R⟩ :=
  ⟨λ i, lt_mk_of_le (le_refl _), λ i, mk_lt_of_le (le_refl _)⟩

theorem lt_irrefl (x : pgame) : ¬ x < x :=
not_lt.2 (le_refl _)

theorem ne_of_lt : ∀ {x y : pgame}, x < y → x ≠ y
| x _ h rfl := lt_irrefl x h

theorem le_trans_aux
  {xl xr} {xL : xl → pgame} {xR : xr → pgame}
  {yl yr} {yL : yl → pgame} {yR : yr → pgame}
  {zl zr} {zL : zl → pgame} {zR : zr → pgame}
  (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
  (h₂ : ∀ i, zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) :
  mk xl xr xL xR ≤ mk yl yr yL yR →
  mk yl yr yL yR ≤ mk zl zr zL zR →
  mk xl xr xL xR ≤ mk zl zr zL zR :=
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

/-- Define the equivalence relation on pre-games. Two pre-games
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def equiv (x y : pgame) : Prop := x ≤ y ∧ y ≤ x

local infix ` ≈ ` := pgame.equiv

@[refl] theorem equiv_refl (x) : x ≈ x := ⟨le_refl _, le_refl _⟩
@[symm] theorem equiv_symm {x y} : x ≈ y → y ≈ x | ⟨xy, yx⟩ := ⟨yx, xy⟩
@[trans] theorem equiv_trans {x y z} : x ≈ y → y ≈ z → x ≈ z
| ⟨xy, yx⟩ ⟨yz, zy⟩ := ⟨le_trans xy yz, le_trans zy yx⟩

theorem le_congr {x₁ y₁ x₂ y₂} : x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ≤ y₁ ↔ x₂ ≤ y₂)
| ⟨x12, x21⟩ ⟨y12, y21⟩ := ⟨λ h, le_trans x21 (le_trans h y12), λ h, le_trans x12 (le_trans h y21)⟩

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
not_le.symm.trans $ (not_congr (le_congr hy hx)).trans not_le

/-- `restricted x y` says that Left always has no more moves in `x` than in `y`,
     and Right always has no more moves in `y` than in `x` -/
inductive restricted : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π (x y : pgame) (L : x.left_moves ↪ y.left_moves) (R : y.right_moves ↪ x.right_moves),
         (∀ (i : x.left_moves), restricted (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), restricted (x.move_right (R j)) (y.move_right j)) → restricted x y

/-- The identity restriction. -/
@[refl] def restricted.refl : Π (x : pgame), restricted x x
| (mk xl xr xL xR) :=
  restricted.mk (mk xl xr xL xR) (mk xl xr xL xR)
    (function.embedding.refl _) (function.embedding.refl _)
    (λ i, restricted.refl _) (λ j, restricted.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

-- TODO trans for restricted

theorem le_of_restricted : Π {x y : pgame} (r : restricted x y), x ≤ y
| (mk xl xr xL xR) (mk yl yr yL yR) (restricted.mk _ _ L_embedding R_embedding L_restriction R_restriction) :=
begin
  rw le_def,
  split,
  { intro i,
    left,
    use (L_embedding.to_fun i),
    dsimp,
    exact le_of_restricted (L_restriction i) },
  { intro j,
    right,
    use (R_embedding.to_fun j),
    dsimp,
    exact le_of_restricted (R_restriction j) },
end

/-- `relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
  Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
  for Right, and under these bijections we inductively have `relabelling`s for the consequent games. -/
inductive relabelling : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π (x y : pgame) (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ (i : x.left_moves), relabelling (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), relabelling (x.move_right (R.symm j)) (y.move_right j)) → relabelling x y

/-- If `x` is a relabelling of `y`, then Left and Right have the same moves in either game,
    so `x` is a restriction of `y`. -/
def restricted_of_relabelling : Π {x y : pgame} (r : relabelling x y), restricted x y
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk _ _ L_equiv R_equiv L_relabelling R_relabelling) :=
restricted.mk _ _ L_equiv.to_embedding R_equiv.symm.to_embedding
  (λ i, restricted_of_relabelling (L_relabelling i))
  (λ j, restricted_of_relabelling (R_relabelling j))

-- TODO prove `restricted x y → restricted y x → relabelling x y`

/-- The identity relabelling. -/
@[refl] def relabelling.refl : Π (x : pgame), relabelling x x
| (mk xl xr xL xR) :=
  relabelling.mk (mk xl xr xL xR) (mk xl xr xL xR) (equiv.refl _) (equiv.refl _)
    (λ i, relabelling.refl _) (λ j, relabelling.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

/-- Reverse a relabelling. -/
@[symm] def relabelling.symm : Π {x y : pgame}, relabelling x y → relabelling y x
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk _ _ L_equiv R_equiv L_relabelling R_relabelling) :=
begin
  refine relabelling.mk _ _ L_equiv.symm R_equiv.symm _ _,
  intro i,
  simpa using (L_relabelling (L_equiv.symm i)).symm,
  intro j,
  simpa using (R_relabelling (R_equiv j)).symm,
end

-- TODO trans for relabelling?

theorem le_of_relabelling {x y : pgame} (r : relabelling x y) : x ≤ y :=
le_of_restricted (restricted_of_relabelling r)

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv_of_relabelling {x y : pgame} (r : relabelling x y) : x ≈ y :=
⟨le_of_relabelling r, le_of_relabelling r.symm⟩

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : pgame → pgame
| ⟨l, r, L, R⟩ := ⟨r, l, λ i, neg (R i), λ i, neg (L i)⟩

instance : has_neg pgame := ⟨neg⟩

@[simp] lemma neg_def {xl xr xL xR} : -(mk xl xr xL xR) = mk xr xl (λ j, -(xR j)) (λ i, -(xL i)) := rfl

@[simp] theorem neg_neg : Π {x : pgame}, -(-x) = x
| (mk xl xr xL xR) :=
begin
  dsimp [has_neg.neg, neg],
  congr; funext i,
  { have t := @neg_neg (xL i),
    exact t },
  { have t := @neg_neg (xR i),
    exact t }
end

@[simp] theorem neg_zero : -(0 : pgame) = 0 :=
begin
  dsimp [has_zero.zero, has_neg.neg, neg],
  congr; funext i; cases i
end

/-- An explicit equivalence between the moves for Left in `-x` and the moves for Right in `x`. -/
-- This equivalence is useful to avoid having to use `cases` unnecessarily.
def left_moves_neg (x : pgame) : (-x).left_moves ≃ x.right_moves :=
begin
  induction x,
  refl,
end
/-- An explicit equivalence between the moves for Right in `-x` and the moves for Left in `x`. -/
def right_moves_neg (x : pgame) : (-x).right_moves ≃ x.left_moves :=
begin
  induction x,
  refl,
end

@[simp] lemma move_right_left_moves_neg {x : pgame} (i : left_moves (-x)) :
move_right x ((left_moves_neg x) i) = -(move_left (-x) i) :=
begin
  induction x,
  dsimp [left_moves_neg],
  rw neg_neg,
end
@[simp] lemma move_left_right_moves_neg_symm {x : pgame} (i : right_moves x) :
move_left (-x) ((left_moves_neg x).symm i) = -(move_right x i) :=
begin
  induction x,
  refl,
end
@[simp] lemma move_left_right_moves_neg {x : pgame} (i : right_moves (-x)) :
move_left x ((right_moves_neg x) i) = -(move_right (-x) i) :=
begin
  induction x,
  dsimp [right_moves_neg],
  rw neg_neg,
end
@[simp] lemma move_right_right_moves_neg_symm {x : pgame} (i : left_moves x) :
move_right (-x) ((right_moves_neg x).symm i) = -(move_left x i) :=
begin
  induction x,
  refl,
end

theorem le_iff_neg_ge : Π {x y : pgame}, x ≤ y ↔ -y ≤ -x
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  rw [le_def],
  rw [le_def],
  dsimp [neg],
  split,
  { intro h,
    split,
    { intro i, have t := h.right i, cases t,
      { right, cases t, use (@right_moves_neg (yR i)).symm t_w, convert le_iff_neg_ge.1 t_h, simp },
      { left, cases t, use t_w, exact le_iff_neg_ge.1 t_h, } },
    { intro j, have t := h.left j, cases t,
      { right, cases t, use t_w, exact le_iff_neg_ge.1 t_h, },
      { left, cases t, use (@left_moves_neg (xL j)).symm t_w, convert le_iff_neg_ge.1 t_h, simp, } } },
  { intro h,
    split,
    { intro i, have t := h.right i, cases t,
      { right, cases t, use (@left_moves_neg (xL i)) t_w, convert le_iff_neg_ge.2 _, convert t_h, simp, },
      { left, cases t, use t_w, exact le_iff_neg_ge.2 t_h, } },
    { intro j, have t := h.left j, cases t,
      { right, cases t, use t_w, exact le_iff_neg_ge.2 t_h, },
      { left, cases t, use (@right_moves_neg (yR j)) t_w, convert le_iff_neg_ge.2 _, convert t_h, simp } } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_congr {x y : pgame} (h : x ≈ y) : -x ≈ -y :=
⟨le_iff_neg_ge.1 h.2, le_iff_neg_ge.1 h.1⟩

section
local attribute [instance] classical.prop_decidable
theorem lt_iff_neg_gt : Π {x y : pgame}, x < y ↔ -y < -x :=
begin
  intros,
  rw [←not_le, ←not_le],
  apply not_iff_not.2,
  apply le_iff_neg_ge,
  apply_instance,
  apply_instance
end
end

theorem zero_le_iff_neg_le_zero {x : pgame} : 0 ≤ x ↔ -x ≤ 0 :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
end

theorem le_zero_iff_zero_le_neg {x : pgame} : x ≤ 0 ↔ 0 ≤ -x :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
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

/-- `x + 0` has exactly the same moves as `x`. -/
def add_zero_relabelling : Π (x : pgame.{u}), relabelling (x + 0) x
| (mk xl xr xL xR) :=
begin
  fsplit,
  exact equiv.sum_pempty xl,
  exact equiv.sum_pempty xr,
  { rintro (⟨i⟩|⟨⟨⟩⟩),
    change relabelling (xL i + 0) (xL i),
    apply add_zero_relabelling, },
  { rintro j,
    change relabelling (xR j + 0) (xR j),
    apply add_zero_relabelling, }
end

/-- `x + 0` is equivalent to `x`. -/
def add_zero_equiv (x : pgame.{u}) : x + 0 ≈ x :=
equiv_of_relabelling (add_zero_relabelling x)

/-- `0 + x` has exactly the same moves as `x`. -/
def zero_add_relabelling : Π (x : pgame.{u}), relabelling (0 + x) x
| (mk xl xr xL xR) :=
begin
  fsplit,
  exact equiv.pempty_sum xl,
  exact equiv.pempty_sum xr,
  { rintro (⟨⟨⟩⟩|⟨i⟩),
    change relabelling (0 + xL i) (xL i),
    apply zero_add_relabelling, },
  { rintro j,
    change relabelling (0 + xR j) (xR j),
    apply zero_add_relabelling, }
end

/-- `0 + x` is equivalent to `x`. -/
def zero_add_equiv (x : pgame.{u}) : 0 + x ≈ x :=
equiv_of_relabelling (zero_add_relabelling x)

/-- An explicit equivalence between the moves for Left in `x + y` and the type-theory sum
    of the moves for Left in `x` and in `y`. -/
def left_moves_add {x y : pgame} : (x + y).left_moves ≃ (x.left_moves ⊕ y.left_moves) :=
begin
  induction x generalizing y,
  induction y,
  refl,
end
/-- An explicit equivalence between the moves for Right in `x + y` and the type-theory sum
    of the moves for Right in `x` and in `y`. -/
def right_moves_add {x y : pgame} : (x + y).right_moves ≃ (x.right_moves ⊕ y.right_moves) :=
begin
  induction x generalizing y,
  induction y,
  refl,
end

@[simp] lemma left_moves_add_inv_fun_inl {x y : pgame} {i : x.left_moves} :
  left_moves_add.inv_fun (sum.inl i) = (@left_moves_add x y).symm (sum.inl i) := rfl
@[simp] lemma left_moves_add_inv_fun_inr {x y : pgame} {i : y.left_moves} :
  left_moves_add.inv_fun (sum.inr i) = (@left_moves_add x y).symm (sum.inr i) := rfl
@[simp] lemma right_moves_add_inv_fun_inl {x y : pgame} {i : x.right_moves} :
  right_moves_add.inv_fun (sum.inl i) = (@right_moves_add x y).symm (sum.inl i) := rfl
@[simp] lemma right_moves_add_inv_fun_inr {x y : pgame} {i : y.right_moves} :
  right_moves_add.inv_fun (sum.inr i) = (@right_moves_add x y).symm (sum.inr i) := rfl

@[simp] lemma mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inl i) = (mk xl xr xL xR).move_left i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_left_inl {x y : pgame} {i} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inl i)) = x.move_left i + y :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inl i) = (mk xl xr xL xR).move_right i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_right_inl {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inl i)) = x.move_right i + y :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inr i) = (mk xl xr xL xR) + (mk yl yr yL yR).move_left i :=
rfl
@[simp] lemma add_move_left_inr {x y : pgame} {i : y.left_moves} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inr i)) = x + y.move_left i :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inr i) = (mk xl xr xL xR) + (mk yl yr yL yR).move_right i :=
rfl
@[simp] lemma add_move_right_inr {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inr i)) = x + y.move_right i :=
begin
  cases x, cases y,
  refl,
end

instance : has_sub pgame := ⟨λ x y, x + -y⟩

/-- `-(x+y)` has exactly the same moves as `-x + -y`. -/
def neg_add_relabelling : Π (x y : pgame), relabelling (-(x + y)) (-x + -y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  fsplit,
  refl,
  refl,
  { intro j, dsimp, change xr ⊕ yr at j,
    cases j,
    dsimp,
    exact neg_add_relabelling (xR j) (mk yl yr yL yR),
    dsimp,
    exact neg_add_relabelling (mk xl xr xL xR) (yR j), },
  { intro i, dsimp, change xl ⊕ yl at i,
    cases i,
    dsimp,
    exact neg_add_relabelling (xL i) (mk yl yr yL yR),
    dsimp,
    exact neg_add_relabelling (mk xl xr xL xR) (yL i), },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_add_le {x y : pgame} : -(x + y) ≤ -x + -y :=
le_of_relabelling (neg_add_relabelling x y)

/-- `x+y` has exactly the same moves as `y+x`. -/
def add_comm_relabelling : Π (x y : pgame.{u}), relabelling (x + y) (y + x)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  fsplit,
  { transitivity,
    exact left_moves_add,
    transitivity,
    apply equiv.sum_comm,
    exact left_moves_add.symm, },
  { transitivity,
    exact right_moves_add,
    transitivity,
    apply equiv.sum_comm,
    exact right_moves_add.symm, },
  { intros,
    cases i; { dsimp [left_moves_add], apply add_comm_relabelling, } },
  { intros,
    simp only [equiv.symm_trans_apply, equiv.symm_symm_apply, equiv.sum_comm],
    cases j; { dsimp [right_moves_add], apply add_comm_relabelling, } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_comm_le {x y : pgame} : (x + y) ≤ (y + x) :=
le_of_relabelling (add_comm_relabelling x y)

theorem add_comm_equiv {x y : pgame} : (x + y) ≈ (y + x) :=
equiv_of_relabelling (add_comm_relabelling x y)

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def add_assoc_relabelling : Π (x y z : pgame.{u}), relabelling ((x + y) + z) (x + (y + z))
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  fsplit,
  { transitivity,
    exact left_moves_add,
    transitivity,
    apply equiv.sum_congr left_moves_add (equiv.refl _),
    apply equiv.sum_assoc, },
  { transitivity,
    exact right_moves_add,
    transitivity,
    apply equiv.sum_congr right_moves_add (equiv.refl _),
    apply equiv.sum_assoc, },
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

theorem add_assoc_equiv {x y z : pgame} : ((x + y) + z) ≈ (x + (y + z)) :=
equiv_of_relabelling (add_assoc_relabelling x y z)

theorem add_le_add_right : Π {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
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
        use left_moves_add.inv_fun (sum.inl i'),
        dsimp,
        simp only [move_left_mk, add_move_left_inl],
        exact add_le_add_right ih, },
      { right,
        use right_moves_add.inv_fun (sum.inl j),
        dsimp,
        simp only [add_move_right_inl],
        exact add_le_add_right jh },
      },
    { -- or play in z
      left,
      use left_moves_add.inv_fun (sum.inr i),
      dsimp,
      simp only [move_left_mk, add_move_left_inr],
      exact add_le_add_right h,
    }, },
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
        use left_moves_add.inv_fun (sum.inl i),
        dsimp,
        simp only [add_move_left_inl],
        exact add_le_add_right ih, },
      { right,
        use right_moves_add.inv_fun (sum.inl j'),
        dsimp,
        simp only [move_left_mk, add_move_left_inr],
        exact add_le_add_right jh },
      },
    { -- or play in z
      right,
      use right_moves_add.inv_fun (sum.inr j),
      dsimp,
      simp only [move_right_mk, add_move_right_inr],
      exact add_le_add_right h,
    }
  }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_le_add_left {x y z : pgame} (h : y ≤ z) : x + y ≤ x + z :=
calc x + y ≤ y + x : add_comm_le
     ... ≤ z + x : add_le_add_right h
     ... ≤ x + z : add_comm_le

theorem add_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : (w + y) ≈ (x + z) :=
⟨calc w + y ≤ w + z : add_le_add_left h₂.1
        ... ≤ x + z : add_le_add_right h₁.1,
 calc x + z ≤ x + y : add_le_add_left h₂.2
        ... ≤ w + y : add_le_add_right h₁.2⟩

theorem add_left_neg_le_zero : Π {x : pgame}, (-x) + x ≤ 0
| ⟨xl, xr, xL, xR⟩ :=
begin
  rw [le_def],
  split,
  { intro i,
    change xr ⊕ xl at i,
    cases i,
    { -- If Left played in -x, Right responds with the same move in x.
      right,
      fsplit,
      { dsimp,
        apply right_moves_add.inv_fun,
        right,
        use i },
      { dsimp,
        simp only [move_right_mk, add_move_right_inr],
        apply add_left_neg_le_zero, } },
    { -- If Left in x, Right responds with the same move in -x.
      right,
      fsplit,
      { dsimp,
        apply right_moves_add.inv_fun,
        left,
        use i },
      { dsimp,
        simp only [move_right_mk, add_move_right_inl],
        apply add_left_neg_le_zero, } },
  },
  { rintro ⟨⟩, }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem zero_le_add_left_neg : Π {x : pgame}, 0 ≤ (-x) + x
| ⟨xl, xr, xL, xR⟩ :=
begin
  rw [le_def],
  split,
  { rintro ⟨⟩, },
  { intro i,
    change xl ⊕ xr at i,
    cases i,
    { -- If Right played in -x, Left responds with the same move in x.
      left,
      fsplit,
      { dsimp,
        apply left_moves_add.inv_fun,
        right,
        use i },
      { dsimp,
        simp only [move_left_mk, add_move_left_inr],
        apply zero_le_add_left_neg, } },
    { -- If Right in x, Left responds with the same move in -x.
      left,
      fsplit,
      { dsimp,
        apply left_moves_add.inv_fun,
        left,
        use i },
      { dsimp,
        simp only [move_left_mk, add_move_left_inl],
        apply zero_le_add_left_neg, } },
  },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_left_neg_equiv {x : pgame} : (-x) + x ≈ 0 :=
⟨add_left_neg_le_zero, zero_le_add_left_neg⟩

theorem add_right_neg_le_zero {x : pgame} : x + (-x) ≤ 0 :=
calc x + (-x) ≤ (-x) + x : le_of_relabelling (add_comm_relabelling _ _)
     ... ≤ 0 : add_left_neg_le_zero

theorem zero_le_add_right_neg {x : pgame} : 0 ≤ x + (-x) :=
calc 0 ≤ (-x) + x : zero_le_add_left_neg
     ... ≤ x + (-x) : le_of_relabelling (add_comm_relabelling _ _)

theorem add_lt_add_right {x y z : pgame} (h : x < y) : x + z < y + z :=
begin
  rw ←not_le,
  rw ←not_le at h,
  intro w,
  replace w : (y + z) + (-z) ≤ (x + z) + (-z) := by apply add_le_add_right w,
  have h' : y ≤ x,
  calc y ≤ y + 0            : le_of_relabelling (add_zero_relabelling _).symm
       ... ≤ y + (z + -z)   : @add_le_add_left y 0 (z + -z) zero_le_add_right_neg
       ... ≤ (y + z) + (-z) : le_of_relabelling (add_assoc_relabelling _ _ _).symm
       ... ≤ (x + z) + (-z) : w
       ... ≤ x + (z + -z)   : le_of_relabelling (add_assoc_relabelling _ _ _)
       ... ≤ x + 0          : @add_le_add_left x (z + -z) 0 add_right_neg_le_zero
       ... ≤ x              : le_of_relabelling (add_zero_relabelling _),
  exact h h',
end

theorem add_lt_add_left {x y z : pgame} (h : y < z) : x + y < x + z :=
-- We can't argue via `x + y ≤ y + x < z + x ≤ x + z` since pgame does not form a preorder.
begin
  rw ←not_le,
  rw ←not_le at h,
  intro w,
  replace w : -x + (x + z) ≤ -x + (x + y) := by apply add_le_add_left w,
  have h' : z ≤ y,
  calc z ≤ 0 + z          : le_of_relabelling (zero_add_relabelling _).symm
       ... ≤ (-x + x) + z : @add_le_add_right 0 (-x + x) z zero_le_add_left_neg
       ... ≤ -x + (x + z) : le_of_relabelling (add_assoc_relabelling _ _ _)
       ... ≤ -x + (x + y) : w
       ... ≤ (-x + x) + y : le_of_relabelling (add_assoc_relabelling _ _ _).symm
       ... ≤ 0 + y        : @add_le_add_right (-x + x) 0 y add_left_neg_le_zero
       ... ≤ y            : le_of_relabelling (zero_add_relabelling _),
  exact h h',
end

/-- The pre-game `star`, which is fuzzy/confused with zero. -/
def star : pgame := pgame.of_lists [0] [0]

theorem star_lt_zero : star < 0 :=
begin
  rw lt_def,
  right,
  use 0,
  exact zero_lt_one,
  split;
  rintros ⟨⟩,
end
theorem zero_lt_star : 0 < star :=
begin
  rw lt_def,
  left,
  use 0,
  exact zero_lt_one,
  split;
  rintros ⟨⟩,
end

/-- The pre-game `ω`. (In fact all ordinals have game and surreal representatives.) -/
def omega : pgame := ⟨ulift ℕ, pempty, λ n, ↑n.1, pempty.elim⟩

end pgame

local infix ` ≈ ` := pgame.equiv

instance pgame.setoid : setoid pgame :=
⟨λ x y, x ≈ y,
 λ x, pgame.equiv_refl _,
 λ x y, pgame.equiv_symm,
 λ x y z, pgame.equiv_trans⟩

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
def game := quotient pgame.setoid

open pgame

namespace game

/-- The relation `x ≤ y` on games. -/
def le : game → game → Prop :=
quotient.lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy))

instance : has_le game :=
{ le := le }

@[refl] theorem le_refl : ∀ x : game, x ≤ x :=
by { rintro ⟨x⟩, apply pgame.le_refl }
@[trans] theorem le_trans : ∀ x y z : game, x ≤ y → y ≤ z → x ≤ z :=
by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, apply pgame.le_trans }
theorem le_antisymm : ∀ x y : game, x ≤ y → y ≤ x → x = y :=
by { rintro ⟨x⟩ ⟨y⟩ h₁ h₂, apply quot.sound, exact ⟨h₁, h₂⟩ }

/-- The relation `x < y` on games. -/
def lt : game → game → Prop :=
quotient.lift₂ (λ x y, x < y) (λ x₁ y₁ x₂ y₂ hx hy, propext (lt_congr hx hy))

theorem not_le : ∀ {x y : game}, ¬ (x ≤ y) ↔ (lt y x) :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_le }

instance : has_zero game := ⟨⟦0⟧⟩
instance : has_one game := ⟨⟦1⟧⟩


/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : game → game :=
quot.lift (λ x, ⟦-x⟧) (λ x y h, quot.sound (@neg_congr x y h))

instance : has_neg game :=
{ neg := neg, }

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add : game → game → game :=
quotient.lift₂ (λ x y : pgame, ⟦x + y⟧) (λ x₁ y₁ x₂ y₂ hx hy, quot.sound (pgame.add_congr hx hy))

instance : has_add game := ⟨add⟩

theorem add_assoc (x y z : game) : x + y + z = x + (y + z) :=
begin
  induction x generalizing y z,
  induction y generalizing z,
  induction z,
  apply quot.sound,
  exact add_assoc_equiv,
  refl,
  refl,
  refl
end

instance : add_semigroup game.{u} :=
{ add_assoc := add_assoc,
  ..game.has_add }

theorem add_zero (x : game) : x + 0 = x :=
begin
  induction x,
  apply quot.sound,
  apply add_zero_equiv,
  refl
end
theorem zero_add (x : game) : 0 + x = x :=
begin
  induction x,
  apply quot.sound,
  apply zero_add_equiv,
  refl
end

instance : add_monoid game :=
{ add_zero := add_zero,
  zero_add := zero_add,
  ..game.has_zero,
  ..game.add_semigroup }

theorem add_left_neg (x : game) : (-x) + x = 0 :=
begin
  induction x,
  apply quot.sound,
  apply add_left_neg_equiv,
  refl
end

instance : add_group game :=
{ add_left_neg := add_left_neg,
  ..game.has_neg,
  ..game.add_monoid }

theorem add_comm (x y : game) : x + y = y + x :=
begin
  induction x generalizing y,
  induction y,
  apply quot.sound,
  exact add_comm_equiv,
  refl,
  refl,
end

instance : add_comm_semigroup game :=
{ add_comm := add_comm,
  ..game.add_semigroup }

instance : add_comm_group game :=
{ ..game.add_comm_semigroup,
  ..game.add_group }

theorem add_le_add_left : ∀ (a b : game), a ≤ b → ∀ (c : game), c + a ≤ c + b :=
begin rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩, apply pgame.add_le_add_left h, end

-- While it is very tempting to define a `partial_order` on games, and prove
-- that games form an `ordered_comm_group`, it is a bit dangerous.

-- The relations `≤` and `<` on games do not satisfy
-- `lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`
-- (Consider `a = 0`, `b = star`.)
-- (`lt_iff_le_not_le` is satisfied by surreal numbers, however.)
-- Thus we can not use `<` when defining a `partial_order`.

-- Because of this issue, we define the `partial_order` and `ordered_comm_group` instances,
-- but do not actually mark them as instances, for safety.

def game_partial_order : partial_order game :=
{ le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,
  ..game.has_le }

local attribute [instance] game_partial_order

theorem add_lt_add_left (a b : game) (h : a < b) (c : game) : c + a < c + b :=
begin
  rw lt_iff_le_not_le at h,
  rw lt_iff_le_not_le,
  split,
  { apply add_le_add_left _ _ h.1 },
  { intro w,
    replace w : -c + (c + b) ≤ -c + (c + a) := add_le_add_left _ _ w _,
    simp only [add_zero, add_comm, add_left_neg, add_left_comm] at w,
    exact h.2 w },
end

def ordered_comm_group_game : ordered_comm_group game :=
{ add_le_add_left := add_le_add_left,
  add_lt_add_left := add_lt_add_left,
  ..game_partial_order,
  ..game.add_comm_group }

end game
