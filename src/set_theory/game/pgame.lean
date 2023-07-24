/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import data.fin.basic
import data.list.basic
import logic.relation
import order.game_add

/-!
# Combinatorial (pre-)games.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

Pregames have both a `≤` and a `<` relation, satisfying the usual properties of a `preorder`. The
relation `0 < x` means that `x` can always be won by Left, while `0 ≤ x` means that `x` can be won
by Left as the second player.

It turns out to be quite convenient to define various relations on top of these. We define the "less
or fuzzy" relation `x ⧏ y` as `¬ y ≤ x`, the equivalence relation `x ≈ y` as `x ≤ y ∧ y ≤ x`, and
the fuzzy relation `x ‖ y` as `x ⧏ y ∧ y ⧏ x`. If `0 ⧏ x`, then `x` can be won by Left as the
first player. If `x ≈ 0`, then `x` can be won by the second player. If `x ‖ 0`, then `x` can be won
by the first player.

Statements like `zero_le_lf`, `zero_lf_le`, etc. unfold these definitions. The theorems `le_def` and
`lf_def` give a recursive characterisation of each relation in terms of themselves two moves later.
The theorems `zero_le`, `zero_lf`, etc. also take into account that `0` has no moves.

Later, games will be defined as the quotient by the `≈` relation; that is to say, the
`antisymmetrization` of `pgame`.

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

/-! ### Pre-game moves -/

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

@[trans] theorem subsequent.trans {x y z} : subsequent x y → subsequent y z → subsequent x z :=
trans_gen.trans

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

/-! ### Basic pre-games -/

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

/-! ### Pre-game order relations -/

/-- The less or equal relation on pre-games.

If `0 ≤ x`, then Left can win `x` as the second player. -/
instance : has_le pgame :=
⟨sym2.game_add.fix wf_is_option $ λ x y le,
  (∀ i, ¬ le y (x.move_left i) (sym2.game_add.snd_fst $ is_option.move_left i)) ∧
  (∀ j, ¬ le (y.move_right j) x (sym2.game_add.fst_snd $ is_option.move_right j))⟩

/-- The less or fuzzy relation on pre-games.

If `0 ⧏ x`, then Left can win `x` as the first player. -/
def lf (x y : pgame) : Prop := ¬ y ≤ x

localized "infix (name := pgame.lf) ` ⧏ `:50 := pgame.lf" in pgame

@[simp] protected theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y ⧏ x := iff.rfl
@[simp] theorem not_lf {x y : pgame} : ¬ x ⧏ y ↔ y ≤ x := not_not
theorem _root_.has_le.le.not_gf {x y : pgame} : x ≤ y → ¬ y ⧏ x := not_lf.2
theorem lf.not_ge {x y : pgame} : x ⧏ y → ¬ y ≤ x := id

/-- Definition of `x ≤ y` on pre-games, in terms of `⧏`.

The ordering here is chosen so that `and.left` refer to moves by Left, and `and.right` refer to
moves by Right. -/

theorem le_iff_forall_lf {x y : pgame} :
  x ≤ y ↔ (∀ i, x.move_left i ⧏ y) ∧ ∀ j, x ⧏ y.move_right j :=
by { unfold has_le.le, rw sym2.game_add.fix_eq, refl }

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  mk xl xr xL xR ≤ mk yl yr yL yR ↔
  (∀ i, xL i ⧏ mk yl yr yL yR) ∧ ∀ j, mk xl xr xL xR ⧏ yR j :=
le_iff_forall_lf

theorem le_of_forall_lf {x y : pgame} (h₁ : ∀ i, x.move_left i ⧏ y) (h₂ : ∀ j, x ⧏ y.move_right j) :
  x ≤ y :=
le_iff_forall_lf.2 ⟨h₁, h₂⟩

/-- Definition of `x ⧏ y` on pre-games, in terms of `≤`.

The ordering here is chosen so that `or.inl` refer to moves by Left, and `or.inr` refer to
moves by Right. -/
theorem lf_iff_exists_le {x y : pgame} :
  x ⧏ y ↔ (∃ i, x ≤ y.move_left i) ∨ ∃ j, x.move_right j ≤ y :=
by { rw [lf, le_iff_forall_lf, not_and_distrib], simp }

/-- Definition of `x ⧏ y` on pre-games built using the constructor. -/
@[simp] theorem mk_lf_mk {xl xr xL xR yl yr yL yR} :
  mk xl xr xL xR ⧏ mk yl yr yL yR ↔
  (∃ i, mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ mk yl yr yL yR :=
lf_iff_exists_le

theorem le_or_gf (x y : pgame) : x ≤ y ∨ y ⧏ x :=
by { rw ←pgame.not_le, apply em }

theorem move_left_lf_of_le {x y : pgame} (h : x ≤ y) (i) : x.move_left i ⧏ y :=
(le_iff_forall_lf.1 h).1 i

alias move_left_lf_of_le ← _root_.has_le.le.move_left_lf

theorem lf_move_right_of_le {x y : pgame} (h : x ≤ y) (j) : x ⧏ y.move_right j :=
(le_iff_forall_lf.1 h).2 j

alias lf_move_right_of_le ← _root_.has_le.le.lf_move_right

theorem lf_of_move_right_le {x y : pgame} {j} (h : x.move_right j ≤ y) : x ⧏ y :=
lf_iff_exists_le.2 $ or.inr ⟨j, h⟩

theorem lf_of_le_move_left {x y : pgame} {i} (h : x ≤ y.move_left i) : x ⧏ y :=
lf_iff_exists_le.2 $ or.inl ⟨i, h⟩

theorem lf_of_le_mk {xl xr xL xR y} : mk xl xr xL xR ≤ y → ∀ i, xL i ⧏ y :=
move_left_lf_of_le

theorem lf_of_mk_le {x yl yr yL yR} : x ≤ mk yl yr yL yR → ∀ j, x ⧏ yR j :=
lf_move_right_of_le

theorem mk_lf_of_le {xl xr y j} (xL) {xR : xr → pgame} : xR j ≤ y → mk xl xr xL xR ⧏ y :=
@lf_of_move_right_le (mk _ _ _ _) y j

theorem lf_mk_of_le {x yl yr} {yL : yl → pgame} (yR) {i} : x ≤ yL i → x ⧏ mk yl yr yL yR :=
@lf_of_le_move_left x (mk _ _ _ _) i

/- We prove that `x ≤ y → y ≤ z ← x ≤ z` inductively, by also simultaneously proving its cyclic
reorderings. This auxiliary lemma is used during said induction. -/
private theorem le_trans_aux {x y z : pgame}
  (h₁ : ∀ {i}, y ≤ z → z ≤ x.move_left i → y ≤ x.move_left i)
  (h₂ : ∀ {j}, z.move_right j ≤ x → x ≤ y → z.move_right j ≤ y)
  (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z :=
le_of_forall_lf
  (λ i, pgame.not_le.1 $ λ h, (h₁ hyz h).not_gf $ hxy.move_left_lf i)
  (λ j, pgame.not_le.1 $ λ h, (h₂ h hxy).not_gf $ hyz.lf_move_right j)

instance : preorder pgame :=
{ le_refl := λ x, begin
    induction x with _ _ _ _ IHl IHr,
    exact le_of_forall_lf (λ i, lf_of_le_move_left (IHl i)) (λ i, lf_of_move_right_le (IHr i))
  end,
  le_trans := begin
    suffices : ∀ {x y z : pgame},
      (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y),
      from λ x y z, this.1,
    intros x y z,
    induction x with xl xr xL xR IHxl IHxr generalizing y z,
    induction y with yl yr yL yR IHyl IHyr generalizing z,
    induction z with zl zr zL zR IHzl IHzr,
    exact ⟨le_trans_aux (λ i, (IHxl i).2.1) (λ j, (IHzr j).2.2),
      le_trans_aux (λ i, (IHyl i).2.2) (λ j, (IHxr j).1),
      le_trans_aux (λ i, (IHzl i).1) (λ j, (IHyr j).2.1)⟩
  end,
  lt := λ x y, x ≤ y ∧ x ⧏ y,
  ..pgame.has_le, }

theorem lt_iff_le_and_lf {x y : pgame} : x < y ↔ x ≤ y ∧ x ⧏ y := iff.rfl
theorem lt_of_le_of_lf {x y : pgame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y := ⟨h₁, h₂⟩

theorem lf_of_lt {x y : pgame} (h : x < y) : x ⧏ y := h.2
alias lf_of_lt ← _root_.has_lt.lt.lf

theorem lf_irrefl (x : pgame) : ¬ x ⧏ x := le_rfl.not_gf
instance : is_irrefl _ (⧏) := ⟨lf_irrefl⟩

@[trans] theorem lf_of_le_of_lf {x y z : pgame} (h₁ : x ≤ y) (h₂ : y ⧏ z) : x ⧏ z :=
by { rw ←pgame.not_le at h₂ ⊢, exact λ h₃, h₂ (h₃.trans h₁) }
@[trans] theorem lf_of_lf_of_le {x y z : pgame} (h₁ : x ⧏ y) (h₂ : y ≤ z) : x ⧏ z :=
by { rw ←pgame.not_le at h₁ ⊢, exact λ h₃, h₁ (h₂.trans h₃) }

alias lf_of_le_of_lf ← _root_.has_le.le.trans_lf
alias lf_of_lf_of_le ← lf.trans_le

@[trans] theorem lf_of_lt_of_lf {x y z : pgame} (h₁ : x < y) (h₂ : y ⧏ z) : x ⧏ z :=
h₁.le.trans_lf h₂

@[trans] theorem lf_of_lf_of_lt {x y z : pgame} (h₁ : x ⧏ y) (h₂ : y < z) : x ⧏ z :=
h₁.trans_le h₂.le

alias lf_of_lt_of_lf ← _root_.has_lt.lt.trans_lf
alias lf_of_lf_of_lt ← lf.trans_lt

theorem move_left_lf {x : pgame} : ∀ i, x.move_left i ⧏ x :=
le_rfl.move_left_lf

theorem lf_move_right {x : pgame} : ∀ j, x ⧏ x.move_right j :=
le_rfl.lf_move_right

theorem lf_mk {xl xr} (xL : xl → pgame) (xR : xr → pgame) (i) : xL i ⧏ mk xl xr xL xR :=
@move_left_lf (mk _ _ _ _) i

theorem mk_lf {xl xr} (xL : xl → pgame) (xR : xr → pgame) (j) : mk xl xr xL xR ⧏ xR j :=
@lf_move_right (mk _ _ _ _) j

/-- This special case of `pgame.le_of_forall_lf` is useful when dealing with surreals, where `<` is
preferred over `⧏`. -/
theorem le_of_forall_lt {x y : pgame} (h₁ : ∀ i, x.move_left i < y) (h₂ : ∀ j, x < y.move_right j) :
  x ≤ y :=
le_of_forall_lf (λ i, (h₁ i).lf) (λ i, (h₂ i).lf)

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x y : pgame} : x ≤ y ↔
  (∀ i, (∃ i', x.move_left i ≤ y.move_left i')  ∨ ∃ j, (x.move_left i).move_right j ≤ y) ∧
   ∀ j, (∃ i, x ≤ (y.move_right j).move_left i) ∨ ∃ j', x.move_right j' ≤ y.move_right j :=
by { rw le_iff_forall_lf, conv { to_lhs, simp only [lf_iff_exists_le] } }

/-- The definition of `x ⧏ y` on pre-games, in terms of `⧏` two moves later. -/
theorem lf_def {x y : pgame} : x ⧏ y ↔
  (∃ i, (∀ i', x.move_left i' ⧏ y.move_left i)  ∧ ∀ j, x ⧏ (y.move_left i).move_right j) ∨
   ∃ j, (∀ i, (x.move_right j).move_left i ⧏ y) ∧ ∀ j', x.move_right j ⧏ y.move_right j' :=
by { rw lf_iff_exists_le, conv { to_lhs, simp only [le_iff_forall_lf] } }

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ⧏`. -/
theorem zero_le_lf {x : pgame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.move_right j :=
by { rw le_iff_forall_lf, simp }

/-- The definition of `x ≤ 0` on pre-games, in terms of `⧏ 0`. -/
theorem le_zero_lf {x : pgame} : x ≤ 0 ↔ ∀ i, x.move_left i ⧏ 0 :=
by { rw le_iff_forall_lf, simp }

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ≤`. -/
theorem zero_lf_le {x : pgame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.move_left i :=
by { rw lf_iff_exists_le, simp }

/-- The definition of `x ⧏ 0` on pre-games, in terms of `≤ 0`. -/
theorem lf_zero_le {x : pgame} : x ⧏ 0 ↔ ∃ j, x.move_right j ≤ 0 :=
by { rw lf_iff_exists_le, simp }

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : pgame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.move_right j).move_left i :=
by { rw le_def, simp }

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : pgame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.move_left i).move_right j ≤ 0 :=
by { rw le_def, simp }

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ⧏` two moves later. -/
theorem zero_lf {x : pgame} : 0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.move_left i).move_right j :=
by { rw lf_def, simp }

/-- The definition of `x ⧏ 0` on pre-games, in terms of `⧏ 0` two moves later. -/
theorem lf_zero {x : pgame} : x ⧏ 0 ↔ ∃ j, ∀ i, (x.move_right j).move_left i ⧏ 0 :=
by { rw lf_def, simp }

@[simp] theorem zero_le_of_is_empty_right_moves (x : pgame) [is_empty x.right_moves] : 0 ≤ x :=
zero_le.2 is_empty_elim

@[simp] theorem le_zero_of_is_empty_left_moves (x : pgame) [is_empty x.left_moves] : x ≤ 0 :=
le_zero.2 is_empty_elim

/-- Given a game won by the right player when they play second, provide a response to any move by
left. -/
noncomputable def right_response {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).right_moves :=
classical.some $ (le_zero.1 h) i

/-- Show that the response for right provided by `right_response` preserves the right-player-wins
condition. -/
lemma right_response_spec {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).move_right (right_response h i) ≤ 0 :=
classical.some_spec $ (le_zero.1 h) i

/-- Given a game won by the left player when they play second, provide a response to any move by
right. -/
noncomputable def left_response {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  (x.move_right j).left_moves :=
classical.some $ (zero_le.1 h) j

/-- Show that the response for left provided by `left_response` preserves the left-player-wins
condition. -/
lemma left_response_spec {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  0 ≤ (x.move_right j).move_left (left_response h j) :=
classical.some_spec $ (zero_le.1 h) j

/-- The equivalence relation on pre-games. Two pre-games `x`, `y` are equivalent if `x ≤ y` and
`y ≤ x`.

If `x ≈ 0`, then the second player can always win `x`. -/
def equiv (x y : pgame) : Prop := x ≤ y ∧ y ≤ x

localized "infix (name := pgame.equiv) ` ≈ ` := pgame.equiv" in pgame

instance : is_equiv _ (≈) :=
{ refl := λ x, ⟨le_rfl, le_rfl⟩,
  trans := λ x y z ⟨xy, yx⟩ ⟨yz, zy⟩, ⟨xy.trans yz, zy.trans yx⟩,
  symm := λ x y, and.symm }

theorem equiv.le {x y : pgame} (h : x ≈ y) : x ≤ y := h.1
theorem equiv.ge {x y : pgame} (h : x ≈ y) : y ≤ x := h.2

@[refl, simp] theorem equiv_rfl {x} : x ≈ x := refl x
theorem equiv_refl (x) : x ≈ x := refl x

@[symm] protected theorem equiv.symm {x y} : x ≈ y → y ≈ x := symm
@[trans] protected theorem equiv.trans {x y z} : x ≈ y → y ≈ z → x ≈ z := trans
protected theorem equiv_comm {x y} : x ≈ y ↔ y ≈ x := comm

theorem equiv_of_eq {x y} (h : x = y) : x ≈ y := by subst h

@[trans] theorem le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z := h₁.trans h₂.1
@[trans] theorem le_of_equiv_of_le {x y z} (h₁ : x ≈ y) : y ≤ z → x ≤ z := h₁.1.trans

theorem lf.not_equiv {x y} (h : x ⧏ y) : ¬ x ≈ y := λ h', h.not_ge h'.2
theorem lf.not_equiv' {x y} (h : x ⧏ y) : ¬ y ≈ x := λ h', h.not_ge h'.1

theorem lf.not_gt {x y} (h : x ⧏ y) : ¬ y < x := λ h', h.not_ge h'.le

theorem le_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) : x₂ ≤ y₂ :=
hx.2.trans (h.trans hy.1)
theorem le_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
⟨le_congr_imp hx hy, le_congr_imp hx.symm hy.symm⟩
theorem le_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
le_congr hx equiv_rfl
theorem le_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
le_congr equiv_rfl hy

theorem lf_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
pgame.not_le.symm.trans $ (not_congr (le_congr hy hx)).trans pgame.not_le
theorem lf_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
(lf_congr hx hy).1
theorem lf_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
lf_congr hx equiv_rfl
theorem lf_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
lf_congr equiv_rfl hy

@[trans] theorem lf_of_lf_of_equiv {x y z} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
lf_congr_imp equiv_rfl h₂ h₁
@[trans] theorem lf_of_equiv_of_lf {x y z} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
lf_congr_imp h₁.symm equiv_rfl

@[trans] theorem lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z := h₁.trans_le h₂.1
@[trans] theorem lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) : y < z → x < z := h₁.1.trans_lt

theorem lt_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) : x₂ < y₂ :=
hx.2.trans_lt (h.trans_le hy.1)
theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
⟨lt_congr_imp hx hy, lt_congr_imp hx.symm hy.symm⟩
theorem lt_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
lt_congr hx equiv_rfl
theorem lt_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
lt_congr equiv_rfl hy

theorem lt_or_equiv_of_le {x y : pgame} (h : x ≤ y) : x < y ∨ x ≈ y :=
and_or_distrib_left.mp ⟨h, (em $ y ≤ x).swap.imp_left pgame.not_le.1⟩

theorem lf_or_equiv_or_gf (x y : pgame) : x ⧏ y ∨ x ≈ y ∨ y ⧏ x :=
begin
  by_cases h : x ⧏ y,
  { exact or.inl h },
  { right,
    cases (lt_or_equiv_of_le (pgame.not_lf.1 h)) with h' h',
    { exact or.inr h'.lf },
    { exact or.inl h'.symm } }
end

theorem equiv_congr_left {y₁ y₂} : y₁ ≈ y₂ ↔ ∀ x₁, x₁ ≈ y₁ ↔ x₁ ≈ y₂ :=
⟨λ h x₁, ⟨λ h', h'.trans h, λ h', h'.trans h.symm⟩,
 λ h, (h y₁).1 $ equiv_rfl⟩

theorem equiv_congr_right {x₁ x₂} : x₁ ≈ x₂ ↔ ∀ y₁, x₁ ≈ y₁ ↔ x₂ ≈ y₁ :=
⟨λ h y₁, ⟨λ h', h.symm.trans h', λ h', h.trans h'⟩,
 λ h, (h x₂).2 $ equiv_rfl⟩

theorem equiv_of_mk_equiv {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ i, x.move_left i ≈ y.move_left (L i))
  (hr : ∀ j, x.move_right j ≈ y.move_right (R j)) : x ≈ y :=
begin
  fsplit; rw le_def,
  { exact ⟨λ i, or.inl ⟨_, (hl i).1⟩, λ j, or.inr ⟨_, by simpa using (hr (R.symm j)).1⟩⟩ },
  { exact ⟨λ i, or.inl ⟨_, by simpa using (hl (L.symm i)).2⟩, λ j, or.inr ⟨_, (hr j).2⟩⟩ }
end

/-- The fuzzy, confused, or incomparable relation on pre-games.

If `x ‖ 0`, then the first player can always win `x`. -/
def fuzzy (x y : pgame) : Prop := x ⧏ y ∧ y ⧏ x

localized "infix (name := pgame.fuzzy) ` ‖ `:50 := pgame.fuzzy" in pgame

@[symm] theorem fuzzy.swap {x y : pgame} : x ‖ y → y ‖ x := and.swap
instance : is_symm _ (‖) := ⟨λ x y, fuzzy.swap⟩
theorem fuzzy.swap_iff {x y : pgame} : x ‖ y ↔ y ‖ x := ⟨fuzzy.swap, fuzzy.swap⟩

theorem fuzzy_irrefl (x : pgame) : ¬ x ‖ x := λ h, lf_irrefl x h.1
instance : is_irrefl _ (‖) := ⟨fuzzy_irrefl⟩

theorem lf_iff_lt_or_fuzzy {x y : pgame} : x ⧏ y ↔ x < y ∨ x ‖ y :=
by { simp only [lt_iff_le_and_lf, fuzzy, ←pgame.not_le], tauto! }

theorem lf_of_fuzzy {x y : pgame} (h : x ‖ y) : x ⧏ y := lf_iff_lt_or_fuzzy.2 (or.inr h)
alias lf_of_fuzzy ← fuzzy.lf

theorem lt_or_fuzzy_of_lf {x y : pgame} : x ⧏ y → x < y ∨ x ‖ y :=
lf_iff_lt_or_fuzzy.1

theorem fuzzy.not_equiv {x y : pgame} (h : x ‖ y) : ¬ x ≈ y :=
λ h', h'.1.not_gf h.2
theorem fuzzy.not_equiv' {x y : pgame} (h : x ‖ y) : ¬ y ≈ x :=
λ h', h'.2.not_gf h.2

theorem not_fuzzy_of_le {x y : pgame} (h : x ≤ y) : ¬ x ‖ y :=
λ h', h'.2.not_ge h
theorem not_fuzzy_of_ge {x y : pgame} (h : y ≤ x) : ¬ x ‖ y :=
λ h', h'.1.not_ge h

theorem equiv.not_fuzzy {x y : pgame} (h : x ≈ y) : ¬ x ‖ y :=
not_fuzzy_of_le h.1
theorem equiv.not_fuzzy' {x y : pgame} (h : x ≈ y) : ¬ y ‖ x :=
not_fuzzy_of_le h.2

theorem fuzzy_congr {x₁ y₁ x₂ y₂ : pgame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ ↔ x₂ ‖ y₂ :=
show _ ∧ _ ↔ _ ∧ _, by rw [lf_congr hx hy, lf_congr hy hx]
theorem fuzzy_congr_imp {x₁ y₁ x₂ y₂ : pgame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ → x₂ ‖ y₂ :=
(fuzzy_congr hx hy).1
theorem fuzzy_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ‖ y ↔ x₂ ‖ y :=
fuzzy_congr hx equiv_rfl
theorem fuzzy_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ‖ y₁ ↔ x ‖ y₂ :=
fuzzy_congr equiv_rfl hy

@[trans] theorem fuzzy_of_fuzzy_of_equiv {x y z} (h₁ : x ‖ y) (h₂ : y ≈ z) : x ‖ z :=
(fuzzy_congr_right h₂).1 h₁
@[trans] theorem fuzzy_of_equiv_of_fuzzy {x y z} (h₁ : x ≈ y) (h₂ : y ‖ z) : x ‖ z :=
(fuzzy_congr_left h₁).2 h₂

/-- Exactly one of the following is true (although we don't prove this here). -/
theorem lt_or_equiv_or_gt_or_fuzzy (x y : pgame) : x < y ∨ x ≈ y ∨ y < x ∨ x ‖ y :=
begin
  cases le_or_gf x y with h₁ h₁;
  cases le_or_gf y x with h₂ h₂,
  { right, left, exact ⟨h₁, h₂⟩ },
  { left, exact ⟨h₁, h₂⟩ },
  { right, right, left, exact ⟨h₂, h₁⟩ },
  { right, right, right, exact ⟨h₂, h₁⟩ }
end

theorem lt_or_equiv_or_gf (x y : pgame) : x < y ∨ x ≈ y ∨ y ⧏ x :=
begin
  rw [lf_iff_lt_or_fuzzy, fuzzy.swap_iff],
  exact lt_or_equiv_or_gt_or_fuzzy x y
end

/-! ### Relabellings -/

/--
`relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `relabelling`s for the consequent games.
-/
inductive relabelling : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π {x y : pgame} (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ i, relabelling (x.move_left i) (y.move_left (L i))) →
         (∀ j, relabelling (x.move_right j) (y.move_right (R j))) →
       relabelling x y

localized "infix (name := pgame.relabelling) ` ≡r `:50 := pgame.relabelling" in pgame

namespace relabelling
variables {x y : pgame.{u}}

/-- A constructor for relabellings swapping the equivalences. -/
def mk' (L : y.left_moves ≃ x.left_moves) (R : y.right_moves ≃ x.right_moves)
  (hL : ∀ i, x.move_left (L i) ≡r y.move_left i)
  (hR : ∀ j, x.move_right (R j) ≡r y.move_right j) : x ≡r y :=
⟨L.symm, R.symm, λ i, by simpa using hL (L.symm i), λ j, by simpa using hR (R.symm j)⟩

/-- The equivalence between left moves of `x` and `y` given by the relabelling. -/
def left_moves_equiv : Π (r : x ≡r y), x.left_moves ≃ y.left_moves
| ⟨L, R, hL, hR⟩ := L

@[simp] theorem mk_left_moves_equiv {x y L R hL hR} :
  (@relabelling.mk x y L R hL hR).left_moves_equiv = L := rfl
@[simp] theorem mk'_left_moves_equiv {x y L R hL hR} :
  (@relabelling.mk' x y L R hL hR).left_moves_equiv = L.symm := rfl

/-- The equivalence between right moves of `x` and `y` given by the relabelling. -/
def right_moves_equiv : Π (r : x ≡r y), x.right_moves ≃ y.right_moves
| ⟨L, R, hL, hR⟩ := R

@[simp] theorem mk_right_moves_equiv {x y L R hL hR} :
  (@relabelling.mk x y L R hL hR).right_moves_equiv = R := rfl
@[simp] theorem mk'_right_moves_equiv {x y L R hL hR} :
  (@relabelling.mk' x y L R hL hR).right_moves_equiv = R.symm := rfl

/-- A left move of `x` is a relabelling of a left move of `y`. -/
def move_left : ∀ (r : x ≡r y) (i : x.left_moves),
  x.move_left i ≡r y.move_left (r.left_moves_equiv i)
| ⟨L, R, hL, hR⟩ := hL

/-- A left move of `y` is a relabelling of a left move of `x`. -/
def move_left_symm : ∀ (r : x ≡r y) (i : y.left_moves),
  x.move_left (r.left_moves_equiv.symm i) ≡r y.move_left i
| ⟨L, R, hL, hR⟩ i := by simpa using hL (L.symm i)

/-- A right move of `x` is a relabelling of a right move of `y`. -/
def move_right : ∀ (r : x ≡r y) (i : x.right_moves),
  x.move_right i ≡r y.move_right (r.right_moves_equiv i)
| ⟨L, R, hL, hR⟩ := hR

/-- A right move of `y` is a relabelling of a right move of `x`. -/
def move_right_symm : ∀ (r : x ≡r y) (i : y.right_moves),
  x.move_right (r.right_moves_equiv.symm i) ≡r y.move_right i
| ⟨L, R, hL, hR⟩ i := by simpa using hR (R.symm i)

/-- The identity relabelling. -/
@[refl] def refl : Π (x : pgame), x ≡r x
| x := ⟨equiv.refl _, equiv.refl _, λ i, refl _, λ j, refl _⟩
using_well_founded { dec_tac := pgame_wf_tac }

instance (x : pgame) : inhabited (x ≡r x) := ⟨refl _⟩

/-- Flip a relabelling. -/
@[symm] def symm : Π {x y : pgame}, x ≡r y → y ≡r x
| x y ⟨L, R, hL, hR⟩ := mk' L R (λ i, (hL i).symm) (λ j, (hR j).symm)

theorem le : ∀ {x y : pgame} (r : x ≡r y), x ≤ y
| x y r := le_def.2 ⟨λ i, or.inl ⟨_, (r.move_left i).le⟩, λ j, or.inr ⟨_, (r.move_right_symm j).le⟩⟩
using_well_founded { dec_tac := pgame_wf_tac }

theorem ge {x y : pgame} (r : x ≡r y) : y ≤ x := r.symm.le

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv (r : x ≡r y) : x ≈ y := ⟨r.le, r.ge⟩

/-- Transitivity of relabelling. -/
@[trans] def trans : Π {x y z : pgame}, x ≡r y → y ≡r z → x ≡r z
| x y z ⟨L₁, R₁, hL₁, hR₁⟩ ⟨L₂, R₂, hL₂, hR₂⟩ :=
⟨L₁.trans L₂, R₁.trans R₂, λ i, (hL₁ i).trans (hL₂ _), λ j, (hR₁ j).trans (hR₂ _)⟩

/-- Any game without left or right moves is a relabelling of 0. -/
def is_empty (x : pgame) [is_empty x.left_moves] [is_empty x.right_moves] : x ≡r 0 :=
⟨equiv.equiv_pempty _, equiv.equiv_of_is_empty _ _, is_empty_elim, is_empty_elim⟩

end relabelling

theorem equiv.is_empty (x : pgame) [is_empty x.left_moves] [is_empty x.right_moves] : x ≈ 0 :=
(relabelling.is_empty x).equiv

instance {x y : pgame} : has_coe (x ≡r y) (x ≈ y) := ⟨relabelling.equiv⟩

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : pgame} {xl' xr'} (el : xl' ≃ x.left_moves) (er : xr' ≃ x.right_moves) : pgame :=
⟨xl', xr', x.move_left ∘ el, x.move_right ∘ er⟩

@[simp] lemma relabel_move_left' {x : pgame} {xl' xr'}
  (el : xl' ≃ x.left_moves) (er : xr' ≃ x.right_moves) (i : xl') :
  move_left (relabel el er) i = x.move_left (el i) :=
rfl
@[simp] lemma relabel_move_left {x : pgame} {xl' xr'}
  (el : xl' ≃ x.left_moves) (er : xr' ≃ x.right_moves) (i : x.left_moves) :
  move_left (relabel el er) (el.symm i) = x.move_left i :=
by simp

@[simp] lemma relabel_move_right' {x : pgame} {xl' xr'}
  (el : xl' ≃ x.left_moves) (er : xr' ≃ x.right_moves) (j : xr') :
  move_right (relabel el er) j = x.move_right (er j) :=
rfl
@[simp] lemma relabel_move_right {x : pgame} {xl' xr'}
  (el : xl' ≃ x.left_moves) (er : xr' ≃ x.right_moves) (j : x.right_moves) :
  move_right (relabel el er) (er.symm j) = x.move_right j :=
by simp

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabel_relabelling {x : pgame} {xl' xr'} (el : xl' ≃ x.left_moves) (er : xr' ≃ x.right_moves) :
  x ≡r relabel el er :=
relabelling.mk' el er (λ i, by simp) (λ j, by simp)

/-! ### Negation -/

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

instance : neg_zero_class pgame :=
{ neg_zero :=
  begin
    dsimp [has_zero.zero, has_neg.neg, neg],
    congr; funext i; cases i
  end,
  ..pgame.has_zero,
  ..pgame.has_neg }

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

theorem is_option_neg {x y : pgame} : is_option x (-y) ↔ is_option (-x) y :=
begin
  rw [is_option_iff, is_option_iff, or_comm],
  cases y, apply or_congr;
  { apply exists_congr, intro, rw neg_eq_iff_eq_neg, refl },
end

@[simp] theorem is_option_neg_neg {x y : pgame} : is_option (-x) (-y) ↔ is_option x y :=
by rw [is_option_neg, neg_neg]

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
def relabelling.neg_congr : ∀ {x y : pgame}, x ≡r y → -x ≡r -y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨L, R, hL, hR⟩ :=
⟨R, L, λ j, (hR j).neg_congr, λ i, (hL i).neg_congr⟩

private theorem neg_le_lf_neg_iff :
  Π {x y : pgame.{u}}, (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  simp_rw [neg_def, mk_le_mk, mk_lf_mk, ← neg_def],
  split,
  { rw and_comm, apply and_congr; exact forall_congr (λ _, neg_le_lf_neg_iff.2) },
  { rw or_comm, apply or_congr; exact exists_congr (λ _, neg_le_lf_neg_iff.1) },
end
using_well_founded { dec_tac := pgame_wf_tac }

@[simp] theorem neg_le_neg_iff {x y : pgame} : -y ≤ -x ↔ x ≤ y := neg_le_lf_neg_iff.1

@[simp] theorem neg_lf_neg_iff {x y : pgame} : -y ⧏ -x ↔ x ⧏ y := neg_le_lf_neg_iff.2

@[simp] theorem neg_lt_neg_iff {x y : pgame} : -y < -x ↔ x < y :=
by rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]

@[simp] theorem neg_equiv_neg_iff {x y : pgame} : -x ≈ -y ↔ x ≈ y :=
by rw [equiv, equiv, neg_le_neg_iff, neg_le_neg_iff, and.comm]

@[simp] theorem neg_fuzzy_neg_iff {x y : pgame} : -x ‖ -y ↔ x ‖ y :=
by rw [fuzzy, fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, and.comm]

theorem neg_le_iff {x y : pgame} : -y ≤ x ↔ -x ≤ y :=
by rw [←neg_neg x, neg_le_neg_iff, neg_neg]

theorem neg_lf_iff {x y : pgame} : -y ⧏ x ↔ -x ⧏ y :=
by rw [←neg_neg x, neg_lf_neg_iff, neg_neg]

theorem neg_lt_iff {x y : pgame} : -y < x ↔ -x < y :=
by rw [←neg_neg x, neg_lt_neg_iff, neg_neg]

theorem neg_equiv_iff {x y : pgame} : -x ≈ y ↔ x ≈ -y :=
by rw [←neg_neg y, neg_equiv_neg_iff, neg_neg]

theorem neg_fuzzy_iff {x y : pgame} : -x ‖ y ↔ x ‖ -y :=
by rw [←neg_neg y, neg_fuzzy_neg_iff, neg_neg]

theorem le_neg_iff {x y : pgame} : y ≤ -x ↔ x ≤ -y :=
by rw [←neg_neg x, neg_le_neg_iff, neg_neg]

theorem lf_neg_iff {x y : pgame} : y ⧏ -x ↔ x ⧏ -y :=
by rw [←neg_neg x, neg_lf_neg_iff, neg_neg]

theorem lt_neg_iff {x y : pgame} : y < -x ↔ x < -y :=
by rw [←neg_neg x, neg_lt_neg_iff, neg_neg]

@[simp] theorem neg_le_zero_iff {x : pgame} : -x ≤ 0 ↔ 0 ≤ x :=
by rw [neg_le_iff, neg_zero]

@[simp] theorem zero_le_neg_iff {x : pgame} : 0 ≤ -x ↔ x ≤ 0 :=
by rw [le_neg_iff, neg_zero]

@[simp] theorem neg_lf_zero_iff {x : pgame} : -x ⧏ 0 ↔ 0 ⧏ x :=
by rw [neg_lf_iff, neg_zero]

@[simp] theorem zero_lf_neg_iff {x : pgame} : 0 ⧏ -x ↔ x ⧏ 0 :=
by rw [lf_neg_iff, neg_zero]

@[simp] theorem neg_lt_zero_iff {x : pgame} : -x < 0 ↔ 0 < x :=
by rw [neg_lt_iff, neg_zero]

@[simp] theorem zero_lt_neg_iff {x : pgame} : 0 < -x ↔ x < 0 :=
by rw [lt_neg_iff, neg_zero]

@[simp] theorem neg_equiv_zero_iff {x : pgame} : -x ≈ 0 ↔ x ≈ 0 :=
by rw [neg_equiv_iff, neg_zero]

@[simp] theorem neg_fuzzy_zero_iff {x : pgame} : -x ‖ 0 ↔ x ‖ 0 :=
by rw [neg_fuzzy_iff, neg_zero]

@[simp] theorem zero_equiv_neg_iff {x : pgame} : 0 ≈ -x ↔ 0 ≈ x :=
by rw [←neg_equiv_iff, neg_zero]

@[simp] theorem zero_fuzzy_neg_iff {x : pgame} : 0 ‖ -x ↔ 0 ‖ x :=
by rw [←neg_fuzzy_iff, neg_zero]

/-! ### Addition and subtraction -/

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : has_add pgame.{u} := ⟨λ x y, begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
  { exact λ i, IHxl i y },
  { exact IHyl },
  { exact λ i, IHxr i y },
  { exact IHyr }
end⟩

/-- The pre-game `((0+1)+⋯)+1`. -/
instance : has_nat_cast pgame := ⟨nat.unary_cast⟩

@[simp] protected theorem nat_succ (n : ℕ) : ((n + 1 : ℕ) : pgame) = n + 1 := rfl

instance is_empty_left_moves_add (x y : pgame.{u})
  [is_empty x.left_moves] [is_empty y.left_moves] : is_empty (x + y).left_moves :=
begin
  unfreezingI { cases x, cases y },
  apply is_empty_sum.2 ⟨_, _⟩,
  assumption'
end

instance is_empty_right_moves_add (x y : pgame.{u})
  [is_empty x.right_moves] [is_empty y.right_moves] : is_empty (x + y).right_moves :=
begin
  unfreezingI { cases x, cases y },
  apply is_empty_sum.2 ⟨_, _⟩,
  assumption'
end

/-- `x + 0` has exactly the same moves as `x`. -/
def add_zero_relabelling : Π (x : pgame.{u}), x + 0 ≡r x
| ⟨xl, xr, xL, xR⟩ :=
begin
  refine ⟨equiv.sum_empty xl pempty, equiv.sum_empty xr pempty, _, _⟩;
  rintro (⟨i⟩|⟨⟨⟩⟩);
  apply add_zero_relabelling
end

/-- `x + 0` is equivalent to `x`. -/
lemma add_zero_equiv (x : pgame.{u}) : x + 0 ≈ x :=
(add_zero_relabelling x).equiv

/-- `0 + x` has exactly the same moves as `x`. -/
def zero_add_relabelling : Π (x : pgame.{u}), 0 + x ≡r x
| ⟨xl, xr, xL, xR⟩ :=
begin
  refine ⟨equiv.empty_sum pempty xl, equiv.empty_sum pempty xr, _, _⟩;
  rintro (⟨⟨⟩⟩|⟨i⟩);
  apply zero_add_relabelling
end

/-- `0 + x` is equivalent to `x`. -/
lemma zero_add_equiv (x : pgame.{u}) : 0 + x ≈ x :=
(zero_add_relabelling x).equiv

theorem left_moves_add : ∀ (x y : pgame.{u}),
  (x + y).left_moves = (x.left_moves ⊕ y.left_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

theorem right_moves_add : ∀ (x y : pgame.{u}),
  (x + y).right_moves = (x.right_moves ⊕ y.right_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

/-- Converts a left move for `x` or `y` into a left move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def to_left_moves_add {x y : pgame} :
  x.left_moves ⊕ y.left_moves ≃ (x + y).left_moves :=
equiv.cast (left_moves_add x y).symm

/-- Converts a right move for `x` or `y` into a right move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def to_right_moves_add {x y : pgame} :
  x.right_moves ⊕ y.right_moves ≃ (x + y).right_moves :=
equiv.cast (right_moves_add x y).symm

@[simp] lemma mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inl i) =
    (mk xl xr xL xR).move_left i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_left_inl {x : pgame} (y : pgame) (i) :
  (x + y).move_left (to_left_moves_add (sum.inl i)) = x.move_left i + y :=
by { cases x, cases y, refl }

@[simp] lemma mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inl i) =
    (mk xl xr xL xR).move_right i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_right_inl {x : pgame} (y : pgame) (i) :
  (x + y).move_right (to_right_moves_add (sum.inl i)) = x.move_right i + y :=
by { cases x, cases y, refl }

@[simp] lemma mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_left i :=
rfl
@[simp] lemma add_move_left_inr (x : pgame) {y : pgame} (i) :
  (x + y).move_left (to_left_moves_add (sum.inr i)) = x + y.move_left i :=
by { cases x, cases y, refl }

@[simp] lemma mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_right i :=
rfl
@[simp] lemma add_move_right_inr (x : pgame) {y : pgame} (i) :
  (x + y).move_right (to_right_moves_add (sum.inr i)) = x + y.move_right i :=
by { cases x, cases y, refl }

lemma left_moves_add_cases {x y : pgame} (k) {P : (x + y).left_moves → Prop}
  (hl : ∀ i, P $ to_left_moves_add (sum.inl i))
  (hr : ∀ i, P $ to_left_moves_add (sum.inr i)) : P k :=
begin
  rw ←to_left_moves_add.apply_symm_apply k,
  cases to_left_moves_add.symm k with i i,
  { exact hl i },
  { exact hr i }
end

lemma right_moves_add_cases {x y : pgame} (k) {P : (x + y).right_moves → Prop}
  (hl : ∀ j, P $ to_right_moves_add (sum.inl j))
  (hr : ∀ j, P $ to_right_moves_add (sum.inr j)) : P k :=
begin
  rw ←to_right_moves_add.apply_symm_apply k,
  cases to_right_moves_add.symm k with i i,
  { exact hl i },
  { exact hr i }
end

instance is_empty_nat_right_moves : ∀ n : ℕ, is_empty (right_moves n)
| 0 := pempty.is_empty
| (n + 1) := begin
  haveI := is_empty_nat_right_moves n,
  rw [pgame.nat_succ, right_moves_add],
  apply_instance
end

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def relabelling.add_congr : ∀ {w x y z : pgame.{u}}, w ≡r x → y ≡r z → w + y ≡r x + z
| ⟨wl, wr, wL, wR⟩ ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨zl, zr, zL, zR⟩
  ⟨L₁, R₁, hL₁, hR₁⟩ ⟨L₂, R₂, hL₂, hR₂⟩ :=
begin
  let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩,
  let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩,
  refine ⟨equiv.sum_congr L₁ L₂, equiv.sum_congr R₁ R₂, _, _⟩;
  rintro (i|j),
  { exact (hL₁ i).add_congr Hyz },
  { exact Hwx.add_congr (hL₂ j) },
  { exact (hR₁ i).add_congr Hyz },
  { exact Hwx.add_congr (hR₂ j) }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance : has_sub pgame := ⟨λ x y, x + -y⟩

@[simp] theorem sub_zero (x : pgame) : x - 0 = x + 0 :=
show x + -0 = x + 0, by rw neg_zero

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def relabelling.sub_congr {w x y z : pgame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
h₁.add_congr h₂.neg_congr

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
def neg_add_relabelling : Π (x y : pgame), -(x + y) ≡r -x + -y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ :=
begin
  refine ⟨equiv.refl _, equiv.refl _, _, _⟩,
  all_goals {
    exact λ j, sum.cases_on j
      (λ j, neg_add_relabelling _ _)
      (λ j, neg_add_relabelling ⟨xl, xr, xL, xR⟩ _) }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_add_le {x y : pgame} : -(x + y) ≤ -x + -y :=
(neg_add_relabelling x y).le

/-- `x + y` has exactly the same moves as `y + x`. -/
def add_comm_relabelling : Π (x y : pgame.{u}), x + y ≡r y + x
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  refine ⟨equiv.sum_comm _ _, equiv.sum_comm _ _, _, _⟩;
  rintros (_|_);
  { dsimp [left_moves_add, right_moves_add], apply add_comm_relabelling }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_comm_le {x y : pgame} : x + y ≤ y + x :=
(add_comm_relabelling x y).le

theorem add_comm_equiv {x y : pgame} : x + y ≈ y + x :=
(add_comm_relabelling x y).equiv

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def add_assoc_relabelling : Π (x y z : pgame.{u}), x + y + z ≡r x + (y + z)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨zl, zr, zL, zR⟩ :=
begin
  refine ⟨equiv.sum_assoc _ _ _, equiv.sum_assoc _ _ _, _, _⟩,
  all_goals
  { rintro (⟨i|i⟩|i) <|> rintro (j|⟨j|j⟩),
    { apply add_assoc_relabelling },
    { apply add_assoc_relabelling ⟨xl, xr, xL, xR⟩ },
    { apply add_assoc_relabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ } }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_assoc_equiv {x y z : pgame} : (x + y) + z ≈ x + (y + z) :=
(add_assoc_relabelling x y z).equiv

theorem add_left_neg_le_zero : ∀ (x : pgame), -x + x ≤ 0
| ⟨xl, xr, xL, xR⟩ :=
le_zero.2 $ λ i, begin
  cases i,
  { -- If Left played in -x, Right responds with the same move in x.
    refine ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (sum.inr i), _⟩,
    convert @add_left_neg_le_zero (xR i),
    apply add_move_right_inr },
  { -- If Left in x, Right responds with the same move in -x.
    dsimp,
    refine ⟨@to_right_moves_add ⟨_, _, _, _⟩ _ (sum.inl i), _⟩,
    convert @add_left_neg_le_zero (xL i),
    apply add_move_right_inl }
end

theorem zero_le_add_left_neg (x : pgame) : 0 ≤ -x + x :=
begin
  rw [←neg_le_neg_iff, neg_zero],
  exact neg_add_le.trans (add_left_neg_le_zero _)
end

theorem add_left_neg_equiv (x : pgame) : -x + x ≈ 0 :=
⟨add_left_neg_le_zero x, zero_le_add_left_neg x⟩

theorem add_right_neg_le_zero (x : pgame) : x + -x ≤ 0 :=
add_comm_le.trans (add_left_neg_le_zero x)

theorem zero_le_add_right_neg (x : pgame) : 0 ≤ x + -x :=
(zero_le_add_left_neg x).trans add_comm_le

theorem add_right_neg_equiv (x : pgame) : x + -x ≈ 0 :=
⟨add_right_neg_le_zero x, zero_le_add_right_neg x⟩

theorem sub_self_equiv : ∀ x, x - x ≈ 0 :=
add_right_neg_equiv

private lemma add_le_add_right' : ∀ {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
λ h, begin
  refine le_def.2 ⟨λ i, _, λ i, _⟩;
  cases i,
  { rw le_def at h,
    cases h,
    rcases h_left i with ⟨i', ih⟩ | ⟨j, jh⟩,
    { exact or.inl ⟨to_left_moves_add (sum.inl i'), add_le_add_right' ih⟩ },
    { refine or.inr ⟨to_right_moves_add (sum.inl j), _⟩,
      convert add_le_add_right' jh,
      apply add_move_right_inl } },
  { exact or.inl ⟨@to_left_moves_add _ ⟨_, _, _, _⟩ (sum.inr i), add_le_add_right' h⟩ },
  { rw le_def at h,
    cases h,
    rcases h_right i with ⟨i, ih⟩ | ⟨j', jh⟩,
    { refine or.inl ⟨to_left_moves_add (sum.inl i), _⟩,
      convert add_le_add_right' ih,
      apply add_move_left_inl },
    { exact or.inr ⟨to_right_moves_add (sum.inl j'), add_le_add_right' jh⟩ } },
  { exact or.inr ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (sum.inr i), add_le_add_right' h⟩ }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance covariant_class_swap_add_le : covariant_class pgame pgame (swap (+)) (≤) :=
⟨λ x y z, add_le_add_right'⟩

instance covariant_class_add_le : covariant_class pgame pgame (+) (≤) :=
⟨λ x y z h, (add_comm_le.trans (add_le_add_right h x)).trans add_comm_le⟩

theorem add_lf_add_right {y z : pgame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
suffices z + x ≤ y + x → z ≤ y, by { rw ←pgame.not_le at ⊢ h, exact mt this h }, λ w,
  calc z ≤ z + 0        : (add_zero_relabelling _).symm.le
     ... ≤ z + (x + -x) : add_le_add_left (zero_le_add_right_neg x) _
     ... ≤ z + x + -x   : (add_assoc_relabelling _ _ _).symm.le
     ... ≤ y + x + -x   : add_le_add_right w _
     ... ≤ y + (x + -x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0        : add_le_add_left (add_right_neg_le_zero x) _
     ... ≤ y            : (add_zero_relabelling _).le

theorem add_lf_add_left {y z : pgame} (h : y ⧏ z) (x) : x + y ⧏ x + z :=
by { rw lf_congr add_comm_equiv add_comm_equiv, apply add_lf_add_right h }

instance covariant_class_swap_add_lt : covariant_class pgame pgame (swap (+)) (<) :=
⟨λ x y z h, ⟨add_le_add_right h.1 x, add_lf_add_right h.2 x⟩⟩

instance covariant_class_add_lt : covariant_class pgame pgame (+) (<) :=
⟨λ x y z h, ⟨add_le_add_left h.1 x, add_lf_add_left h.2 x⟩⟩

theorem add_lf_add_of_lf_of_le {w x y z : pgame} (hwx : w ⧏ x) (hyz : y ≤ z) : w + y ⧏ x + z :=
lf_of_lf_of_le (add_lf_add_right hwx y) (add_le_add_left hyz x)

theorem add_lf_add_of_le_of_lf {w x y z : pgame} (hwx : w ≤ x) (hyz : y ⧏ z) : w + y ⧏ x + z :=
lf_of_le_of_lf (add_le_add_right hwx y) (add_lf_add_left hyz x)

theorem add_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z),
  (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩

theorem add_congr_left {x y z : pgame} (h : x ≈ y) : x + z ≈ y + z :=
add_congr h equiv_rfl

theorem add_congr_right {x y z : pgame} : y ≈ z → x + y ≈ x + z :=
add_congr equiv_rfl

theorem sub_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
add_congr h₁ (neg_equiv_neg_iff.2 h₂)

theorem sub_congr_left {x y z : pgame} (h : x ≈ y) : x - z ≈ y - z :=
sub_congr h equiv_rfl

theorem sub_congr_right {x y z : pgame} : y ≈ z → x - y ≈ x - z :=
sub_congr equiv_rfl

theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x :=
⟨λ h, (zero_le_add_right_neg x).trans (add_le_add_right h _),
 λ h,
  calc x ≤ 0 + x : (zero_add_relabelling x).symm.le
     ... ≤ y - x + x : add_le_add_right h _
     ... ≤ y + (-x + x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero x) _
     ... ≤ y : (add_zero_relabelling y).le⟩

theorem lf_iff_sub_zero_lf {x y : pgame} : x ⧏ y ↔ 0 ⧏ y - x :=
⟨λ h, (zero_le_add_right_neg x).trans_lf (add_lf_add_right h _),
 λ h,
  calc x ≤ 0 + x : (zero_add_relabelling x).symm.le
     ... ⧏ y - x + x : add_lf_add_right h _
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

/-! ### Special pre-games -/

/-- The pre-game `star`, which is fuzzy with zero. -/
def star : pgame.{u} := ⟨punit, punit, λ _, 0, λ _, 0⟩

@[simp] theorem star_left_moves : star.left_moves = punit := rfl
@[simp] theorem star_right_moves : star.right_moves = punit := rfl

@[simp] theorem star_move_left (x) : star.move_left x = 0 := rfl
@[simp] theorem star_move_right (x) : star.move_right x = 0 := rfl

instance unique_star_left_moves : unique star.left_moves := punit.unique
instance unique_star_right_moves : unique star.right_moves := punit.unique

theorem star_fuzzy_zero : star ‖ 0 :=
⟨by { rw lf_zero, use default, rintros ⟨⟩ }, by { rw zero_lf, use default, rintros ⟨⟩ }⟩

@[simp] theorem neg_star : -star = star :=
by simp [star]

@[simp] protected theorem zero_lt_one : (0 : pgame) < 1 :=
lt_of_le_of_lf (zero_le_of_is_empty_right_moves 1) (zero_lf_le.2 ⟨default, le_rfl⟩)

instance : zero_le_one_class pgame := ⟨pgame.zero_lt_one.le⟩

@[simp] theorem zero_lf_one : (0 : pgame) ⧏ 1 :=
pgame.zero_lt_one.lf

end pgame
