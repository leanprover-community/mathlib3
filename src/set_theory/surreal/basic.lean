/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import set_theory.game.ordinal
import set_theory.game.basic
import logic.hydra

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a linearly ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties

Surreal numbers inherit the relations `≤` and `<` from games (`surreal.has_le` and
`surreal.has_lt`), and these relations satisfy the axioms of a linear order.

## Algebraic operations

We show that the surreals form a linear ordered commutative group.

One can also map all the ordinals into the surreals!

### Multiplication of surreal numbers

The proof that multiplication lifts to surreal numbers is surprisingly difficult and relies on an
intricate inductive argument, where three theorems `P1`, `P2` and `P4` with different numbers of
arguments (either 2 or 3) needs to be shown simultaneously. We define a single type
`pgame.thm8.args` that encompasses both types of arguments. The proof is carried out with
auxiliary definitions and lemmas under `namespace thm8`.

## References

* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
-/

universes u

local infix ` ≈ ` := pgame.equiv
local infix ` ⧏ `:50 := pgame.lf

namespace pgame

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def numeric : set pgame
| ⟨l, r, L, R⟩ :=
  (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ (∀ i, numeric (R i))

lemma numeric_def (x : pgame) : numeric x ↔ (∀ i j, x.move_left i < x.move_right j) ∧
  (∀ i, numeric (x.move_left i)) ∧ (∀ i, numeric (x.move_right i)) :=
by { cases x, refl }

lemma numeric.left_lt_right {x : pgame} (o : numeric x) (i : x.left_moves) (j : x.right_moves) :
  x.move_left i < x.move_right j := by { cases x, exact o.1 i j }
lemma numeric.move_left {x : pgame} (o : numeric x) (i : x.left_moves) :
  numeric (x.move_left i) := by { cases x, exact o.2.1 i }
lemma numeric.move_right {x : pgame} (o : numeric x) (j : x.right_moves) :
  numeric (x.move_right j) := by { cases x, exact o.2.2 j }
lemma numeric.is_option {x' x} (h : is_option x' x) (hx : numeric x) : numeric x' :=
by { cases h, apply hx.move_left, apply hx.move_right }

@[elab_as_eliminator]
theorem numeric_rec {C : pgame → Prop}
  (H : ∀ l r (L : l → pgame) (R : r → pgame),
    (∀ i j, L i < R j) → (∀ i, numeric (L i)) → (∀ i, numeric (R i)) →
    (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
  ∀ x, numeric x → C x
| ⟨l, r, L, R⟩ ⟨h, hl, hr⟩ :=
  H _ _ _ _ h hl hr (λ i, numeric_rec _ (hl i)) (λ i, numeric_rec _ (hr i))

theorem lf_asymm {x y : pgame} (ox : numeric x) (oy : numeric y) : x ⧏ y → ¬ y ⧏ x :=
begin
  refine numeric_rec (λ xl xr xL xR hx oxl oxr IHxl IHxr, _) x ox y oy,
  refine numeric_rec (λ yl yr yL yR hy oyl oyr IHyl IHyr, _),
  rw [mk_lf_mk, mk_lf_mk], rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩),
  { exact IHxl _ _ (oyl _) (move_left_lf_of_le _ h₁) (move_left_lf_of_le _ h₂) },
  { exact (le_trans h₂ h₁).not_lf (lf_of_lt (hy _ _)) },
  { exact (le_trans h₁ h₂).not_lf (lf_of_lt (hx _ _)) },
  { exact IHxr _ _ (oyr _) (lf_move_right_of_le _ h₁) (lf_move_right_of_le _ h₂) },
end

theorem le_of_lf {x y : pgame} (h : x ⧏ y) (ox : numeric x) (oy : numeric y) : x ≤ y :=
not_lf.1 (lf_asymm ox oy h)

alias le_of_lf ← pgame.lf.le

theorem lt_of_lf {x y : pgame} (h : x ⧏ y) (ox : numeric x) (oy : numeric y) : x < y :=
(lt_or_fuzzy_of_lf h).resolve_right (not_fuzzy_of_le (h.le ox oy))

alias lt_of_lf ← pgame.lf.lt

theorem lf_iff_lt {x y : pgame} (ox : numeric x) (oy : numeric y) : x ⧏ y ↔ x < y :=
⟨λ h, h.lt ox oy, lf_of_lt⟩

/-- Definition of `x ≤ y` on numeric pre-games, in terms of `<` -/
theorem le_iff_forall_lt {x y : pgame} (ox : x.numeric) (oy : y.numeric) :
  x ≤ y ↔ (∀ i, x.move_left i < y) ∧ ∀ j, x < y.move_right j :=
begin
  rw le_iff_forall_lf,
  refine and_congr _ _;
    refine forall_congr (λ i, (lf_iff_lt _ _));
    apply_rules [numeric.move_left, numeric.move_right]
end

/-- Definition of `x < y` on numeric pre-games, in terms of `≤` -/
theorem lt_iff_forall_le {x y : pgame} (ox : x.numeric) (oy : y.numeric) :
  x < y ↔ (∃ i, x ≤ y.move_left i) ∨ ∃ j, x.move_right j ≤ y :=
by rw [←lf_iff_lt ox oy, lf_iff_forall_le]

theorem lt_of_forall_le {x y : pgame} (ox : x.numeric) (oy : y.numeric) :
  ((∃ i, x ≤ y.move_left i) ∨ ∃ j, x.move_right j ≤ y) → x < y :=
(lt_iff_forall_le ox oy).2

/-- The definition of `x < y` on numeric pre-games, in terms of `<` two moves later. -/
theorem lt_def {x y : pgame} (ox : x.numeric) (oy : y.numeric) : x < y ↔
  (∃ i, (∀ i', x.move_left i' < y.move_left i)  ∧ ∀ j, x < (y.move_left i).move_right j) ∨
   ∃ j, (∀ i, (x.move_right j).move_left i < y) ∧ ∀ j', x.move_right j < y.move_right j' :=
begin
  rw [←lf_iff_lt ox oy, lf_def],
  refine or_congr _ _;
    refine exists_congr (λ x_1, _);
    refine and_congr _ _;
    refine (forall_congr $ λ i, lf_iff_lt _ _);
    apply_rules [numeric.move_left, numeric.move_right]
end

theorem not_fuzzy {x y : pgame} (ox : numeric x) (oy : numeric y) : ¬ fuzzy x y :=
λ h, not_lf.2 ((lf_of_fuzzy h).le ox oy) h.2

theorem lt_or_equiv_or_gt {x y : pgame} (ox : numeric x) (oy : numeric y) : x < y ∨ x ≈ y ∨ y < x :=
(lf_or_equiv_or_gf x y).imp (λ h, h.lt ox oy) $ or.imp_right $ λ h, h.lt oy ox

theorem numeric_of_is_empty (x : pgame) [is_empty x.left_moves] [is_empty x.right_moves] :
  numeric x :=
(numeric_def x).2 ⟨is_empty_elim, is_empty_elim, is_empty_elim⟩

theorem numeric_of_is_empty_left_moves (x : pgame) [is_empty x.left_moves]
  (H : ∀ j, numeric (x.move_right j)) : numeric x :=
(numeric_def x).2 ⟨is_empty_elim, is_empty_elim, H⟩

theorem numeric_of_is_empty_right_moves (x : pgame) [is_empty x.right_moves]
  (H : ∀ i, numeric (x.move_left i)) : numeric x :=
(numeric_def x).2 ⟨λ _, is_empty_elim, H, is_empty_elim⟩

theorem numeric_zero : numeric 0 := numeric_of_is_empty 0
theorem numeric_one : numeric 1 := numeric_of_is_empty_right_moves 1 $ λ _, numeric_zero

theorem numeric.neg : Π {x : pgame} (o : numeric x), numeric (-x)
| ⟨l, r, L, R⟩ o := ⟨λ j i, neg_lt_iff.2 (o.1 i j), λ j, (o.2.2 j).neg, λ i, (o.2.1 i).neg⟩

theorem numeric.move_left_lt {x : pgame} (o : numeric x) (i) : x.move_left i < x :=
(pgame.move_left_lf i).lt (o.move_left i) o
theorem numeric.move_left_le {x : pgame} (o : numeric x) (i) : x.move_left i ≤ x :=
(o.move_left_lt i).le

theorem numeric.lt_move_right {x : pgame} (o : numeric x) (j) : x < x.move_right j :=
(pgame.lf_move_right j).lt o (o.move_right j)
theorem numeric.le_move_right {x : pgame} (o : numeric x) (j) : x ≤ x.move_right j :=
(o.lt_move_right j).le

theorem numeric.add : Π {x y : pgame} (ox : numeric x) (oy : numeric y), numeric (x + y)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ox oy :=
⟨begin
   rintros (ix|iy) (jx|jy),
   { exact add_lt_add_right (ox.1 ix jx) _ },
   { exact (add_lf_add_of_lf_of_le (pgame.lf_mk _ _ ix) (oy.le_move_right jy)).lt
     ((ox.move_left ix).add oy) (ox.add (oy.move_right jy)) },
   { exact (add_lf_add_of_lf_of_le (pgame.mk_lf _ _ jx) (oy.move_left_le iy)).lt
      (ox.add (oy.move_left iy)) ((ox.move_right jx).add oy) },
   { exact add_lt_add_left (oy.1 iy jy) ⟨xl, xr, xL, xR⟩ }
 end,
 begin
   split,
   { rintros (ix|iy),
     { exact (ox.move_left ix).add oy },
     { exact ox.add (oy.move_left iy) } },
   { rintros (jx|jy),
     { apply (ox.move_right jx).add oy },
     { apply ox.add (oy.move_right jy) } }
 end⟩
using_well_founded { dec_tac := pgame_wf_tac }

lemma numeric.sub {x y : pgame} (ox : numeric x) (oy : numeric y) : numeric (x - y) := ox.add oy.neg

/-- Pre-games defined by natural numbers are numeric. -/
theorem numeric_nat : Π (n : ℕ), numeric n
| 0 := numeric_zero
| (n + 1) := (numeric_nat n).add numeric_one

/-- The pre-game `half` is numeric. -/
theorem numeric_half : numeric half :=
⟨λ _ _, zero_lt_one, λ _, numeric_zero, λ _, numeric_one⟩

/-- Ordinal games are numeric. -/
theorem numeric_to_pgame (o : ordinal) : o.to_pgame.numeric :=
begin
  induction o using ordinal.induction with o IH,
  apply numeric_of_is_empty_right_moves,
  simpa using λ i, IH _ (ordinal.to_left_moves_to_pgame_symm_lt i)
end

/-!
### Surreal multiplication

This section carries out the main inductive argument that proves the following three main theorems:
* P1: being numeric is closed under multiplication,
* P2: multiplying a numeric pregame by equivalent numeric pregames results in equivalent pregames,
* P3: the product of two positive numeric pregames is positive (`mul_pos`).

This is Theorem 8 in [conway2001], or Theorem 3.8 in [schleicher_stoll]. P1 allows us to define
multiplication as an operation on numeric pregames, P2 says that this is well-defined as an
operation on the quotient by `pgame.equiv`, namely the surreal numbers, and P3 is an axiom that
needs to be satisfied for the surreals to be a `ordered_ring`.

We follow the proof in [schleicher_stoll], except that we use the well-foundedness of
the hydra relation `cut_expand` on `multiset pgame` instead of the argument based
on a depth function in the paper.

In the argument, P3 is stated with four variables `x₁, x₂, y₁, y₂` satisfying `x₁ < x₂` and
`y₁ < y₂`, and says that `x₁ * y₂ + x₂ * x₁ < x₁ * y₁ + x₂ * y₂`, which is equivalent to
`0 < x₂ - x₁ → 0 < y₂ - y₁ → 0 < (x₂ - x₁) * (y₂ - y₁)`, i.e.
`@mul_pos pgame _ (x₂ - x₁) (y₂ - y₁)`. It has to be stated in this form and not in terms of
`mul_pos` because we needs show P1, P2 and (a specialized form of) P3 simultaneously, and for
example `P1 x y` will be deduced from P3 with variables taking values simpler than `x` or `y`
(among other induction hypotheses), but if you subtract two pregames simpler than `x` or `y`,
the result may no longer be simpler.

The specialized version of P3 is called P4, which takes only three arguments `x₁, x₂, y` and
requires that `y₂ = y` or `-y` and that `y₁` is a left option of `y₂`. After P1, P2 and P4 are
shown, a further inductive argument (this time using the `game_add` relation) proves P3 in full.

Our proof features a clear separation of
* calculation (e.g. ...),
* application of indution hypothesis,
* symmetry verification,
* verification of `cut_expand` relations,
* `numeric` hypotheses.
and we utilize symmetry (permutation and negation) to minimize calculation.

  strategy: extract specialized versions of the induction hypothesis that easier to apply
  (example: `ih1`, ...),
  show they are invariant under certain symmetries (permutation and negation of variables),
  and that the induction hypothesis indeed implies the restricted versions.
  (Actually the induction hypotheses themselves already have those symmetries ...)

  add the numeric hypothesis only at the last moment ..
  -/

/- specialization of induction hypothesis -/

namespace thm8

/-- The nontrivial part of P1 says that the left options of `x * y` are less than the right options,
  and this is the general form of these statements. -/
def P1 (x₁ x₂ x₃ y₁ y₂ y₃ : pgame) :=
⟦x₁ * y₁⟧ + ⟦x₂ * y₂⟧ - ⟦x₁ * y₂⟧ < ⟦x₃ * y₁⟧ + ⟦x₂ * y₃⟧ - ⟦x₃ * y₃⟧

/-- The proposition P2, without numeric assumptions. -/
def P2 (x₁ x₂ y : pgame) := x₁ ≈ x₂ → ⟦x₁ * y⟧ = ⟦x₂ * y⟧

/-- The proposition P3, without the `x₁ < x₂` and `y₁ < y₂` assumptions. -/
def P3 (x₁ x₂ y₁ y₂ : pgame) := ⟦x₁ * y₂⟧ + ⟦x₂ * y₁⟧ < ⟦x₁ * y₁⟧ + ⟦x₂ * y₂⟧

/-- The proposition P4, without numeric assumptions. In the references, the second part of the
  conjunction is stated as `∀ j, P3 x₁ x₂ y (y.move_right j)`, which is equivalent to our statement
  by `P3_comm` and `P3_neg`. We choose to state everything in terms of left options for uniform
  treatment. -/
def P4 (x₁ x₂ y : pgame) :=
x₁ < x₂ → (∀ i, P3 x₁ x₂ (y.move_left i) y) ∧ ∀ j, P3 x₁ x₂ ((-y).move_left j) (-y)

/-- The conjunction of P2 and P4. -/
def P24 (x₁ x₂ y : pgame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y

variables {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' : pgame.{u}}

/-! #### Symmetry properties of P1, P2, P3, and P4 -/

lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ :=
by { rw [P3, P3, add_comm], congr' 3; rw quot_mul_comm }

lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ :=
begin
  rw P3 at h₁ h₂, rw [P3, ← add_lt_add_iff_left (⟦x₂ * y₁⟧ + ⟦x₂ * y₂⟧)],
  convert add_lt_add h₁ h₂ using 1; abel,
end

lemma P3_neg : P3 x₁ x₂ y₁ y₂ ↔ P3 (-x₂) (-x₁) y₁ y₂ :=
by { simp only [P3, quot_neg_mul], rw ← neg_lt_neg_iff, convert iff.rfl; abel }

lemma P2_negx : P2 x₁ x₂ y ↔ P2 (-x₂) (-x₁) y :=
iff.imp (by rw [equiv_comm, neg_equiv_iff]) (by rw [quot_neg_mul, quot_neg_mul, eq_comm, neg_inj])

lemma P2_negy : P2 x₁ x₂ y ↔ P2 x₁ x₂ (-y) :=
iff.rfl.imp $ by rw [quot_mul_neg, quot_mul_neg, neg_inj]

lemma P4_negx : P4 x₁ x₂ y ↔ P4 (-x₂) (-x₁) y :=
iff.imp (by rw neg_lt_iff) $ and_congr (forall_congr $ λ _, P3_neg) (forall_congr $ λ _, P3_neg)

lemma P4_negy : P4 x₁ x₂ y ↔ P4 x₁ x₂ (-y) := iff.rfl.imp $ by rw [neg_neg, and_comm]

lemma P24_negx : P24 x₁ x₂ y ↔ P24 (-x₂) (-x₁) y := by rw [P24, P24, P2_negx, P4_negx]
lemma P24_negy : P24 x₁ x₂ y ↔ P24 x₁ x₂ (-y) := by rw [P24, P24, P2_negy, P4_negy]

/-! #### Explicit calculations necessary for the main proof -/

lemma mul_option_lt_iff_P1 {i j k l} :
  ⟦mul_option x y i k⟧ < -⟦mul_option x (-y) j l⟧ ↔
  P1 (x.move_left i) x (x.move_left j) y (y.move_left k) (-(-y).move_left l) :=
begin
  dsimp [mul_option, P1], convert iff.rfl using 2,
  simp only [neg_sub', neg_add, quot_mul_neg, neg_neg],
end

lemma mul_option_lt_mul_iff_P3 {i j} :
  ⟦mul_option x y i j⟧ < ⟦x * y⟧ ↔ P3 (x.move_left i) x (y.move_left j) y :=
by { dsimp [mul_option], exact sub_lt_iff_lt_add' }

lemma P1_of_eq (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃) (h3 : P3 x₁ x₂ y₂ y₃) :
  P1 x₁ x₂ x₃ y₁ y₂ y₃ :=
begin
  rw [P1, ← h₁ he, ← h₃ he, sub_lt_sub_iff],
  convert add_lt_add_left h3 ⟦x₁ * y₁⟧ using 1; abel,
end

lemma P1_of_lt (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₁ x₂ x₃ y₁ y₂ y₃ :=
begin
  rw [P1, sub_lt_sub_iff, ← add_lt_add_iff_left ⟦x₃ * y₂⟧],
  convert add_lt_add h₁ h₂ using 1; abel,
end

/-- The type of lists of arguments for P1, P2, and P4. -/
inductive args : Type (u+1)
| P1 (x y : pgame.{u}) : args
| P24 (x₁ x₂ y : pgame.{u}) : args

/-- The multiset associated to a list of arguments. -/
def args.to_multiset : args → multiset pgame
| (args.P1 x y) := {x, y}
| (args.P24 x₁ x₂ y) := {x₁, x₂, y}

/-- A list of arguments is numeric if all the arguments are. -/
def args.numeric (a : args) := ∀ x ∈ a.to_multiset, numeric x

open relation

/-- The relation specifying when a list of (pregame) arguments is considered simpler than another:
  `args_rel a₁ a₂` is true if `a₁`, considered as a multiset, can be obtained from `a₂` by
  repeatedly removing a pregame from `a₂` and adding back one or two options of the pregame.  -/
def args_rel := inv_image (trans_gen $ cut_expand is_option) args.to_multiset

/-- `args_rel` is well-founded. -/
theorem args_rel_wf : well_founded args_rel := inv_image.wf _ wf_is_option.cut_expand.trans_gen

/-- The statement that we will be shown by induction using the well-founded relation `args_rel`. -/
def P124 : args → Prop
| (args.P1 x y) := numeric (x * y)
| (args.P24 x₁ x₂ y) := P24 x₁ x₂ y

/-- The property that all arguments are numeric is leftward-closed under `arg_rel`. -/
lemma args_rel.numeric_closed {a' a} : args_rel a' a → a.numeric → a'.numeric :=
closed.trans_gen $ @cut_expand_closed _ is_option wf_is_option.is_irrefl.1 _ @numeric.is_option

/-- A specialized induction hypothesis used to prove P1. -/
def ih1 (x y) : Prop :=
∀ ⦃x₁ x₂ y'⦄, is_option x₁ x → is_option x₂ x → (y' = y ∨ is_option y' y) → P24 x₁ x₂ y'

/-! #### Symmetry properties of `ih1` -/

lemma ih1_negx : ih1 x y → ih1 (-x) y :=
λ h x₁ x₂ y' h₁ h₂ hy, by { rw is_option_neg at h₁ h₂, exact P24_negx.2 (h h₂ h₁ hy) }

lemma ih1_negy : ih1 x y → ih1 x (-y) :=
λ h x₁ x₂ y', by { rw [eq_neg_iff_eq_neg, eq_comm, is_option_neg, P24_negy], apply h }

/-! #### Specialize `ih` to obtain specialized induction hypotheses for P1 -/

variable (ih : ∀ a, args_rel a (args.P1 x y) → P124 a)
include ih

lemma ihnx (h : is_option x' x) : (x' * y).numeric :=
ih (args.P1 x' y) $ trans_gen.single $ cut_expand_pair_left h

lemma ihny (h : is_option y' y) : (x * y').numeric :=
ih (args.P1 x y') $ trans_gen.single $ cut_expand_pair_right h

lemma ihnxy (hx : is_option x' x) (hy : is_option y' y) : (x' * y').numeric :=
ih (args.P1 x' y') $ trans_gen.tail (trans_gen.single $ cut_expand_pair_right hy) $
  cut_expand_pair_left hx

lemma ih1xy : ih1 x y :=
begin
  rintro x₁ x₂ y' h₁ h₂ (rfl|hy); apply ih (args.P24 _ _ _),
  swap 2, refine trans_gen.tail _ (cut_expand_pair_right hy),
  all_goals { exact trans_gen.single (cut_expand_double_left h₁ h₂) },
end

lemma ih1yx : ih1 y x :=
ih1xy $ by { convert ih, simp_rw [args_rel, inv_image, args.to_multiset, multiset.pair_comm] }

omit ih

lemma P3_of_ih (hy : numeric y) (ihyx : ih1 y x) (i k l) :
  P3 (x.move_left i) x (y.move_left k) (-(-y).move_left l) :=
P3_comm.2 $ ((ihyx (is_option.move_left k) (is_option_neg.1 $ is_option.move_left l) (or.inl rfl)).2
  (by {rw ← move_right_neg_symm, apply hy.left_lt_right})).1 i

lemma P24_of_ih (ihxy : ih1 x y) (i j) : P24 (x.move_left i) (x.move_left j) y :=
ihxy (is_option.move_left i) (is_option.move_left j) (or.inl rfl)

variables (hx : numeric x) (hy : numeric y) (ihxy : ih1 x y) (ihyx : ih1 y x)
include hy ihxy ihyx

lemma mul_option_lt_of_lt (i j k l) (h : x.move_left i < x.move_left j) :
  ⟦mul_option x y i k⟧ < -⟦mul_option x (-y) j l⟧ :=
mul_option_lt_iff_P1.2 $ P1_of_lt (P3_of_ih hy ihyx j k l) $ ((P24_of_ih ihxy i j).2 h).1 k

include hx
lemma mul_option_lt (i j k l) : ⟦mul_option x y i k⟧ < -⟦mul_option x (-y) j l⟧ :=
begin
  obtain (h|h|h) := lt_or_equiv_or_gt (hx.move_left i) (hx.move_left j),
  { exact mul_option_lt_of_lt hy ihxy ihyx i j k l h },
  { have ml := @is_option.move_left,
    exact mul_option_lt_iff_P1.2 (P1_of_eq h (P24_of_ih ihxy i j).1
      (ihxy (ml i) (ml j) $ or.inr $ is_option_neg.1 $ ml l).1 $ P3_of_ih hy ihyx i k l) },
  { rw [mul_option_neg_neg, lt_neg],
    exact mul_option_lt_of_lt hy.neg (ih1_negy ihxy) (ih1_negx ihyx) j i l _ h },
end

omit ihxy ihyx
include ih

/-- P1 follows from the induction hypothesis. -/
theorem P1_of_ih : (x * y).numeric :=
begin
  obtain ⟨ihxy, ihyx⟩ := ⟨ih1xy ih, ih1yx ih⟩,
  obtain ⟨ihxyn, ihyxn⟩ := ⟨ih1_negx (ih1_negy ihxy), ih1_negx (ih1_negy ihyx)⟩,
  refine (numeric_def _).2 ⟨_, _, _⟩,
  { simp_rw lt_iff_game_lt, intro i, rw right_moves_mul_iff, split;
    intros j l; revert i; rw left_moves_mul_iff (gt _); split; intros i k,
    { apply mul_option_lt hx hy ihxy ihyx },
    { simp only [← mul_option_symm (-y)], rw mul_option_neg_neg x,
      apply mul_option_lt hy.neg hx.neg ihyxn ihxyn },
    { simp only [← mul_option_symm y], apply mul_option_lt hy hx ihyx ihxy },
    { rw mul_option_neg_neg y, apply mul_option_lt hx.neg hy.neg ihxyn ihyxn } },
  all_goals { cases x, cases y, rintro (⟨i,j⟩|⟨i,j⟩) },
  rw mk_mul_move_left_inl, swap 2, rw mk_mul_move_left_inr,
  swap 3, rw mk_mul_move_right_inl, swap 4, rw mk_mul_move_right_inr,
  all_goals { apply numeric.sub, apply numeric.add,
    apply ihnx ih, swap 2, apply ihny ih, swap 3, apply ihnxy ih },
  all_goals { apply is_option.mk_left <|> apply is_option.mk_right },
end

omit ih hx hy

/-- A specialized induction hypothesis used to prove P2 and P4. -/
def ih24 (x₁ x₂ y) : Prop :=
∀ ⦃z⦄, (is_option z x₁ → P24 z x₂ y) ∧ (is_option z x₂ → P24 x₁ z y) ∧ (is_option z y → P24 x₁ x₂ z)

/-- A specialized induction hypothesis used to prove P4. -/
def ih4 (x₁ x₂ y : pgame) : Prop :=
∀ ⦃z w⦄, is_option w y → (is_option z x₁ → P2 z x₂ w) ∧ (is_option z x₂ → P2 x₁ z w)

/-! #### Specialize `ih'` to obtain specialized induction hypotheses for P2 and P4 -/

variable (ih' : ∀ a, args_rel a (args.P24 x₁ x₂ y) → P124 a)
include ih'

lemma ih₁₂ : ih24 x₁ x₂ y :=
begin
  refine (λ z, ⟨_, _, _⟩);
  refine λ h, ih' (args.P24 _ _ _) (trans_gen.single _),
  exacts [(cut_expand_add_right {y}).2 (cut_expand_pair_left h),
    (cut_expand_add_left {x₁}).2 (cut_expand_pair_left h),
    (cut_expand_add_left {x₁}).2 (cut_expand_pair_right h)],
end

lemma ih₂₁ : ih24 x₂ x₁ y :=
ih₁₂ begin
  convert ih', simp_rw [args_rel, inv_image, args.to_multiset],
  dsimp [← multiset.singleton_add], abel,
end

lemma ih4_of_ih : ih4 x₁ x₂ y :=
begin
  refine (λ z w h, ⟨_, _⟩);
  refine λ h', (ih' (args.P24 _ _ _) (trans_gen.tail (trans_gen.single _) $
    (cut_expand_add_left {x₁}).2 $ cut_expand_pair_right h)).1,
  exacts [(cut_expand_add_right {w}).2 $ cut_expand_pair_left h',
    (cut_expand_add_right {w}).2 $ cut_expand_pair_right h'],
end

lemma numeric_of_ih : (x₁ * y).numeric ∧ (x₂ * y).numeric :=
begin
  split; refine ih' (args.P1 _ _) (trans_gen.single _),
  exacts [(cut_expand_add_right {y}).2 $ (cut_expand_add_left {x₁}).2 cut_expand_zero,
    (cut_expand_add_right {x₂, y}).2 cut_expand_zero],
end

omit ih'

/-- Symmetry properties of `ih24`. -/
lemma ih24_neg : ih24 x₁ x₂ y → ih24 (-x₂) (-x₁) y ∧ ih24 x₁ x₂ (-y) :=
begin
  simp_rw [ih24, ← P24_negy, is_option_neg],
  refine (λ h, ⟨λ z, ⟨_, _, _⟩, λ z, ⟨(@h z).1, (@h z).2.1, P24_negy.2 ∘ (@h $ -z).2.2⟩⟩);
  rw P24_negx; simp only [neg_neg], exacts [(@h $ -z).2.1, (@h $ -z).1, (@h z).2.2],
end

/-- Symmetry properties of `ih4`. -/
lemma ih4_neg : ih4 x₁ x₂ y → ih4 (-x₂) (-x₁) y ∧ ih4 x₁ x₂ (-y) :=
begin
  simp_rw [ih4, is_option_neg],
  refine (λ h, ⟨λ z w h', _, λ z w h', _⟩),
  { convert (h h').symm; rw [P2_negx, neg_neg] },
  { convert h h'; rw P2_negy },
end

lemma mul_option_lt_mul_of_equiv (hn : x₁.numeric) (h : ih24 x₁ x₂ y) (he : x₁ ≈ x₂) (i j) :
  ⟦mul_option x₁ y i j⟧ < ⟦x₂ * y⟧ :=
begin
  convert sub_lt_iff_lt_add'.2 ((((@h _).1 $ is_option.move_left i).2 _).1 j) using 1,
  { rw ← ((@h _).2.2 $ is_option.move_left j).1 he, refl },
  { rw ← lt_congr_right he, apply hn.move_left_lt },
end

/-- P2 follows from specialized induction hypotheses ("one half" of the equality). -/
theorem mul_right_le_of_equiv (h₁ : x₁.numeric) (h₂ : x₂.numeric)
  (h₁₂ : ih24 x₁ x₂ y) (h₂₁ : ih24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y :=
le_of_forall_lt begin
  have he' := neg_congr he, simp_rw lt_iff_game_lt,
  rw [left_moves_mul_iff (gt _), right_moves_mul_iff],
  refine ⟨⟨mul_option_lt_mul_of_equiv h₁ h₁₂ he, _⟩, _⟩,
  { rw ← quot_neg_mul_neg,
    exact mul_option_lt_mul_of_equiv h₁.neg (ih24_neg $ (ih24_neg h₂₁).1).2 he' },
  { split; intros; rw lt_neg,
    { rw ← quot_mul_neg, apply mul_option_lt_mul_of_equiv h₂ (ih24_neg h₂₁).2 he.symm },
    { rw ← quot_neg_mul, apply mul_option_lt_mul_of_equiv h₂.neg (ih24_neg h₁₂).1 he'.symm } },
end

/-- The statement that all left options of `x * y` of the first kind are less than itself. -/
def mul_options_lt_mul (x y) : Prop := ∀ ⦃i j⦄, ⟦mul_option x y i j⟧ < ⟦x * y⟧

/-- That the left options of `x * y` are less than itself and the right options are greater, which
  is part of the condition that `x * y` is numeric, is equivalent to the conjunction of various
  `mul_options_lt_mul` statements for `x, y` and their negations. We only show the forward
  direction. -/
lemma mul_options_lt_mul_of_numeric (hn : (x * y).numeric) :
  (mul_options_lt_mul x y ∧ mul_options_lt_mul (-x) (-y)) ∧
  (mul_options_lt_mul x (-y) ∧ mul_options_lt_mul (-x) y) :=
⟨by { have h := hn.move_left_lt, simp_rw lt_iff_game_lt at h,
      convert (left_moves_mul_iff (gt _)).1 h, rw ← quot_neg_mul_neg, refl },
 by { have h := hn.lt_move_right, simp_rw [lt_iff_game_lt, right_moves_mul_iff] at h,
      refine h.imp _ _; { refine forall₂_imp (λ a b, _),
      rw lt_neg, rw quot_mul_neg <|> rw quot_neg_mul, exact id } }⟩

/-- A condition just enough to deduce P3, which will always be used with `x'` being a left
  option of `x₂`. When `y₁` is a left option of `y₂`, it can be deduced from induction hypotheses
  `ih24 x₁ x₂ y₂`, `ih4 x₁ x₂ y₂`, and `(x₂ * y₂).numeric` for P124 (`P3_cond_of_ih`); when `y₁` is
  not necessarily an option of `y₂`, it follows from the induction hypothesis for P3 (with `x₂`
  replaced by a left option `x'`) after the `main` theorem (P124) is established, and is used to
  prove P3 in full (`P3_of_lt_of_lt`). -/
def ih3 (x₁ x' x₂ y₁ y₂) : Prop :=
P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

lemma ih3_of_ih (h24 : ih24 x₁ x₂ y) (h4 : ih4 x₁ x₂ y) (hl : mul_options_lt_mul x₂ y)
  (i j) : ih3 x₁ (x₂.move_left i) x₂ (y.move_left j) y :=
let ml := @is_option.move_left, h24 := (@h24 _).2.1 $ ml i in
⟨(h4 $ ml j).2 $ ml i, h24.1, mul_option_lt_mul_iff_P3.1 $ @hl i j, λ l, (h24.2 l).1 _⟩

lemma P3_of_le_left {y₁ y₂} (i) (h : ih3 x₁ (x₂.move_left i) x₂ y₁ y₂)
  (hl : x₁ ≤ x₂.move_left i) : P3 x₁ x₂ y₁ y₂ :=
begin
  obtain (hl|he) := lt_or_equiv_of_le hl,
  exacts [(h.2.2.2 hl).trans h.2.2.1, by { rw [P3, h.1 he, h.2.1 he], exact h.2.2.1 }],
end

/-- P3 follows from `ih3`, so P4 (with `y₁` a left option of `y₂`) follows from the induction
  hypothesis. -/
theorem P3_of_lt {y₁ y₂} (h : ∀ i, ih3 x₁ (x₂.move_left i) x₂ y₁ y₂)
  (hs : ∀ i, ih3 (-x₂) ((-x₁).move_left i) (-x₁) y₁ y₂) (hl : x₁ < x₂) : P3 x₁ x₂ y₁ y₂ :=
begin
  obtain (⟨i,hi⟩|⟨i,hi⟩) := lf_iff_forall_le.1 (lf_of_lt hl),
  exacts [P3_of_le_left i (h i) hi, P3_neg.2 $
    P3_of_le_left _ (hs _) $ by { rw move_left_neg, exact neg_le_neg (le_iff_game_le.1 hi) }],
end

/-- The main chunk of Theorem 8 in [conway2001] / Theorem 3.8 in [schleicher_stoll]. -/
theorem main (a : args) : a.numeric → P124 a :=
begin
  apply args_rel_wf.induction a, intros a ih ha,
  replace ih : ∀ a', args_rel a' a → P124 a' := λ a' hr, ih a' hr (hr.numeric_closed ha),
  cases a with x y x₁ x₂ y,
  { /- P1 -/ exact P1_of_ih ih (ha x $ or.inl rfl) (ha y $ or.inr $ or.inl rfl) },
  obtain ⟨h₁₂, h₂₁, h4⟩ := ⟨ih₁₂ ih, ih₂₁ ih, ih4_of_ih ih⟩,
  obtain ⟨⟨h₁₂x, h₁₂y⟩, h4x, h4y⟩ := ⟨ih24_neg h₁₂, ih4_neg h4⟩,
  refine ⟨λ he, quotient.sound _, λ hl, _⟩,
  { /- P2 -/ obtain ⟨h₁, h₂⟩ := ⟨ha x₁ $ or.inl rfl, ha x₂ $ or.inr $ or.inl rfl⟩,
    exact ⟨mul_right_le_of_equiv h₁ h₂ h₁₂ h₂₁ he, mul_right_le_of_equiv h₂ h₁ h₂₁ h₁₂ he.symm⟩ },
  /- P4 ↓ -/
  obtain ⟨hn₁, hn₂⟩ := numeric_of_ih ih,
  obtain ⟨⟨h₁, -⟩, h₂, -⟩ := mul_options_lt_mul_of_numeric hn₂,
  obtain ⟨⟨-, h₃⟩, -, h₄⟩ := mul_options_lt_mul_of_numeric hn₁,
  split; intro; refine P3_of_lt _ _ hl; intro; apply ih3_of_ih,
  exacts [h₁₂, h4, h₁, h₁₂x, h4x, h₄, h₁₂y, h4y, h₂, (ih24_neg h₁₂y).1, (ih4_neg h4y).1, h₃],
end

end thm8

namespace numeric
open thm8

variables {x x₁ x₂ y y₁ y₂ : pgame.{u}}
  (hx : x.numeric) (hx₁ : x₁.numeric) (hx₂ : x₂.numeric)
  (hy : y.numeric) (hy₁ : y₁.numeric) (hy₂ : y₂.numeric)

include hx hy
theorem mul : numeric (x * y) := main (args.P1 x y) $ by rintro _ (rfl|rfl|⟨⟨⟩⟩); assumption
omit hx

include hx₁ hx₂
theorem P24 : P24 x₁ x₂ y :=
main (args.P24 x₁ x₂ y) $ by rintro _ (rfl|rfl|rfl|⟨⟨⟩⟩); assumption
omit hx₁ hx₂ hy

theorem mul_congr_left (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
equiv_iff_game_eq.2 $ (P24 hx₁ hx₂ hy).1 he

theorem mul_congr_right (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ :=
(mul_comm_equiv _ _).trans $ (mul_congr_left hy₁ hy₂ hx he).trans $ mul_comm_equiv _ _

theorem mul_congr (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
(mul_congr_left hx₁ hx₂ hy₁ hx).trans (mul_congr_right hx₂ hy₁ hy₂ hy)

open relation.game_add

include hx₁ hx₂ hy₁ hy₂
/-- One additional inductive argument that supplies the last missing part of Theorem 8. -/
theorem P3_of_lt_of_lt (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ :=
begin
  revert x₁ x₂, rw ← prod.forall',
  refine λ t, (wf_is_option.game_add wf_is_option).induction t _,
  rintro ⟨x₁, x₂⟩ ih hx₁ hx₂ hx, refine P3_of_lt _ _ hx; intro i,
  { have hi := hx₂.move_left i,
    exact ⟨(P24 hx₁ hi hy₁).1, (P24 hx₁ hi hy₂).1,
      P3_comm.2 $ ((P24 hy₁ hy₂ hx₂).2 hy).1 _,
      ih _ (snd $ is_option.move_left i) hx₁ hi⟩ },
  { have hi := hx₁.neg.move_left i,
    exact ⟨(P24 hx₂.neg hi hy₁).1, (P24 hx₂.neg hi hy₂).1,
      P3_comm.2 $ ((P24 hy₁ hy₂ hx₁).2 hy).2 _,
      by { rw [move_left_neg', ← P3_neg, neg_lt_iff],
        exact ih _ (fst $ is_option.move_right _) (hx₁.move_right _) hx₂ }⟩ },
end
omit hy₁ hy₂

theorem mul_pos (hp₁ : 0 < x₁) (hp₂ : 0 < x₂) : 0 < x₁ * x₂ :=
begin
  rw lt_iff_game_lt,
  convert P3_of_lt_of_lt numeric_zero hx₁ numeric_zero hx₂ hp₁ hp₂ using 1; simpa,
end

end numeric

end pgame

/-- The equivalence on numeric pre-games. -/
def surreal.equiv (x y : pgame.numeric) : Prop := x.1.equiv y.1

open pgame

instance surreal.setoid : setoid numeric :=
⟨λ x y, x.1 ≈ y.1,
 λ x, equiv_rfl,
 λ x y, pgame.equiv.symm,
 λ x y z, pgame.equiv.trans⟩

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a linear order. -/
def surreal := quotient surreal.setoid

namespace surreal

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : pgame) (h : x.numeric) : surreal := ⟦⟨x, h⟩⟧

instance : has_zero surreal := ⟨mk 0 numeric_zero⟩
instance : has_one surreal := ⟨mk 1 numeric_one⟩

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, numeric x → α)
  (H : ∀ {x y} (hx : numeric x) (hy : numeric y), x.equiv y → f x hx = f y hy) : surreal → α :=
quotient.lift (λ x : numeric, f x.1 x.2) (λ x y, H x.2 y.2)

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, numeric x → numeric y → α)
  (H : ∀ {x₁ y₁ x₂ y₂} (ox₁ : numeric x₁) (oy₁ : numeric y₁) (ox₂ : numeric x₂) (oy₂ : numeric y₂),
    x₁.equiv x₂ → y₁.equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) : surreal → surreal → α :=
lift (λ x ox, lift (λ y oy, f x y ox oy) (λ y₁ y₂ oy₁ oy₂, H _ _ _ _ equiv_rfl))
  (λ x₁ x₂ ox₁ ox₂ h, funext $ quotient.ind $ by exact λ ⟨y, oy⟩, H _ _ _ _ h equiv_rfl)

noncomputable instance : linear_ordered_comm_ring surreal :=
{ add := lift₂ (λ (x y : pgame) (ox) (oy), ⟦⟨x + y, ox.add oy⟩⟧)
    (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, quotient.sound $ add_congr hx hy),
  add_assoc := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, exact quotient.sound add_assoc_equiv },
  zero := 0,
  zero_add := by { rintros ⟨a⟩, exact quotient.sound (zero_add_equiv a) },
  add_zero := by { rintros ⟨a⟩, exact quotient.sound (add_zero_equiv a) },
  neg := lift (λ x ox, ⟦⟨-x, ox.neg⟩⟧) (λ _ _ _ _ a, quotient.sound $ neg_congr a),
  add_left_neg := by { rintros ⟨a⟩, exact quotient.sound (add_left_neg_equiv a) },
  add_comm := by { rintros ⟨_⟩ ⟨_⟩, exact quotient.sound add_comm_equiv },
  le := lift₂ (λ x y _ _, x ≤ y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext $ le_congr hx hy),
  lt := lift₂ (λ x y _ _, x < y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext $ lt_congr hx hy),
  le_refl := by { rintros ⟨_⟩, apply @le_rfl pgame },
  le_trans := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, apply @le_trans pgame },
  lt_iff_le_not_le := by { rintros ⟨_, ox⟩ ⟨_, oy⟩, exact lt_iff_le_not_le },
  le_antisymm := by { rintros ⟨_⟩ ⟨_⟩ h₁ h₂, exact quotient.sound ⟨h₁, h₂⟩ },
  add_le_add_left := by { rintros ⟨_⟩ ⟨_⟩ hx ⟨_⟩, exact @add_le_add_left pgame _ _ _ _ _ hx _ },
  le_total := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; classical; exact
    or_iff_not_imp_left.2 (λ h, (pgame.not_le.1 h).le oy ox),
  decidable_le := classical.dec_rel _,
  mul := lift₂ (λ x y ox oy, ⟦⟨x * y, ox.mul oy⟩⟧)
    (λ _ _ _ _ ox₁ oy₁ ox₂ oy₂ hx hy, quotient.sound $ ox₁.mul_congr ox₂ oy₁ oy₂ hx hy),
  mul_assoc := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quotient.sound (mul_assoc_equiv x.1 y.1 z.1) },
  one := 1,
  one_mul := by { rintro ⟨x⟩, exact quotient.sound (one_mul_equiv x) },
  mul_one := by { rintro ⟨x⟩, exact quotient.sound (mul_one_equiv x) },
  left_distrib := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quotient.sound (left_distrib_equiv x y z) },
  right_distrib := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quotient.sound (right_distrib_equiv x y z) },
  zero_le_one := zero_le_one,
  mul_pos := by { rintro ⟨x⟩ ⟨y⟩, exact x.2.mul_pos y.2 },
  exists_pair_ne := ⟨0, 1, pgame.zero_lt_one.lf.not_equiv ∘ quotient.exact⟩,
  mul_comm := by { rintro ⟨x⟩ ⟨y⟩, exact quotient.sound (mul_comm_equiv x y) } }

end surreal

open surreal

namespace ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def to_surreal : ordinal ↪o surreal :=
{ to_fun := λ o, mk _ (numeric_to_pgame o),
  inj' := λ a b h, to_pgame_equiv_iff.1 (quotient.exact h),
  map_rel_iff' := @to_pgame_le_iff }

end ordinal


-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO define the inclusion of groups `surreal → game`
-- def to_game : surreal → game := surreal.lift (λ x _, ⟦x⟧) (λ _ _ _ _ h, quotient.sound h)

-- TODO define the inverse on the surreals


/- inline all instances before linear_ordered_add_comm_group into one ..? -/

/- Any set of surreals has an upper bound (just take the set as left options),
  but it has a least upper bound iff it has a maximal element. -/

/- order/ring embedding from the reals .. can use only rationals as options?
  rationals are "simpler" than general surreals ..? embedding unique?
  dyadics should suffice ... -/

/- make quot_neg_mul a relabelling?  -/
