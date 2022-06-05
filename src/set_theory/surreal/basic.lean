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
`pgame.numeric.args_ty` that encompasses both types of arguments. The proof is carried out with
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
instance : inhabited surreal := ⟨0⟩

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

instance : has_le surreal :=
⟨lift₂ (λ x y _ _, x ≤ y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext (le_congr hx hy))⟩

instance : has_lt surreal :=
⟨lift₂ (λ x y _ _, x < y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext (lt_congr hx hy))⟩

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : has_add surreal  :=
⟨surreal.lift₂
  (λ (x y : pgame) (ox) (oy), ⟦⟨x + y, ox.add oy⟩⟧)
  (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, quotient.sound (add_congr hx hy))⟩

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
instance : has_neg surreal  :=
⟨surreal.lift
  (λ x ox, ⟦⟨-x, ox.neg⟩⟧)
  (λ _ _ _ _ a, quotient.sound (neg_congr a))⟩

def to_game : surreal → game := surreal.lift (λ x _, ⟦x⟧) (λ _ _ _ _ h, quotient.sound h)

instance : ordered_add_comm_group surreal :=
{ add               := (+),
  add_assoc         := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, exact quotient.sound add_assoc_equiv },
  zero              := 0,
  zero_add          := by { rintros ⟨_⟩, exact quotient.sound (zero_add_equiv a) },
  add_zero          := by { rintros ⟨_⟩, exact quotient.sound (add_zero_equiv a) },
  neg               := has_neg.neg,
  add_left_neg      := by { rintros ⟨_⟩, exact quotient.sound (add_left_neg_equiv a) },
  add_comm          := by { rintros ⟨_⟩ ⟨_⟩, exact quotient.sound add_comm_equiv },
  le                := (≤),
  lt                := (<),
  le_refl           := by { rintros ⟨_⟩, apply @le_rfl pgame },
  le_trans          := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, apply @le_trans pgame },
  lt_iff_le_not_le  := by { rintros ⟨_, ox⟩ ⟨_, oy⟩, exact lt_iff_le_not_le },
  le_antisymm       := by { rintros ⟨_⟩ ⟨_⟩ h₁ h₂, exact quotient.sound ⟨h₁, h₂⟩ },
  add_le_add_left   := by { rintros ⟨_⟩ ⟨_⟩ hx ⟨_⟩, exact @add_le_add_left pgame _ _ _ _ _ hx _ } }

noncomputable instance : linear_ordered_add_comm_group surreal :=
{ le_total := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; classical; exact
    or_iff_not_imp_left.2 (λ h, (pgame.not_le.1 h).le oy ox),
  decidable_le := classical.dec_rel _,
  ..surreal.ordered_add_comm_group }

end surreal

open surreal

namespace ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def to_surreal : ordinal ↪o surreal :=
{ to_fun := λ o, mk _ (numeric_to_pgame o),
  inj' := λ a b h, to_pgame_equiv_iff.1 (quotient.exact h),
  map_rel_iff' := @to_pgame_le_iff }

end ordinal

namespace pgame

namespace numeric

def P3 (x₁ x₂ y₁ y₂ : pgame) := x₁ * y₂ + x₂ * y₁ < x₁ * y₁ + x₂ * y₂
def P1' (x₁ x₂ x₃ y₁ y₂ y₃ : pgame) := x₁ * y₁ + x₂ * y₂ - x₁ * y₂ < x₃ * y₁ + x₂ * y₃ - x₃ * y₃

lemma P1'_swap {x₁ x₂ x₃ y₁ y₂ y₃} : P1' x₁ x₂ x₃ y₁ y₂ y₃ ↔ P1' x₃ x₂ x₁ (-y₁) (-y₃) (-y₂) :=
begin
  simp only [P1', lt_iff_game_lt], convert neg_lt_neg_iff,
  iterate 2 { dsimp, simp only [quot_mul_neg], abel },
  iterate 2 { apply_instance },
end

lemma P3.comm {x₁ x₂ y₁ y₂} : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ :=
begin
  simp only [P3, lt_iff_game_lt], dsimp,
  rw add_comm, congr' 3; rw quot_mul_comm,
end

lemma P3.trans {x₁} (x₂) {x₃ y₁ y₂} : P3 x₁ x₂ y₁ y₂ → P3 x₂ x₃ y₁ y₂ → P3 x₁ x₃ y₁ y₂ :=
λ h₁ h₂, begin
  rw [P3, lt_iff_game_lt, ← add_lt_add_iff_left ⟦x₂ * y₁ + x₂ * y₂⟧],
  convert lt_iff_game_lt.1 (add_lt_add h₁ h₂); dsimp; abel,
end

lemma P3_neg {x₁ x₂ y₁ y₂} : P3 x₁ x₂ y₁ y₂ ↔ P3 (-x₂) (-x₁) y₁ y₂ :=
begin
  simp only [P3, lt_iff_game_lt],  dsimp, simp only [quot_neg_mul],
  rw ← neg_lt_neg_iff, convert iff.rfl; abel,
end

lemma P3_neg' {x₁ x₂ y₁ y₂} : P3 x₁ x₂ y₁ y₂ ↔ P3 x₁ x₂ (-y₂) (-y₁) :=
by rw [P3.comm, P3_neg, P3.comm]

def P24 (x₁ x₂ y : pgame) : Prop :=
(x₁ ≈ x₂ → ⟦x₁ * y⟧ = ⟦x₂ * y⟧) ∧
(x₁ < x₂ → (∀ i, P3 x₁ x₂ (y.move_left i) y) ∧ ∀ j, P3 x₁ x₂ ((-y).move_left j) (-y))

lemma P24_neg {x₁ x₂ y} : P24 x₁ x₂ y ↔ P24 (-x₂) (-x₁) y :=
begin
  simp_rw P24, apply and_congr; apply iff.imp,
  { rw [equiv_comm, neg_equiv_iff] },
  { rw [quot_neg_mul, quot_neg_mul, eq_comm, neg_inj] },
  { rw neg_lt_iff },
  { apply and_congr; { apply forall_congr, intro, rw P3_neg } },
end

lemma P24_neg' {x₁ x₂ y} : P24 x₁ x₂ y ↔ P24 x₁ x₂ (-y) :=
begin
  simp_rw P24, apply and_congr; apply iff.imp,
  { refl },
  { rw [quot_mul_neg, quot_mul_neg, neg_inj] },
  { refl },
  { rw neg_neg, apply and_comm },
end

lemma P24.L {x₁ x₂ y} (h : P24 x₁ x₂ y) (hl : x₁ < x₂) (i) : P3 x₁ x₂ (y.move_left i) y :=
(h.2 hl).1 i

lemma P24.R {x₁ x₂ y} (h : P24 x₁ x₂ y) (hl : x₁ < x₂) (j) : P3 x₁ x₂ y (y.move_right j) :=
by { rw P3_neg', convert (h.2 hl).2 (to_left_moves_neg j), simp }

inductive mul_args : Type (u+1)
| P1 (x y : pgame.{u}) : mul_args
| P24 (x₁ x₂ y : pgame.{u}) : mul_args

def _root_.multiset.numeric : set (multiset pgame) := λ s, ∀ x ∈ s, numeric x

def to_multiset : mul_args → multiset pgame
| (mul_args.P1 x y) := {x, y}
| (mul_args.P24 x₁ x₂ y) := {x₁, x₂, y}

section
open multiset
lemma P1_mem {x y} : x ∈ to_multiset (mul_args.P1 x y) ∧ y ∈ to_multiset (mul_args.P1 x y) :=
⟨or.inl rfl, or.inr $ or.inl rfl⟩

lemma P24_mem {x₁ x₂ y} : x₁ ∈ to_multiset (mul_args.P24 x₁ x₂ y) ∧
  x₂ ∈ to_multiset (mul_args.P24 x₁ x₂ y) ∧ y ∈ to_multiset (mul_args.P24 x₁ x₂ y) :=
⟨or.inl rfl, or.inr $ or.inl rfl, or.inr $ or.inr $ or.inl rfl⟩
end

def hyp : mul_args → Prop
| (mul_args.P1 x y) := numeric (x * y)
| (mul_args.P24 x₁ x₂ y) := P24 x₁ x₂ y

open relation
def ices := inv_image (trans_gen $ cut_expand is_option) to_multiset

lemma ices_wf : well_founded ices := inv_image.wf _ wf_is_option.cut_expand.trans_gen

lemma numeric.is_option {x' x} (h : is_option x' x) (hx : numeric x) : numeric x' :=
by { cases h, apply hx.move_left, apply hx.move_right }

/- being numeric is downward closed under `ices` -/
lemma numeric_dc {a' a} (h : ices a' a) (ha : (to_multiset a).numeric) : (to_multiset a').numeric :=
begin
  have := @cut_expand_dc _ is_option wf_is_option.is_irrefl.1 _ @numeric.is_option,
  apply @trans_gen.head_induction_on _ _ _ (λ a _, multiset.numeric a) _ h,
  exacts [λ s hc, this hc ha, λ s' s hc _ hs, this hc hs],
end

section
open multiset

lemma ices_symm (a x y) : ices a (mul_args.P1 x y) ↔ ices a (mul_args.P1 y x) :=
by { dsimp [ices, inv_image, to_multiset], convert iff.rfl using 2, apply pair_comm }

lemma ices_symm' (a x₁ x₂ y) : ices a (mul_args.P24 x₁ x₂ y) ↔ ices a (mul_args.P24 x₂ x₁ y) :=
by { dsimp [ices, inv_image, to_multiset],
  convert iff.rfl using 2, simp only [← singleton_add], rw add_left_comm }

end

section main

/- restricted inductive hypothesis -/
def ihr (x y) : Prop :=
∀ ⦃x₁ x₂ y'⦄, is_option x₁ x → is_option x₂ x → (y' = y ∨ is_option y' y) → P24 x₁ x₂ y'

variables {x y : pgame.{u}} (ih : ∀ a, ices a (mul_args.P1 x y) → hyp a)

lemma ihr_neg : ihr x y → ihr (-x) y :=
λ h x₁ x₂ y' h₁ h₂ hy, by { rw is_option_neg at h₁ h₂, exact P24_neg.2 (h h₂ h₁ hy) }

lemma ihr_neg' : ihr x y → ihr x (-y) :=
λ h x₁ x₂ y', by { rw [eq_neg_iff_eq_neg, eq_comm, is_option_neg, P24_neg'], apply h }

include ih

lemma P1x {x'} (h : is_option x' x) : (x' * y).numeric :=
ih (mul_args.P1 x' y) $ trans_gen.single $ cut_expand_pair_left h

lemma P1y {y'} (h : is_option y' y) : (x * y').numeric :=
ih (mul_args.P1 x y') $ trans_gen.single $ cut_expand_pair_right h

lemma P1xy {x' y'} (hx : is_option x' x) (hy : is_option y' y) : (x' * y').numeric :=
ih (mul_args.P1 x' y') $ trans_gen.tail (trans_gen.single $ cut_expand_pair_right hy) $
  cut_expand_pair_left hx

lemma ihxy_of_ih : ihr x y :=
begin
  rintro x₁ x₂ y' h₁ h₂ (rfl|hy); apply ih (mul_args.P24 _ _ _),
  swap 2, refine trans_gen.tail _ (cut_expand_pair_right hy),
  all_goals { exact trans_gen.single (cut_expand_double_left h₁ h₂) },
end

lemma ihyx_of_ih : ihr y x := ihxy_of_ih $ by { simp_rw ices_symm, exact ih }

omit ih

lemma P3yyxx (hy : numeric y) (ihyx : ihr y x) (i k l) :
  P3 (x.move_left i) x (y.move_left k) (-(-y).move_left l) :=
P3.comm.2 $ P24.L
  (ihyx (is_option.move_left k) (is_option_neg.1 $ is_option.move_left l) (or.inl rfl))
  (by { rw ← move_right_neg_symm, apply hy.left_lt_right }) i

lemma P24xxy (ihxy : ihr x y) (i j) : P24 (x.move_left i) (x.move_left j) y :=
ihxy (is_option.move_left i) (is_option.move_left j) (or.inl rfl)

lemma P1'_of_eq {x₁ x₂ x₃ y₁ y₂ y₃} (h₁₃ : x₁ ≈ x₃) (h₁ : P24 x₁ x₃ y₁) (h₃ : P24 x₁ x₃ y₃)
  (h3 : P3 x₁ x₂ y₂ y₃) : P1' x₁ x₂ x₃ y₁ y₂ y₃ :=
begin
  rw [P1', lt_iff_game_lt], dsimp,
  rw [← h₁.1 h₁₃, ← h₃.1 h₁₃, sub_lt_sub_iff],
  convert add_lt_add_left (lt_iff_game_lt.1 h3) ⟦x₁ * y₁⟧ using 1; abel,
end

lemma P1'_of_lt {x₁ x₂ x₃ y₁ y₂ y₃} (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) :
  P1' x₁ x₂ x₃ y₁ y₂ y₃ :=
begin
  rw P1', rw P3 at h₁ h₂,
  rw lt_iff_game_lt at h₁ h₂ ⊢,
  dsimp at h₁ h₂ ⊢,
  rw sub_lt_sub_iff,
  rw ← add_lt_add_iff_left ⟦x₃ * y₂⟧,
  convert (add_lt_add h₁ h₂) using 1; abel,
end

lemma mul_option_lt_iff_P1' {i j k l} :
  ⟦mul_option x y i k⟧ < -⟦mul_option x (-y) j l⟧ ↔
  P1' (x.move_left i) x (x.move_left j) y (y.move_left k) (-(-y).move_left l) :=
begin
  dsimp [mul_option, P1'], rw lt_iff_game_lt, convert iff.rfl using 2,
  dsimp, rw [neg_sub', neg_add], congr' 1, congr' 1,
  all_goals { rw quot_mul_neg }, rw neg_neg,
end

variables (hx : numeric x) (hy : numeric y) (ihxy : ihr x y) (ihyx : ihr y x)
include hy ihxy ihyx

lemma mul_option_lt_of_lt (i j k l) (h : x.move_left i < x.move_left j) :
  ⟦mul_option x y i k⟧ < -⟦mul_option x (-y) j l⟧ :=
mul_option_lt_iff_P1'.2 $ P1'_of_lt (P3yyxx hy ihyx j k l) (P24.L (P24xxy ihxy i j) h k)

include hx
lemma mul_option_lt (i j k l) : ⟦mul_option x y i k⟧ < -⟦mul_option x (-y) j l⟧ :=
begin
  obtain (h|h|h) := lt_or_equiv_or_gt (hx.move_left i) (hx.move_left j),
  { exact mul_option_lt_of_lt hy ihxy ihyx i j k l h },
  { have ml := @is_option.move_left,
    exact mul_option_lt_iff_P1'.2 (P1'_of_eq h (P24xxy ihxy i j)
      (ihxy (ml i) (ml j) $ or.inr $ is_option_neg.1 $ ml l) $ P3yyxx hy ihyx i k l) },
  { rw [mul_option_neg_neg, lt_neg],
    exact mul_option_lt_of_lt hy.neg (ihr_neg' ihxy) (ihr_neg ihyx) j i l _ h },
end

omit ihxy ihyx
include ih

theorem P1_of_hyp : (x * y).numeric :=
begin
  have ihxy := ihxy_of_ih ih, have ihxyn := ihr_neg (ihr_neg' ihxy),
  have ihyx := ihyx_of_ih ih, have ihyxn := ihr_neg (ihr_neg' ihyx),
  rw numeric_def,
  refine ⟨_, _, _⟩,
  { simp_rw lt_iff_game_lt, intro i', rw right_moves_mul_iff, split; intros j l;
    revert i'; rw left_moves_mul_iff (gt _); split; intros i k,
    { apply mul_option_lt hx hy ihxy ihyx },
    { simp only [← mul_option_symm (-y)], rw mul_option_neg_neg x,
      apply mul_option_lt hy.neg hx.neg ihyxn ihxyn },
    { simp only [← mul_option_symm y], apply mul_option_lt hy hx ihyx ihxy },
    { rw mul_option_neg_neg y, apply mul_option_lt hx.neg hy.neg ihxyn ihyxn } },
  all_goals { cases x, cases y, rintro (⟨i,j⟩|⟨i,j⟩) },
  rw mk_mul_move_left_inl, swap 2, rw mk_mul_move_left_inr,
  swap 3, rw mk_mul_move_right_inl, swap 4, rw mk_mul_move_right_inr,
  all_goals { apply numeric.sub, apply numeric.add,
    apply P1x ih, swap 2, apply P1y ih, swap 3, apply P1xy ih },
  all_goals { apply is_option.mk_left <|> apply is_option.mk_right },
end

omit ih hx hy

def ihr' (x₁ x₂ y) : Prop :=
∀ ⦃z⦄, (is_option z x₁ → P24 z x₂ y) ∧ (is_option z x₂ → P24 x₁ z y) ∧ (is_option z y → P24 x₁ x₂ z)

def ihr'' (x₁ x₂ y : pgame) : Prop :=
∀ ⦃z w⦄, is_option w y → (is_option z x₁ → P24 z x₂ w) ∧ (is_option z x₂ → P24 x₁ z w)

variables {x₁ x₂ x' y' : pgame.{u}} (ih' : ∀ a, ices a (mul_args.P24 x₁ x₂ y) → hyp a)
include ih'

lemma ih₁₂_of_ih' : ihr' x₁ x₂ y :=
begin
  refine (λ z, ⟨_, _, _⟩);
  refine λ h, ih' (mul_args.P24 _ _ _) (trans_gen.single _),
  { exact (cut_expand_add_right {y}).2 (cut_expand_pair_left h) },
  { exact (cut_expand_add_left {x₁}).2 (cut_expand_pair_left h) },
  { exact (cut_expand_add_left {x₁}).2 (cut_expand_pair_right h) },
end

lemma ih₂₁_of_ih' : ihr' x₂ x₁ y := ih₁₂_of_ih' $ by { simp_rw ices_symm', exact ih' }

lemma ihr''_of_ih' : ihr'' x₁ x₂ y :=
begin
  refine (λ z w h, ⟨_, _⟩);
  refine λ h', ih' (mul_args.P24 _ _ _) (trans_gen.tail (trans_gen.single _) $
    (cut_expand_add_left {x₁}).2 $ cut_expand_pair_right h),
  { exact (cut_expand_add_right {w}).2 (cut_expand_pair_left h') },
  { exact (cut_expand_add_right {w}).2 (cut_expand_pair_right h') },
end

lemma numeric_of_ih' : (x₁ * y).numeric ∧ (x₂ * y).numeric :=
begin
  split; refine ih' (mul_args.P1 _ _) (trans_gen.single _),
  exact (cut_expand_add_right {y}).2 ((cut_expand_add_left {x₁}).2 cut_expand_zero),
  exact (cut_expand_add_right {x₂, y}).2 cut_expand_zero,
end

omit ih'

lemma ihr'_neg : ihr' x₁ x₂ y → ihr' (-x₂) (-x₁) y :=
begin
  simp_rw [ihr', is_option_neg],
  refine (λ h z, ⟨_, _, _⟩); rw P24_neg,
  { convert (@h _).2.1, simp },
  { convert (@h _).1, simp },
  { convert (@h _).2.2, simp },
end

lemma ihr'_neg' : ihr' x₁ x₂ y → ihr' x₁ x₂ (-y) :=
begin
  simp_rw [ihr', ← P24_neg', is_option_neg],
  exact λ h z, ⟨(@h _).1, (@h _).2.1, P24_neg'.2 ∘ (@h _).2.2⟩,
end

lemma ihr''_neg : ihr'' x₁ x₂ y → ihr'' (-x₂) (-x₁) y :=
begin
  simp_rw [ihr'', is_option_neg],
  refine (λ h z w h', ⟨_, _⟩); rw P24_neg,
  { convert (@h _ _ h').2, simp },
  { convert (@h _ _ h').1, simp },
end

lemma ihr''_neg' : ihr'' x₁ x₂ y → ihr'' x₁ x₂ (-y) :=
begin
  simp_rw [ihr'', is_option_neg],
  refine (λ h z w h', ⟨_, _⟩); rw P24_neg',
  exacts [(h h').1, (h h').2],
end

lemma P2'_of_P24 (h₁ : P24 x₁ x₂ y') (h₂ : P3 x' x₂ y' y) (he : x₁ ≈ x₂) :
  x' * y + x₁ * y' - x' * y' < x₂ * y :=
by { rw lt_iff_game_lt, dsimp, rw [h₁.1 he, sub_lt_iff_lt_add'], exact lt_iff_game_lt.1 h₂ }

lemma left_lt_mul_aux (hn : x₁.numeric) (h : ihr' x₁ x₂ y) (he : x₁ ≈ x₂) (i j) :
  mul_option x₁ y i j < x₂ * y :=
P2'_of_P24 ((@h _).2.2 $ is_option.move_left j) (P24.L ((@h _).1 $ is_option.move_left i)
  (by {rw ← lt_congr_right he, apply hn.move_left_lt}) j) he

lemma mul_le_mul_right (h₁ : x₁.numeric) (h₂ : x₂.numeric)
  (h₁₂ : ihr' x₁ x₂ y) (h₂₁ : ihr' x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y :=
le_of_forall_lt begin
  have he' := neg_congr he, split; simp_rw lt_iff_game_lt,
  { rw left_moves_mul_iff (gt _), split,
    { exact left_lt_mul_aux h₁ h₁₂ he },
    { rw ← quot_neg_mul_neg, exact left_lt_mul_aux h₁.neg (ihr'_neg $ ihr'_neg' h₂₁) he' } },
  { rw right_moves_mul_iff, split; intros; rw lt_neg,
    { rw ← quot_mul_neg, apply left_lt_mul_aux h₂ (ihr'_neg' h₂₁) he.symm },
    { rw ← quot_neg_mul, apply left_lt_mul_aux h₂.neg (ihr'_neg h₁₂) he'.symm } },
end

def mul_option_lt_mul (x y) : Prop := ∀ {i j}, ⟦mul_option x y i j⟧ < ⟦x * y⟧

lemma lt_mul_of_numeric (hn : (x * y).numeric) :
  (mul_option_lt_mul x y ∧ mul_option_lt_mul (-x) (-y)) ∧
  mul_option_lt_mul x (-y) ∧ mul_option_lt_mul (-x) y :=
begin
  split,
  { have h := hn.move_left_lt, simp_rw lt_iff_game_lt at h,
    convert (left_moves_mul_iff (gt _)).1 h, rw ← quot_neg_mul_neg, refl },
  { have h := hn.lt_move_right, simp_rw [lt_iff_game_lt, right_moves_mul_iff] at h,
    refine h.imp _ _; refine forall₂_imp _; intros a b; rw lt_neg,
    { rw ← quot_mul_neg, exact id }, { rw ← quot_neg_mul, exact id } },
end

lemma mul_option_lt_iff_P3 {i j} :
  ⟦mul_option x y i j⟧ < ⟦x * y⟧ ↔ P3 (x.move_left i) x (y.move_left j) y :=
by { dsimp [mul_option, P3, lt_iff_game_lt], exact sub_lt_iff_lt_add' }

def P3_cond (x₁ x' x₂ y₁ y₂) : Prop :=
P24 x₁ x' y₁ ∧ P24 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

lemma P3_cond_of_ih' (h : ihr' x₁ x₂ y) (h' : ihr'' x₁ x₂ y) (hl : mul_option_lt_mul x₂ y)
  (i j) : P3_cond x₁ (x₂.move_left i) x₂ (y.move_left j) y :=
let ml := @is_option.move_left, h24 := (@h _).2.1 (ml i) in
⟨(h' $ ml j).2 (ml i), h24, mul_option_lt_iff_P3.1 hl, λ l, h24.L l _⟩

lemma P3_of_le_left {y₁ y₂} (i) (h : P3_cond x₁ (x₂.move_left i) x₂ y₁ y₂)
  (hl : x₁ ≤ x₂.move_left i) : P3 x₁ x₂ y₁ y₂ :=
begin
  obtain (hl|he) := lt_or_equiv_of_le hl,
  { exact (h.2.2.2 hl).trans _ h.2.2.1 },
  { rw [P3, lt_iff_game_lt], dsimp, rw [h.1.1 he, h.2.1.1 he], exact h.2.2.1 },
end

lemma P3_of_lt {y₁ y₂} (h : ∀ i, P3_cond x₁ (x₂.move_left i) x₂ y₁ y₂)
  (hs : ∀ i, P3_cond (-x₂) ((-x₁).move_left i) (-x₁) y₁ y₂) (hl : x₁ < x₂) : P3 x₁ x₂ y₁ y₂ :=
begin
  obtain (⟨i,hi⟩|⟨i,hi⟩) := lf_iff_forall_le.1 (lf_of_lt hl),
  exacts [P3_of_le_left i (h i) hi, P3_neg.2 $
    P3_of_le_left _ (hs _) $ by { convert neg_le_neg (le_iff_game_le.1 hi), rw move_left_neg }],
end

theorem P124 (a : mul_args) : (to_multiset a).numeric → hyp a :=
begin
  apply ices_wf.induction a,
  intros a ih ha,
  replace ih : ∀ a', ices a' a → hyp a' := λ a' hr, ih a' hr (numeric_dc hr ha),
  cases a with x y x₁ x₂ y,
  { exact P1_of_hyp ih (ha x P1_mem.1) (ha y P1_mem.2) },
  obtain ⟨h, hs, h'⟩ := ⟨ih₁₂_of_ih' ih, ih₂₁_of_ih' ih, ihr''_of_ih' ih⟩,
  obtain ⟨hn, hn'⟩ := ⟨ihr'_neg' h, ihr''_neg' h'⟩,
  refine ⟨λ he, equiv_iff_game_eq.1 _, λ hl, _⟩,
  { obtain ⟨h₁, h₂⟩ := ⟨ha x₁ P24_mem.1, ha x₂ P24_mem.2.1⟩,
    exact ⟨mul_le_mul_right h₁ h₂ h hs he, mul_le_mul_right h₂ h₁ hs h he.symm⟩ },
  obtain ⟨hn₁, hn₂⟩ := numeric_of_ih' ih,
  obtain ⟨⟨h₁, -⟩, h₂, -⟩ := lt_mul_of_numeric hn₂,
  obtain ⟨⟨-, h₃⟩, -, h₄⟩ := lt_mul_of_numeric hn₁,
  split; intro j; refine P3_of_lt _ _ hl; intro i; apply P3_cond_of_ih',
  exacts [h, h', @h₁, ihr'_neg h, ihr''_neg h', @h₄, hn, hn', @h₂, ihr'_neg hn, ihr''_neg hn', @h₃],
end

include hx hy

theorem mul : numeric (x * y) :=
P124 (mul_args.P1 x y) $ by rintro _ (rfl|rfl|⟨⟨⟩⟩); assumption

omit hx
variables (h₁ : numeric x₁) (h₂ : numeric x₂)
include h₁ h₂

theorem P24_out (hy : numeric y) : P24 x₁ x₂ y :=
P124 (mul_args.P24 x₁ x₂ y) $ by rintro _ (rfl|rfl|rfl|⟨⟨⟩⟩); assumption

theorem mul_congr_left (hy : numeric y) (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
equiv_iff_game_eq.2 $ (P24_out h₁ h₂ hy).1 he

theorem mul_congr_right (he : x₁ ≈ x₂) : y * x₁ ≈ y * x₂ :=
(mul_comm_equiv _ _).trans $ (mul_congr_left h₁ h₂ hy he).trans $ mul_comm_equiv _ _

omit hy
variables {y₁ y₂ : pgame.{u}} (hy₁ : numeric y₁) (hy₂ : numeric y₂)
include hy₁ hy₂

theorem mul_congr (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
(mul_congr_left h₁ h₂ hy₁ hx).trans (mul_congr_right h₂ hy₁ hy₂ hy)

lemma P3_of_lt_of_lt (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ :=
begin
  revert x₁ x₂, rw ← prod.forall',
  refine λ t, (wf_is_option.game_add wf_is_option).induction t _,
  rintro ⟨x₁, x₂⟩ ih h₁ h₂ hx, refine P3_of_lt _ _ hx; intro i,
  { have hi := h₂.move_left i,
    refine ⟨_, _, _, _⟩,
    exact P24_out h₁ hi hy₁,
    exact P24_out h₁ hi hy₂,
    exact P3.comm.2 (((P24_out hy₁ hy₂ h₂).2 hy).1 _),
    exact ih _ (game_add.snd $ is_option.move_left i) h₁ hi },
  { have hi := h₁.neg.move_left i,
    refine ⟨_, _, _, _⟩,
    exact P24_out h₂.neg hi hy₁,
    exact P24_out h₂.neg hi hy₂,
    exact P3.comm.2 (((P24_out hy₁ hy₂ h₁).2 hy).2 _),
    { rw [move_left_neg', ← P3_neg, neg_lt_iff],
      exact ih _ (game_add.fst $ is_option.move_right _) (h₁.move_right _) h₂ } },
end

omit hy₁ hy₂

lemma mul_pos (hp₁ : 0 < x₁) (hp₂ : 0 < x₂) : 0 < x₁ * x₂ :=
begin
  rw lt_iff_game_lt,
  convert lt_iff_game_lt.1 (P3_of_lt_of_lt numeric_zero h₁ numeric_zero h₂ hp₁ hp₂) using 1;
  simpa,
end

end main

end numeric

end pgame

namespace surreal

noncomputable instance : linear_ordered_comm_ring surreal :=
{ mul := surreal.lift₂
    (λ x y ox oy, ⟦⟨x * y, ox.mul oy⟩⟧)
    (λ _ _ _ _ ox₁ oy₁ ox₂ oy₂ hx hy, quotient.sound $ ox₁.mul_congr ox₂ oy₁ oy₂ hx hy),
  mul_assoc := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quotient.sound (mul_assoc_equiv x.1 y.1 z.1) },
  one := 1,
  one_mul := by { rintro ⟨x⟩, exact quotient.sound (one_mul_equiv x) },
  mul_one := by { rintro ⟨x⟩, exact quotient.sound (mul_one_equiv x) },
  left_distrib := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quotient.sound (left_distrib_equiv x y z) },
  right_distrib := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quotient.sound (right_distrib_equiv x y z) },
  zero_le_one := zero_le_one,
  mul_pos := by { rintro ⟨x⟩ ⟨y⟩, exact x.2.mul_pos y.2 },
  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩,
  mul_comm := by { rintro ⟨x⟩ ⟨y⟩, exact quotient.sound (mul_comm_equiv x y) },
  .. surreal.linear_ordered_add_comm_group }

end surreal


-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO define the inclusion of groups `surreal → game`
-- TODO define the inverse on the surreals

/- make quot_neg_mul a relabelling?  -/

/- mem_subsingleton etc. directly rintro -/
/- inline all instances before linear_ordered_add_comm_group into one ..? -/

/- Any set of surreals has an upper bound (just take the set as left options),
  but it has a least upper bound iff it has a maximal element. -/

/- order/ring embedding from the reals .. can use only rationals as options?
 rationals are "simpler" than general surreals ..? embedding unique? -/

/- docstrings explaining the proof .. -/
/- clear separation of calculation part vs. inductive hypothesis application part /
  cut_expand relation verification part /
  numeric hypothesis part handled at once .. -/
/- utilize symmetry .. to minimize calculation .. -/

/- clean up + docstrings .. -/
/-! The main inductive argument to show that being numeric is closed under multiplication,
  that multiplying a number by equivalent numbers results in equivalent numbers, and
  that the product of two positive numbers is positive
  (Theorem 8 in [conway], Theorem 3.8 in [schleicher_stoll]).

  We follow the proof in [schleicher_stoll], except that we use the well-foundedness of
  the hydra relation `cut_expand` on `multiset pgame` instead of the argument based
  on a depth function in the paper.  -/


/- `arg_ty` .. ? `arg_rel` .. in `inuction` namespace .. -/
/- ihr' -> ih24, ihr'' -> ih4, ihr -> ih1, hyp -> P124, P3cond -> ih3 -/
/- specialization of induction hypothesis -/


/- `iitgceio` or `itco` .. `inv_image trans_gen cut_expand is_option` -/


/- real algebraically closed .. -/


/- ordinals are exactly surreals without right options (recursively) -/

/-  theorem mul_lt_iff_lt_one_left {α : Type u} [linear_ordered_semiring α] {a b : α} (hb : 0 < b) :
a * b < b ↔ a < 1 -/
