/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/

import algebra.order.hom.monoid
import set_theory.game.ordinal

/-!
# Surreal numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties

Surreal numbers inherit the relations `≤` and `<` from games (`surreal.has_le` and
`surreal.has_lt`), and these relations satisfy the axioms of a partial order.

## Algebraic operations

We show that the surreals form a linear ordered commutative group.

One can also map all the ordinals into the surreals!

### Multiplication of surreal numbers

The proof that multiplication lifts to surreal numbers is surprisingly difficult and is currently
missing in the library. A sample proof can be found in Theorem 3.8 in the second reference below.
The difficulty lies in the length of the proof and the number of theorems that need to proven
simultaneously. This will make for a fun and challenging project.

The branch `surreal_mul` contains some progress on this proof.

### Todo

- Define the field structure on the surreals.

## References

* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
-/

universes u

open_locale pgame

namespace pgame

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def numeric : pgame → Prop
| ⟨l, r, L, R⟩ :=
  (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ (∀ j, numeric (R j))

lemma numeric_def {x : pgame} : numeric x ↔ (∀ i j, x.move_left i < x.move_right j) ∧
  (∀ i, numeric (x.move_left i)) ∧ (∀ j, numeric (x.move_right j)) :=
by { cases x, refl }

namespace numeric

lemma mk {x : pgame} (h₁ : ∀ i j, x.move_left i < x.move_right j)
  (h₂ : ∀ i, numeric (x.move_left i)) (h₃ : ∀ j, numeric (x.move_right j)) : numeric x :=
numeric_def.2 ⟨h₁, h₂, h₃⟩

lemma left_lt_right {x : pgame} (o : numeric x) (i : x.left_moves) (j : x.right_moves) :
  x.move_left i < x.move_right j :=
by { cases x, exact o.1 i j }
lemma move_left {x : pgame} (o : numeric x) (i : x.left_moves) :
  numeric (x.move_left i) :=
by { cases x, exact o.2.1 i }
lemma move_right {x : pgame} (o : numeric x) (j : x.right_moves) :
  numeric (x.move_right j) :=
by { cases x, exact o.2.2 j }

end numeric

@[elab_as_eliminator]
theorem numeric_rec {C : pgame → Prop}
  (H : ∀ l r (L : l → pgame) (R : r → pgame),
    (∀ i j, L i < R j) → (∀ i, numeric (L i)) → (∀ i, numeric (R i)) →
    (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
  ∀ x, numeric x → C x
| ⟨l, r, L, R⟩ ⟨h, hl, hr⟩ :=
  H _ _ _ _ h hl hr (λ i, numeric_rec _ (hl i)) (λ i, numeric_rec _ (hr i))

theorem relabelling.numeric_imp {x y : pgame} (r : x ≡r y) (ox : numeric x) : numeric y :=
begin
  induction x using pgame.move_rec_on with x IHl IHr generalizing y,
  apply numeric.mk (λ i j, _) (λ i, _) (λ j, _),
  { rw ←lt_congr (r.move_left_symm i).equiv (r.move_right_symm j).equiv,
    apply ox.left_lt_right },
  { exact IHl _ (ox.move_left _) (r.move_left_symm i) },
  { exact IHr _ (ox.move_right _) (r.move_right_symm j) }
end

/-- Relabellings preserve being numeric. -/
theorem relabelling.numeric_congr {x y : pgame} (r : x ≡r y) : numeric x ↔ numeric y :=
⟨r.numeric_imp, r.symm.numeric_imp⟩

theorem lf_asymm {x y : pgame} (ox : numeric x) (oy : numeric y) : x ⧏ y → ¬ y ⧏ x :=
begin
  refine numeric_rec (λ xl xr xL xR hx oxl oxr IHxl IHxr, _) x ox y oy,
  refine numeric_rec (λ yl yr yL yR hy oyl oyr IHyl IHyr, _),
  rw [mk_lf_mk, mk_lf_mk], rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩),
  { exact IHxl _ _ (oyl _) (h₁.move_left_lf _) (h₂.move_left_lf _) },
  { exact (le_trans h₂ h₁).not_gf (lf_of_lt (hy _ _)) },
  { exact (le_trans h₁ h₂).not_gf (lf_of_lt (hx _ _)) },
  { exact IHxr _ _ (oyr _) (h₁.lf_move_right _) (h₂.lf_move_right _) },
end

theorem le_of_lf {x y : pgame} (h : x ⧏ y) (ox : numeric x) (oy : numeric y) : x ≤ y :=
not_lf.1 (lf_asymm ox oy h)

alias le_of_lf ← lf.le

theorem lt_of_lf {x y : pgame} (h : x ⧏ y) (ox : numeric x) (oy : numeric y) : x < y :=
(lt_or_fuzzy_of_lf h).resolve_right (not_fuzzy_of_le (h.le ox oy))

alias lt_of_lf ← lf.lt

theorem lf_iff_lt {x y : pgame} (ox : numeric x) (oy : numeric y) : x ⧏ y ↔ x < y :=
⟨λ h, h.lt ox oy, lf_of_lt⟩

/-- Definition of `x ≤ y` on numeric pre-games, in terms of `<` -/
theorem le_iff_forall_lt {x y : pgame} (ox : x.numeric) (oy : y.numeric) :
  x ≤ y ↔ (∀ i, x.move_left i < y) ∧ ∀ j, x < y.move_right j :=
begin
  refine le_iff_forall_lf.trans (and_congr _ _);
  refine forall_congr (λ i, lf_iff_lt _ _);
  apply_rules [numeric.move_left, numeric.move_right]
end

/-- Definition of `x < y` on numeric pre-games, in terms of `≤` -/
theorem lt_iff_exists_le {x y : pgame} (ox : x.numeric) (oy : y.numeric) :
  x < y ↔ (∃ i, x ≤ y.move_left i) ∨ ∃ j, x.move_right j ≤ y :=
by rw [←lf_iff_lt ox oy, lf_iff_exists_le]

theorem lt_of_exists_le {x y : pgame} (ox : x.numeric) (oy : y.numeric) :
  ((∃ i, x ≤ y.move_left i) ∨ ∃ j, x.move_right j ≤ y) → x < y :=
(lt_iff_exists_le ox oy).2

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
numeric.mk is_empty_elim is_empty_elim is_empty_elim

theorem numeric_of_is_empty_left_moves (x : pgame) [is_empty x.left_moves] :
  (∀ j, numeric (x.move_right j)) → numeric x :=
numeric.mk is_empty_elim is_empty_elim

theorem numeric_of_is_empty_right_moves (x : pgame) [is_empty x.right_moves]
  (H : ∀ i, numeric (x.move_left i)) : numeric x :=
numeric.mk (λ _, is_empty_elim) H is_empty_elim

theorem numeric_zero : numeric 0 := numeric_of_is_empty 0
theorem numeric_one : numeric 1 := numeric_of_is_empty_right_moves 1 $ λ _, numeric_zero

theorem numeric.neg : Π {x : pgame} (o : numeric x), numeric (-x)
| ⟨l, r, L, R⟩ o := ⟨λ j i, neg_lt_neg_iff.2 (o.1 i j), λ j, (o.2.2 j).neg, λ i, (o.2.1 i).neg⟩

namespace numeric

theorem move_left_lt {x : pgame} (o : numeric x) (i) : x.move_left i < x :=
(move_left_lf i).lt (o.move_left i) o
theorem move_left_le {x : pgame} (o : numeric x) (i) : x.move_left i ≤ x :=
(o.move_left_lt i).le

theorem lt_move_right {x : pgame} (o : numeric x) (j) : x < x.move_right j :=
(lf_move_right j).lt o (o.move_right j)
theorem le_move_right {x : pgame} (o : numeric x) (j) : x ≤ x.move_right j :=
(o.lt_move_right j).le

theorem add : Π {x y : pgame} (ox : numeric x) (oy : numeric y), numeric (x + y)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ox oy :=
⟨begin
   rintros (ix|iy) (jx|jy),
   { exact add_lt_add_right (ox.1 ix jx) _ },
   { exact (add_lf_add_of_lf_of_le (lf_mk _ _ ix) (oy.le_move_right jy)).lt
     ((ox.move_left ix).add oy) (ox.add (oy.move_right jy)) },
   { exact (add_lf_add_of_lf_of_le (mk_lf _ _ jx) (oy.move_left_le iy)).lt
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

lemma sub {x y : pgame} (ox : numeric x) (oy : numeric y) : numeric (x - y) := ox.add oy.neg

end numeric

/-- Pre-games defined by natural numbers are numeric. -/
theorem numeric_nat : Π (n : ℕ), numeric n
| 0 := numeric_zero
| (n + 1) := (numeric_nat n).add numeric_one

/-- Ordinal games are numeric. -/
theorem numeric_to_pgame (o : ordinal) : o.to_pgame.numeric :=
begin
  induction o using ordinal.induction with o IH,
  apply numeric_of_is_empty_right_moves,
  simpa using λ i, IH _ (ordinal.to_left_moves_to_pgame_symm_lt i)
end

end pgame

open pgame

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def surreal := quotient (subtype.setoid numeric)

namespace surreal

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : pgame) (h : x.numeric) : surreal := ⟦⟨x, h⟩⟧

instance : has_zero surreal := ⟨mk 0 numeric_zero⟩
instance : has_one surreal := ⟨mk 1 numeric_one⟩
instance : inhabited surreal := ⟨0⟩

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, numeric x → α)
  (H : ∀ {x y} (hx : numeric x) (hy : numeric y), x.equiv y → f x hx = f y hy) : surreal → α :=
quotient.lift (λ x : {x // numeric x}, f x.1 x.2) (λ x y, H x.2 y.2)

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
  (λ _ _ _ _ a, quotient.sound (neg_equiv_neg_iff.2 a))⟩

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
  lt_iff_le_not_le  := by { rintros ⟨_, ox⟩ ⟨_, oy⟩, apply @lt_iff_le_not_le pgame },
  le_antisymm       := by { rintros ⟨_⟩ ⟨_⟩ h₁ h₂, exact quotient.sound ⟨h₁, h₂⟩ },
  add_le_add_left   := by { rintros ⟨_⟩ ⟨_⟩ hx ⟨_⟩, exact @add_le_add_left pgame _ _ _ _ _ hx _ } }

noncomputable instance : linear_ordered_add_comm_group surreal :=
{ le_total := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; classical; exact
    or_iff_not_imp_left.2 (λ h, (pgame.not_le.1 h).le oy ox),
  decidable_le := classical.dec_rel _,
  ..surreal.ordered_add_comm_group }

instance : add_monoid_with_one surreal := add_monoid_with_one.unary

/-- Casts a `surreal` number into a `game`. -/
def to_game : surreal →+o game :=
{ to_fun := lift (λ x _, ⟦x⟧) (λ x y ox oy, quot.sound),
  map_zero' := rfl,
  map_add' := by { rintros ⟨_, _⟩ ⟨_, _⟩, refl },
  monotone' := by { rintros ⟨_, _⟩ ⟨_, _⟩, exact id } }

theorem zero_to_game : to_game 0 = 0 := rfl
@[simp] theorem one_to_game : to_game 1 = 1 := rfl
@[simp] theorem nat_to_game : ∀ n : ℕ, to_game n = n := map_nat_cast' _ one_to_game

end surreal

open surreal

namespace ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def to_surreal : ordinal ↪o surreal :=
{ to_fun := λ o, mk _ (numeric_to_pgame o),
  inj' := λ a b h, to_pgame_equiv_iff.1 (quotient.exact h),
  map_rel_iff' := @to_pgame_le_iff }

end ordinal
