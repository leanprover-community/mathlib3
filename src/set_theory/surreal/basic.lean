/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import set_theory.game.basic
import set_theory.game.birthday

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties
Surreal numbers inherit the relations `≤` and `<` from games, and these relations satisfy the axioms
of a partial order (recall that `x < y ↔ x ≤ y ∧ ¬ y ≤ x` did not hold for games).

## Algebraic operations
We show that the surreals form a linear ordered commutative group.

One can also map all the ordinals into the surreals!

### Multiplication of surreal numbers
The definition of multiplication for surreal numbers is surprisingly difficult and is currently
missing in the library. A sample proof can be found in Theorem 3.8 in the second reference below.
The difficulty lies in the length of the proof and the number of theorems that need to proven
simultaneously. This will make for a fun and challenging project.

## References
* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
-/

universes u

local infix ` ≈ ` := pgame.equiv

namespace pgame

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def numeric : pgame → Prop
| ⟨l, r, L, R⟩ :=
  (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ (∀ i, numeric (R i))

lemma numeric_def (x : pgame) : numeric x ↔ (∀ i j, x.move_left i < x.move_right j) ∧
  (∀ i, numeric (x.move_left i)) ∧ (∀ i, numeric (x.move_right i)) :=
by { cases x, refl }

lemma numeric.move_left {x : pgame} (o : numeric x) (i : x.left_moves) :
  numeric (x.move_left i) :=
begin
  cases x with xl xr xL xR,
  exact o.2.1 i,
end
lemma numeric.move_right {x : pgame} (o : numeric x) (j : x.right_moves) :
  numeric (x.move_right j) :=
begin
  cases x with xl xr xL xR,
  exact o.2.2 j,
end

@[elab_as_eliminator]
theorem numeric_rec {C : pgame → Prop}
  (H : ∀ l r (L : l → pgame) (R : r → pgame),
    (∀ i j, L i < R j) → (∀ i, numeric (L i)) → (∀ i, numeric (R i)) →
    (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
  ∀ x, numeric x → C x
| ⟨l, r, L, R⟩ ⟨h, hl, hr⟩ :=
  H _ _ _ _ h hl hr (λ i, numeric_rec _ (hl i)) (λ i, numeric_rec _ (hr i))

theorem lt_asymm {x y : pgame} (ox : numeric x) (oy : numeric y) : x < y → ¬ y < x :=
begin
  refine numeric_rec (λ xl xr xL xR hx oxl oxr IHxl IHxr, _) x ox y oy,
  refine numeric_rec (λ yl yr yL yR hy oyl oyr IHyl IHyr, _),
  rw [mk_lt_mk, mk_lt_mk], rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩),
  { exact IHxl _ _ (oyl _) (lt_of_le_mk h₁) (lt_of_le_mk h₂) },
  { exact not_lt.2 (le_trans h₂ h₁) (hy _ _) },
  { exact not_lt.2 (le_trans h₁ h₂) (hx _ _) },
  { exact IHxr _ _ (oyr _) (lt_of_mk_le h₁) (lt_of_mk_le h₂) },
end

theorem le_of_lt {x y : pgame} (ox : numeric x) (oy : numeric y) (h : x < y) : x ≤ y :=
not_lt.1 (lt_asymm ox oy h)

/-- On numeric pre-games, `<` and `≤` satisfy the axioms of a partial order (even though they
don't on all pre-games). -/
theorem lt_iff_le_not_le {x y : pgame} (ox : numeric x) (oy : numeric y) :
  x < y ↔ x ≤ y ∧ ¬ y ≤ x :=
⟨λ h, ⟨le_of_lt ox oy h, not_le.2 h⟩, λ h, not_le.1 h.2⟩

theorem numeric_zero : numeric 0 :=
⟨by rintros ⟨⟩ ⟨⟩, ⟨by rintros ⟨⟩, by rintros ⟨⟩⟩⟩
theorem numeric_one : numeric 1 :=
⟨by rintros ⟨⟩ ⟨⟩, ⟨λ x, numeric_zero, by rintros ⟨⟩⟩⟩

theorem numeric.neg : Π {x : pgame} (o : numeric x), numeric (-x)
| ⟨l, r, L, R⟩ o := ⟨λ j i, lt_iff_neg_gt.1 (o.1 i j), λ j, (o.2.2 j).neg, λ i, (o.2.1 i).neg⟩

/-- For the `<` version, see `pgame.move_left_lt`. -/
theorem numeric.move_left_le {x : pgame} (o : numeric x) (i : x.left_moves) :
  x.move_left i ≤ x :=
le_of_lt (o.move_left i) o (pgame.move_left_lt i)

/-- For the `<` version, see `pgame.lt_move_right`. -/
theorem numeric.le_move_right {x : pgame} (o : numeric x) (j : x.right_moves) :
  x ≤ x.move_right j :=
le_of_lt o (o.move_right j) (pgame.lt_move_right j)

theorem add_lt_add
  {w x y z : pgame.{u}} (oy : numeric y) (oz : numeric z)
  (hwx : w < x) (hyz : y < z) : w + y < x + z :=
begin
  rw lt_def_le at *,
  rcases hwx with ⟨ix, hix⟩|⟨jw, hjw⟩;
  rcases hyz with ⟨iz, hiz⟩|⟨jy, hjy⟩,
  { left,
    use (left_moves_add x z).symm (sum.inl ix),
    simp only [add_move_left_inl],
    calc w + y ≤ move_left x ix + y : add_le_add_right hix _
            ... ≤ move_left x ix + move_left z iz : add_le_add_left hiz _
            ... ≤ move_left x ix + z : add_le_add_left (oz.move_left_le iz) _ },
  { left,
    use (left_moves_add x z).symm (sum.inl ix),
    simp only [add_move_left_inl],
    calc w + y ≤ move_left x ix + y : add_le_add_right hix _
            ... ≤ move_left x ix + move_right y jy : add_le_add_left (oy.le_move_right jy) _
            ... ≤ move_left x ix + z : add_le_add_left hjy _ },
  { right,
    use (right_moves_add w y).symm (sum.inl jw),
    simp only [add_move_right_inl],
    calc move_right w jw + y ≤ x + y : add_le_add_right hjw _
            ... ≤ x + move_left z iz : add_le_add_left hiz _
            ... ≤ x + z : add_le_add_left (oz.move_left_le iz) _ },
  { right,
    use (right_moves_add w y).symm (sum.inl jw),
    simp only [add_move_right_inl],
    calc move_right w jw + y ≤ x + y : add_le_add_right hjw _
            ... ≤ x + move_right y jy : add_le_add_left (oy.le_move_right jy) _
            ... ≤ x + z : add_le_add_left hjy _ },
end

theorem numeric.add : Π {x y : pgame} (ox : numeric x) (oy : numeric y), numeric (x + y)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ox oy :=
⟨begin
   rintros (ix|iy) (jx|jy),
   { show xL ix + ⟨yl, yr, yL, yR⟩ < xR jx + ⟨yl, yr, yL, yR⟩,
     exact add_lt_add_right (ox.1 ix jx) _ },
   { show xL ix + ⟨yl, yr, yL, yR⟩ < ⟨xl, xr, xL, xR⟩ + yR jy,
     exact add_lt_add oy (oy.move_right jy) (pgame.lt_mk ix) (pgame.mk_lt jy), },
   { -- show ⟨xl, xr, xL, xR⟩ + yL iy < xR jx + ⟨yl, yr, yL, yR⟩, -- fails?
     exact add_lt_add (oy.move_left iy) oy (pgame.mk_lt jx) (pgame.lt_mk iy), },
   { -- show ⟨xl, xr, xL, xR⟩ + yL iy < ⟨xl, xr, xL, xR⟩ + yR jy, -- fails?
     exact @add_lt_add_left pgame _ _ _ _ _ (oy.1 iy jy) ⟨xl, xr, xL, xR⟩ }
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

/-- The pre-game omega is numeric. -/
theorem numeric_omega : numeric omega :=
⟨by rintros ⟨⟩ ⟨⟩, λ i, numeric_nat i.down, by rintros ⟨⟩⟩

/-- The pre-game `half` is numeric. -/
theorem numeric_half : numeric half :=
begin
  split,
  { rintros ⟨ ⟩ ⟨ ⟩,
    exact zero_lt_one },
  split; rintro ⟨ ⟩,
  { exact numeric_zero },
  { exact numeric_one }
end

theorem half_add_half_equiv_one : half + half ≈ 1 :=
begin
  split; rw le_def; split,
  { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩),
    { right,
      use (sum.inr punit.star),
      calc ((half + half).move_left (sum.inl punit.star)).move_right (sum.inr punit.star)
          = (half.move_left punit.star + half).move_right (sum.inr punit.star) : by fsplit
      ... = (0 + half).move_right (sum.inr punit.star) : by fsplit
      ... ≈ 1 : zero_add_equiv 1
      ... ≤ 1 : pgame.le_refl 1 },
    { right,
      use (sum.inl punit.star),
      calc ((half + half).move_left (sum.inr punit.star)).move_right (sum.inl punit.star)
          = (half + half.move_left punit.star).move_right (sum.inl punit.star) : by fsplit
      ... = (half + 0).move_right (sum.inl punit.star) : by fsplit
      ... ≈ 1 : add_zero_equiv 1
      ... ≤ 1 : pgame.le_refl 1 } },
  { rintro ⟨ ⟩ },
  { rintro ⟨ ⟩,
    left,
    use (sum.inl punit.star),
    calc 0 ≤ half : le_of_lt numeric_zero numeric_half pgame.zero_lt_half
    ... ≈ 0 + half : (zero_add_equiv half).symm
    ... = (half + half).move_left (sum.inl punit.star) : by fsplit },
  { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩); left,
    { exact ⟨sum.inr punit.star, le_of_le_of_equiv (pgame.le_refl _) (add_zero_equiv _).symm⟩ },
    { exact ⟨sum.inl punit.star, le_of_le_of_equiv (pgame.le_refl _) (zero_add_equiv _).symm⟩ } }
end

end pgame

/-- The equivalence on numeric pre-games. -/
def surreal.equiv (x y : {x // pgame.numeric x}) : Prop := x.1.equiv y.1

instance surreal.setoid : setoid {x // pgame.numeric x} :=
⟨λ x y, x.1.equiv y.1,
 λ x, pgame.equiv_refl _,
 λ x y, pgame.equiv_symm,
 λ x y z, pgame.equiv_trans⟩

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def surreal := quotient surreal.setoid

namespace surreal
open pgame

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : pgame) (h : x.numeric) : surreal := quotient.mk ⟨x, h⟩

instance : has_zero surreal :=
{ zero := ⟦⟨0, numeric_zero⟩⟧ }
instance : has_one surreal :=
{ one := ⟦⟨1, numeric_one⟩⟧ }

instance : inhabited surreal := ⟨0⟩

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, numeric x → α)
  (H : ∀ {x y} (hx : numeric x) (hy : numeric y), x.equiv y → f x hx = f y hy) : surreal → α :=
quotient.lift (λ x : {x // numeric x}, f x.1 x.2) (λ x y, H x.2 y.2)

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, numeric x → numeric y → α)
  (H : ∀ {x₁ y₁ x₂ y₂} (ox₁ : numeric x₁) (oy₁ : numeric y₁) (ox₂ : numeric x₂) (oy₂ : numeric y₂),
    x₁.equiv x₂ → y₁.equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) : surreal → surreal → α :=
lift (λ x ox, lift (λ y oy, f x y ox oy) (λ y₁ y₂ oy₁ oy₂ h, H _ _ _ _ (equiv_refl _) h))
  (λ x₁ x₂ ox₁ ox₂ h, funext $ quotient.ind $ by exact λ ⟨y, oy⟩, H _ _ _ _ h (equiv_refl _))

/-- The relation `x ≤ y` on surreals. -/
def le : surreal → surreal → Prop :=
lift₂ (λ x y _ _, x ≤ y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext (le_congr hx hy))

/-- The relation `x < y` on surreals. -/
def lt : surreal → surreal → Prop :=
lift₂ (λ x y _ _, x < y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext (lt_congr hx hy))

theorem not_le : ∀ {x y : surreal}, ¬ le x y ↔ lt y x :=
by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; exact not_le

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add : surreal → surreal → surreal :=
surreal.lift₂
  (λ (x y : pgame) (ox) (oy), ⟦⟨x + y, ox.add oy⟩⟧)
  (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, quotient.sound (pgame.add_congr hx hy))

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
def neg : surreal → surreal :=
surreal.lift
  (λ x ox, ⟦⟨-x, ox.neg⟩⟧)
  (λ _ _ _ _ a, quotient.sound (pgame.neg_congr a))

instance : has_le surreal   := ⟨le⟩
instance : has_lt surreal   := ⟨lt⟩
instance : has_add surreal  := ⟨add⟩
instance : has_neg surreal  := ⟨neg⟩

instance : ordered_add_comm_group surreal :=
{ add               := (+),
  add_assoc         := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, exact quotient.sound add_assoc_equiv },
  zero              := 0,
  zero_add          := by { rintros ⟨_⟩, exact quotient.sound (pgame.zero_add_equiv a) },
  add_zero          := by { rintros ⟨_⟩, exact quotient.sound (pgame.add_zero_equiv a) },
  neg               := has_neg.neg,
  add_left_neg      := by { rintros ⟨_⟩, exact quotient.sound (pgame.add_left_neg_equiv a) },
  add_comm          := by { rintros ⟨_⟩ ⟨_⟩, exact quotient.sound pgame.add_comm_equiv },
  le                := (≤),
  lt                := (<),
  le_refl           := by { rintros ⟨_⟩, refl },
  le_trans          := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, exact pgame.le_trans },
  lt_iff_le_not_le  := by { rintros ⟨_, ox⟩ ⟨_, oy⟩, exact pgame.lt_iff_le_not_le ox oy },
  le_antisymm       := by { rintros ⟨_⟩ ⟨_⟩ h₁ h₂, exact quotient.sound ⟨h₁, h₂⟩ },
  add_le_add_left   := by { rintros ⟨_⟩ ⟨_⟩ hx ⟨_⟩, exact @add_le_add_left pgame _ _ _ _ _ hx _ } }

noncomputable instance : linear_ordered_add_comm_group surreal :=
{ le_total := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; classical; exact
    or_iff_not_imp_left.2 (λ h, le_of_lt oy ox (pgame.not_le.1 h)),
  decidable_le := classical.dec_rel _,
  ..surreal.ordered_add_comm_group }

end surreal

namespace pgame

/-- To prove that surreal multiplication is well-defined, we use a modified argument by Schleicher.
We simultaneously prove two assertions on numeric pre-games:

- `P1 x y` means `x * y` is numeric.
- `P2 x₁ x₂ y` means all of the following hold:
- - If `x₁ ≈ x₂` then `x₁ * y ≈ x₂ * y`,
- - If `x₁ < x₂`, then
- - - For every left move `yL`, `yL * x₂ + y * x₁ < yL * x₁ + y * x₂`,
- - - For every right move `yR`, `y * x₂ + yR * x₁ < y * x₁ + yR * x₂`.

We prove this by defining a well-founded "depth" on `P1` and `P2`, and showing that each statement
follows from statements of lesser depth. This auxiliary type represents either the assertion `P1` on
two games, or the assertion `P2` on three games. -/
inductive mul_args : Type (u+1)
| P1 (x y : pgame.{u}) : mul_args
| P2 (x₁ x₂ y : pgame.{u}) : mul_args

namespace mul_args

/-- The depth function on the type. See the docstring for `mul_args`. -/
noncomputable def depth : mul_args → ordinal ×ₗ ordinal
| (P1 x y) := ((x + y).birthday, 0)
| (P2 x₁ x₂ y) := (max ((x₁ + y).birthday) ((x₂ + y).birthday),
                    (min x₁.birthday x₂.birthday).succ)

/-- This is the statement we wish to prove. -/
def hypothesis : mul_args → Prop
| (P1 x y) := numeric x → numeric y → numeric (x * y)
| (P2 x₁ x₂ y) := numeric x₁ → numeric x₂ → numeric y →
                    (x₁ ≈ x₂ → x₁ * y ≈ x₂ * y) ∧
                    (x₁ < x₂ →
                      (∀ i, y.move_left i * x₂ + y * x₁ < y.move_left i * x₁ + y * x₂) ∧
                      ∀ j, y * x₂ + y.move_right j * x₁ < y * x₁ + y.move_right j * x₂)

instance : has_lt mul_args := ⟨λ x y, x.depth < y.depth⟩

instance : has_well_founded mul_args :=
{ r := (<),
  wf := inv_image.wf _ (prod.lex_wf ordinal.wf ordinal.wf) }

/-- The hypothesis is true for any arguments. -/
theorem result : ∀ x : mul_args, x.hypothesis
| (P1 ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩) := begin
  let x := pgame.mk xl xr xL xR,
  let y := pgame.mk yl yr yL yR,
  intros ox oy,
  rw numeric_def,
  refine ⟨_, _, _⟩,
  { rintro (⟨ix, iy⟩ | ⟨ix, iy⟩) (⟨ix', jy⟩ | ⟨ix', jy⟩),
    {
      simp,
      rcases lt_or_equiv_or_gt (xL ix) (xL ix') with h | h | h,
      {
        have := ((result (P2 _ _ _) (ox.move_left ix) (ox.move_left ix') oy).2 h).1 iy,
        have := ((result (P2 _ _ _) (oy.move_left iy) (oy.move_right jy) ox).2 sorry).1 ix,
      },
      /-cases lt_or_equiv_or_gt (ox₁.move_left ix) (ox₁.move_left ix'),
      {

      },
      change game.lt ⟦_⟧ ⟦_⟧,
      simp,
      abel,-/
      sorry
    }, repeat { sorry } },
  { rintro (⟨ix, iy⟩ | ⟨jx, jy⟩),
    { apply (numeric.add _ _).sub _,
      { exact result (P1 _ _) (ox.move_left ix) oy },
      { exact result (P1 _ _) ox (oy.move_left iy) },
      { exact result (P1 _ _) (ox.move_left ix) (oy.move_left iy) } },
    { apply (numeric.add _ _).sub _,
      { exact result (P1 _ _) (ox.move_right jx) oy },
      { exact result (P1 _ _) ox (oy.move_right jy) },
      { exact result (P1 _ _) (ox.move_right jx) (oy.move_right jy) } } },
  { rintro (⟨ix, jy⟩ | ⟨jx, iy⟩),
    { apply (numeric.add _ _).sub _,
      { exact result (P1 _ _) (ox.move_left ix) oy },
      { exact result (P1 _ _) ox (oy.move_right jy) },
      { exact result (P1 _ _) (ox.move_left ix) (oy.move_right jy) } },
    { apply (numeric.add _ _).sub _,
      { exact result (P1 _ _) (ox.move_right jx) oy },
      { exact result (P1 _ _) ox (oy.move_left iy) },
      { exact result (P1 _ _) (ox.move_right jx) (oy.move_left iy) } } }
end
| (P2 x₁ x₂ y) := begin
  sorry
end
using_well_founded { dec_tac := sorry }

end mul_args

theorem numeric_mul {x y : pgame} : numeric x → numeric y → numeric (x * y) :=
(mul_args.P1 x y).result

theorem mul_congr_left {x₁ x₂ y : pgame} (ox₁ : numeric x₁) (ox₂ : numeric x₂) (oy : numeric y) :
  x₁ ≈ x₂ → x₁ * y ≈ x₂ * y :=
((mul_args.P2 x₁ x₂ y).result ox₁ ox₂ oy).1

theorem mul_congr_right {x y₁ y₂ : pgame} (ox : numeric x) (oy₁ : numeric y₁) (oy₂ : numeric y₂)
  (h : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ :=
pgame.equiv_trans (mul_comm_equiv _ _)
  (pgame.equiv_trans (mul_congr_left oy₁ oy₂ ox h) (mul_comm_equiv _ _))

theorem mul_congr {x₁ x₂ y₁ y₂ : pgame} (ox₁ : numeric x₁) (ox₂ : numeric x₂) (oy₁ : numeric y₁)
  (oy₂ : numeric y₂) (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
pgame.equiv_trans (mul_congr_left ox₁ ox₂ oy₁ hx) (mul_congr_right ox₂ oy₁ oy₂ hy)

end pgame

namespace surreal

/-- Multiplication of surreal numbers is inherited from pre-game multiplication: the product of
`x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
def mul : surreal → surreal → surreal :=
surreal.lift₂
  (λ x y ox oy, ⟦⟨x * y, pgame.numeric_mul ox oy⟩⟧)
  (λ _ _ _ _ ox₁ oy₁ ox₂ oy₂ hx hy, quotient.sound (pgame.mul_congr ox₁ ox₂ oy₁ oy₂ hx hy))

instance : has_mul surreal := ⟨mul⟩

end surreal

-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO define the inclusion of groups `surreal → game`
-- TODO define the field structure on the surreals
