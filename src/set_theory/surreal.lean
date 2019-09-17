/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import set_theory.pgame

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `numeric` if all the Left options are strictly smaller than all the Right options,
and all those options are themselves numeric. In terms of combinatorial games, the
numeric games have "frozen"; you can only make your position worse by playing, and Left is some
definite "number" of moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else besides!)
but we do not yet have a complete development.

## Order properties
Surreal numbers inherit the relations `≤` and `<` from games, and these relations
satisfy the axioms of a partial order (recall that `x < y ↔ x ≤ y ∧ ¬ y ≤ x` did not hold for games).

## Algebraic operations
At this point, we have defined addition and negation (from pregames), and shown that surreals
form an additive semigroup. It would be very little work to finish showing that the surreals form
an ordered commutative group.

We define the operations of multiplication and inverse on surreals, but do not yet establish any of the
necessary properties to show the surreals form an ordered field.

## Embeddings
It would be nice projects to define the group homomorphism `surreal → game`, and also
`ℤ → surreal`, and then the homomorphic inclusion of the dyadic rationals into surreals, and finally
via dyadic Dedekind cuts the homomorphic inclusion of the reals into the surreals.

One can also map all the cardinals into the surreals!

## References
* [Conway, *On numbers and games*][conway2001]
-/

universes u

namespace pgame

/- Multiplicative operations can be defined at the level of pre-games, but as
they are only useful on surreal numbers, we define them here. -/

/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
  `{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
def mul (x y : pgame) : pgame :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl × yl ⊕ xr × yr, xl × yr ⊕ xr × yl, _, _⟩; rintro (⟨i, j⟩ | ⟨i, j⟩),
  { exact IHxl i y + IHyl j - IHxl i (yL j) },
  { exact IHxr i y + IHyr j - IHxr i (yR j) },
  { exact IHxl i y + IHyr j - IHxl i (yR j) },
  { exact IHxr i y + IHyl j - IHxr i (yL j) }
end

instance : has_mul pgame := ⟨mul⟩

/-- Because the two halves of the definition of inv produce more elements
  of each side, we have to define the two families inductively.
  This is the indexing set for the function, and `inv_val` is the function part. -/
inductive inv_ty (l r : Type u) : bool → Type u
| zero {} : inv_ty ff
| left₁ : r → inv_ty ff → inv_ty ff
| left₂ : l → inv_ty tt → inv_ty ff
| right₁ : l → inv_ty ff → inv_ty tt
| right₂ : r → inv_ty tt → inv_ty tt

/-- Because the two halves of the definition of inv produce more elements
  of each side, we have to define the two families inductively.
  This is the function part, defined by recursion on `inv_ty`. -/
def inv_val {l r} (L : l → pgame) (R : r → pgame)
  (IHl : l → pgame) (IHr : r → pgame) : ∀ {b}, inv_ty l r b → pgame
| _ inv_ty.zero := 0
| _ (inv_ty.left₁ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i
| _ (inv_ty.left₂ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₁ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₂ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i

/-- The inverse of a positive surreal number `x = {L | R}` is
  given by `x⁻¹ = {0,
    (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
    (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
  Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
  definition, the sets and elements are inductively generated. -/
def inv' : pgame → pgame
| ⟨l, r, L, R⟩ :=
  let l' := {i // 0 < L i},
      L' : l' → pgame := λ i, L i.1,
      IHl' : l' → pgame := λ i, inv' (L i.1),
      IHr := λ i, inv' (R i) in
  ⟨inv_ty l' r ff, inv_ty l' r tt,
    inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩

/-- The inverse of a surreal number in terms of the inverse on
  positive surreals. -/
noncomputable def inv (x : pgame) : pgame :=
by classical; exact
if x = 0 then 0 else if 0 < x then inv' x else inv' (-x)

noncomputable instance : has_inv pgame := ⟨inv⟩
noncomputable instance : has_div pgame := ⟨λ x y, x * y⁻¹⟩

/-- A pre-game is numeric if
  everything in the L set is less than everything in the R set,
  and all the elements of L and R are also numeric. -/
def numeric : pgame → Prop
| ⟨l, r, L, R⟩ :=
  (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ (∀ i, numeric (R i))

def numeric.move_left {x : pgame} (o : numeric x) (i : x.left_moves) : numeric (x.move_left i) :=
begin
  cases x with xl xr xL xR,
  exact o.2.1 i,
end
def numeric.move_right {x : pgame} (o : numeric x) (j : x.right_moves) : numeric (x.move_right j) :=
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
theorem lt_iff_le_not_le {x y : pgame} (ox : numeric x) (oy : numeric y) : x < y ↔ x ≤ y ∧ ¬ y ≤ x :=
⟨λ h, ⟨le_of_lt ox oy h, not_le.2 h⟩, λ h, not_le.1 h.2⟩

theorem numeric_zero : numeric 0 :=
⟨by rintros ⟨⟩ ⟨⟩, ⟨by rintros ⟨⟩, by rintros ⟨⟩⟩⟩
theorem numeric_one : numeric 1 :=
⟨by rintros ⟨⟩ ⟨⟩, ⟨λ x, numeric_zero, by rintros ⟨⟩⟩⟩

theorem numeric_neg : Π {x : pgame} (o : numeric x), numeric (-x)
| ⟨l, r, L, R⟩ o :=
⟨λ j i, lt_iff_neg_gt.1 (o.1 i j),
  ⟨λ j, numeric_neg (o.2.2 j), λ i, numeric_neg (o.2.1 i)⟩⟩

theorem numeric.move_left_lt {x : pgame.{u}} (o : numeric x) (i : x.left_moves) :
  x.move_left i < x :=
begin
  rw lt_def_le,
  left,
  use i,
end

theorem numeric.move_left_le {x : pgame} (o : numeric x) (i : x.left_moves) :
  x.move_left i ≤ x :=
le_of_lt (o.move_left i) o (o.move_left_lt i)

theorem numeric.lt_move_right {x : pgame} (o : numeric x) (j : x.right_moves) :
  x < x.move_right j :=
begin
  rw lt_def_le,
  right,
  use j,
end

theorem numeric.le_move_right {x : pgame} (o : numeric x) (j : x.right_moves) :
  x ≤ x.move_right j :=
le_of_lt o (o.move_right j) (o.lt_move_right j)

theorem add_lt_add
  {w x y z : pgame.{u}} (ow : numeric w) (ox : numeric x) (oy : numeric y) (oz : numeric z)
  (hwx : w < x) (hyz : y < z) : w + y < x + z :=
begin
  rw lt_def_le at *,
  rcases hwx with ⟨ix, hix⟩|⟨jw, hjw⟩;
  rcases hyz with ⟨iz, hiz⟩|⟨jy, hjy⟩,
  { left,
    use (left_moves_add x z).symm (sum.inl ix),
    simp only [add_move_left_inl],
    calc w + y ≤ move_left x ix + y : add_le_add_right hix
            ... ≤ move_left x ix + move_left z iz : add_le_add_left hiz
            ... ≤ move_left x ix + z : add_le_add_left (oz.move_left_le iz) },
  { left,
    use (left_moves_add x z).symm (sum.inl ix),
    simp only [add_move_left_inl],
    calc w + y ≤ move_left x ix + y : add_le_add_right hix
            ... ≤ move_left x ix + move_right y jy : add_le_add_left (oy.le_move_right jy)
            ... ≤ move_left x ix + z : add_le_add_left hjy },
  { right,
    use (right_moves_add w y).symm (sum.inl jw),
    simp only [add_move_right_inl],
    calc move_right w jw + y ≤ x + y : add_le_add_right hjw
            ... ≤ x + move_left z iz : add_le_add_left hiz
            ... ≤ x + z : add_le_add_left (oz.move_left_le iz), },
  { right,
    use (right_moves_add w y).symm (sum.inl jw),
    simp only [add_move_right_inl],
    calc move_right w jw + y ≤ x + y : add_le_add_right hjw
            ... ≤ x + move_right y jy : add_le_add_left (oy.le_move_right jy)
            ... ≤ x + z : add_le_add_left hjy, },
end

theorem numeric_add : Π {x y : pgame} (ox : numeric x) (oy : numeric y), numeric (x + y)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ox oy :=
⟨begin
   rintros (ix|iy) (jx|jy),
   { show xL ix + ⟨yl, yr, yL, yR⟩ < xR jx + ⟨yl, yr, yL, yR⟩,
     exact add_lt_add_right (ox.1 ix jx), },
   { show xL ix + ⟨yl, yr, yL, yR⟩ < ⟨xl, xr, xL, xR⟩ + yR jy,
     apply add_lt_add (ox.move_left ix) ox oy (oy.move_right jy),
     apply ox.move_left_lt,
     apply oy.lt_move_right },
   { --  show ⟨xl, xr, xL, xR⟩ + yL iy < xR jx + ⟨yl, yr, yL, yR⟩, -- fails?
     apply add_lt_add ox (ox.move_right jx) (oy.move_left iy) oy,
     apply ox.lt_move_right,
     apply oy.move_left_lt, },
   { --  show ⟨xl, xr, xL, xR⟩ + yL iy < ⟨xl, xr, xL, xR⟩ + yR jy, -- fails?
     exact @add_lt_add_left ⟨xl, xr, xL, xR⟩ _ _ (oy.1 iy jy), }
 end,
 begin
   split,
   { rintros (ix|iy),
     { apply numeric_add (ox.move_left ix) oy, },
     { apply numeric_add ox (oy.move_left iy), }, },
   { rintros (jx|jy),
     { apply numeric_add (ox.move_right jx) oy, },
     { apply numeric_add ox (oy.move_right jy), }, },
 end⟩
using_well_founded { dec_tac := pgame_wf_tac }

-- TODO prove
-- theorem numeric_nat (n : ℕ) : numeric n := sorry
-- theorem numeric_omega : numeric omega := sorry

end pgame

/-- The equivalence on numeric pre-games. -/
def surreal.equiv (x y : {x // pgame.numeric x}) : Prop := x.1.equiv y.1
local infix ` ≈ ` := surreal.equiv

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

instance : preorder surreal :=
{ le := le,
  lt := lt,
  le_refl := by rintro ⟨⟨x, ox⟩⟩; exact le_refl _,
  le_trans := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ ⟨⟨z, oz⟩⟩; exact le_trans,
  lt_iff_le_not_le := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; exact lt_iff_le_not_le ox oy }

instance : partial_order surreal :=
{ le_antisymm := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ h₁ h₂; exact quot.sound ⟨h₁, h₂⟩,
  ..surreal.preorder }

instance : linear_order surreal :=
{ le_total := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; classical; exact
    or_iff_not_imp_left.2 (λ h, le_of_lt oy ox (pgame.not_le.1 h)),
  ..surreal.partial_order }

def add : surreal → surreal → surreal :=
surreal.lift₂
  (λ (x y : pgame) (ox) (oy), ⟦⟨x + y, numeric_add ox oy⟩⟧)
  (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, quot.sound (pgame.add_congr hx hy))

instance : has_add surreal := ⟨add⟩

theorem add_assoc : ∀ (x y z : surreal), (x + y) + z = x + (y + z) :=
begin
  rintros ⟨x⟩ ⟨y⟩ ⟨z⟩,
  apply quot.sound,
  exact add_assoc_equiv,
end

instance : add_semigroup surreal :=
{ add_assoc := add_assoc,
  ..(by apply_instance : has_add surreal) }

-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO construct the remaining instances:
--   add_monoid, add_group, add_comm_semigroup, add_comm_group, ordered_comm_group,
-- as per the instances for `game`

-- TODO define the inclusion of groups `surreal → game`

-- TODO define the dyadic rationals, and show they map into the surreals via the formula
--   m / 2^n ↦ { (m-1) / 2^n | (m+1) / 2^n }
-- TODO show this is a group homomorphism, and injective

-- TODO map the reals into the surreals, using dyadic Dedekind cuts
-- TODO show this is a group homomorphism, and injective

-- TODO define the field structure on the surreals
-- TODO show the maps from the dyadic rationals and from the reals into the surreals are multiplicative

end surreal
