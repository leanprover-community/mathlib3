/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import set_theory.pgame
import tactic.abel

/-!
# Combinatorial games.

In this file we define the quotient of pre-games by the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤
p`, and construct an instance `add_comm_group game`, as well as an instance `partial_order game`
(although note carefully the warning that the `<` field in this instance is not the usual relation
on combinatorial games).

## Multiplication on pgames

We define the operations of multiplication and inverse on pgames, and prove a few basic theorems
about them. Even though multiplication is not well-defined on games, the abelian group structure on
games allows us to simplify the proofs for pgames.
-/

universes u

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
abbreviation game := quotient pgame.setoid

open pgame

namespace game

/-- The relation `x ≤ y` on games. -/
def le : game → game → Prop :=
quotient.lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy))

instance : has_le game :=
{ le := le }

-- We do not add @[refl] and @[trans] instances because of conflict with pgame.le_refl and
-- pgame.le_trans in calc mode proofs.
theorem le_refl : ∀ x : game, x ≤ x :=
by { rintro ⟨x⟩, apply pgame.le_refl }
theorem le_trans : ∀ x y z : game, x ≤ y → y ≤ z → x ≤ z :=
by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, apply pgame.le_trans }
theorem le_antisymm : ∀ x y : game, x ≤ y → y ≤ x → x = y :=
by { rintro ⟨x⟩ ⟨y⟩ h₁ h₂, apply quot.sound, exact ⟨h₁, h₂⟩ }

/-- The relation `x < y` on games. -/
-- We don't yet make this into an instance, because it will conflict with the (incorrect) notion
-- of `<` provided by `partial_order` later.
def lt : game → game → Prop :=
quotient.lift₂ (λ x y, x < y) (λ x₁ y₁ x₂ y₂ hx hy, propext (lt_congr hx hy))

theorem not_le : ∀ {x y : game}, ¬ (x ≤ y) ↔ (lt y x) :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_le }

instance : has_zero game := ⟨⟦0⟧⟩
instance : inhabited game := ⟨0⟩
instance : has_one game := ⟨⟦1⟧⟩

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : game → game :=
quot.lift (λ x, ⟦-x⟧) (λ x y h, quot.sound (@neg_congr x y h))

instance : has_neg game :=
{ neg := neg }

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add : game → game → game :=
quotient.lift₂ (λ x y : pgame, ⟦x + y⟧) (λ x₁ y₁ x₂ y₂ hx hy, quot.sound (pgame.add_congr hx hy))

instance : has_add game := ⟨add⟩

theorem add_assoc : ∀ (x y z : game), (x + y) + z = x + (y + z) :=
begin
  rintros ⟨x⟩ ⟨y⟩ ⟨z⟩,
  apply quot.sound,
  exact add_assoc_equiv
end

instance : add_semigroup game.{u} :=
{ add_assoc := add_assoc,
  ..game.has_add }

theorem add_zero : ∀ (x : game), x + 0 = x :=
begin
  rintro ⟨x⟩,
  apply quot.sound,
  apply add_zero_equiv
end
theorem zero_add : ∀ (x : game), 0 + x = x :=
begin
  rintro ⟨x⟩,
  apply quot.sound,
  apply zero_add_equiv
end

instance : add_monoid game :=
{ add_zero := add_zero,
  zero_add := zero_add,
  ..game.has_zero,
  ..game.add_semigroup }

theorem add_left_neg : ∀ (x : game), (-x) + x = 0 :=
begin
  rintro ⟨x⟩,
  apply quot.sound,
  apply add_left_neg_equiv
end

instance : add_group game :=
{ add_left_neg := add_left_neg,
  ..game.has_neg,
  ..game.add_monoid }

theorem add_comm : ∀ (x y : game), x + y = y + x :=
begin
  rintros ⟨x⟩ ⟨y⟩,
  apply quot.sound,
  exact add_comm_equiv
end

instance : add_comm_semigroup game :=
{ add_comm := add_comm,
  ..game.add_semigroup }

instance : add_comm_group game :=
{ ..game.add_comm_semigroup,
  ..game.add_group }

theorem add_le_add_left : ∀ (a b : game), a ≤ b → ∀ (c : game), c + a ≤ c + b :=
begin rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩, apply pgame.add_le_add_left h, end

@[simp] lemma quot_neg (a : pgame) : ⟦-a⟧ = -⟦a⟧ := rfl
@[simp] lemma quot_add (a b : pgame) : ⟦a + b⟧ = ⟦a⟧ + ⟦b⟧ := rfl
@[simp] lemma quot_sub (a b : pgame) : ⟦a - b⟧ = ⟦a⟧ - ⟦b⟧ := rfl

-- While it is very tempting to define a `partial_order` on games, and prove
-- that games form an `ordered_add_comm_group`, it is a bit dangerous.

-- The relations `≤` and `<` on games do not satisfy
-- `lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`
-- (Consider `a = 0`, `b = star`.)
-- (`lt_iff_le_not_le` is satisfied by surreal numbers, however.)
-- Thus we can not use `<` when defining a `partial_order`.

-- Because of this issue, we define the `partial_order` and `ordered_add_comm_group` instances,
-- but do not actually mark them as instances, for safety.

/-- The `<` operation provided by this partial order is not the usual `<` on games! -/
def game_partial_order : partial_order game :=
{ le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,
  ..game.has_le }

/-- The `<` operation provided by this `ordered_add_comm_group` is not the usual `<` on games! -/
def ordered_add_comm_group_game : ordered_add_comm_group game :=
{ add_le_add_left := add_le_add_left,
  ..game.add_comm_group,
  ..game_partial_order }

end game

namespace pgame

/-! Multiplicative operations can be defined at the level of pre-games,
but to prove their properties we need to use the abelian group structure of games.
Hence we define them here. -/

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

/-- An explicit description of the moves for Left in `x * y`. -/
def left_moves_mul (x y : pgame) : (x * y).left_moves
  ≃ x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves :=
by { cases x, cases y, refl, }

/-- An explicit description of the moves for Right in `x * y`. -/
def right_moves_mul (x y : pgame) : (x * y).right_moves
  ≃ x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves :=
by { cases x, cases y, refl, }

@[simp] lemma mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inl (i, j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xL i * yL j :=
 rfl

@[simp] lemma mul_move_left_inl {x y : pgame} {i j} :
   (x * y).move_left ((left_moves_mul x y).symm (sum.inl (i, j)))
   = x.move_left i * y + x * y.move_left j - x.move_left i * y.move_left j :=
by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i, j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xR i * yR j :=
rfl

@[simp] lemma mul_move_left_inr {x y : pgame} {i j} :
   (x * y).move_left ((left_moves_mul x y).symm (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_right j - x.move_right i * y.move_right j :=
by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i, j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xL i * yR j :=
rfl

@[simp] lemma mul_move_right_inl {x y : pgame} {i j} :
   (x * y).move_right ((right_moves_mul x y).symm (sum.inl (i, j)))
   = x.move_left i * y + x * y.move_right j - x.move_left i * y.move_right j :=
by {cases x, cases y, refl}

@[simp] lemma mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i,j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xR i * yL j :=
rfl

@[simp] lemma mul_move_right_inr {x y : pgame} {i j} :
   (x * y).move_right ((right_moves_mul x y).symm (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j :=
by {cases x, cases y, refl}

/-- `x * y` has exactly the same moves as `y * x`. -/
def mul_comm_relabelling (x y : pgame.{u}) : (x * y).relabelling (y * x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  refine ⟨equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _), _, _, _⟩,
  calc
    xl × yr ⊕ xr × yl
       ≃ xr × yl ⊕ xl × yr : equiv.sum_comm _ _
   ... ≃ yl × xr ⊕ yr × xl : equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _),
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact ((add_comm_relabelling _ _).trans
                ((IHyl j).add_congr (IHxl i y))).sub_congr (IHxl i (yL j)) },
    { exact ((add_comm_relabelling _ _).trans
                ((IHyr j).add_congr (IHxr i y))).sub_congr (IHxr i (yR j)) } },
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact ((add_comm_relabelling _ _).trans
                ((IHyl i).add_congr (IHxr j y))).sub_congr (IHxr j (yL i)) },
    { exact ((add_comm_relabelling _ _).trans
                ((IHyr i).add_congr (IHxl j y))).sub_congr (IHxl j (yR i)) } }
end

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : pgame) : x * y ≈ y * x :=
(mul_comm_relabelling x y).equiv

/-- `x * 0` has exactly the same moves as `0`. -/
def mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨_,⟨⟩⟩ | ⟨_,⟨⟩⟩),
 by fsplit; rintro (⟨_,⟨⟩⟩ | ⟨_,⟨⟩⟩),
 by rintro (⟨_,⟨⟩⟩ | ⟨_,⟨⟩⟩),
 by rintro ⟨⟩⟩

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : pgame) : x * 0 ≈ 0 :=
(mul_zero_relabelling x).equiv

/-- `0 * x` has exactly the same moves as `0`. -/
def zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by fsplit; rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro (⟨⟨⟩,_⟩ | ⟨⟨⟩,_⟩),
 by rintro ⟨⟩⟩

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : pgame) : 0 * x ≈ 0 :=
(zero_mul_relabelling x).equiv

lemma left_distrib_equiv_aux {a b c d e : pgame} : a + b + (c + d) - (e + b) ≈ a + c - e + d :=
by { apply @quotient.exact pgame, simp, abel }

lemma left_distrib_equiv_aux' {a b c d e : pgame} : b + a + (d + c) - (b + e) ≈ d + (a + c - e) :=
by { apply @quotient.exact pgame, simp, abel }

/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem left_distrib_equiv : Π (x y z : pgame), x * (y + z) ≈ x * y + x * z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine equiv_of_mk_equiv _ _ _ _,
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩));
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩); refl },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)); refl } },
  { fsplit,
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩));
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintros (⟨_,(_|_)⟩|⟨_,(_|_)⟩); refl },
    { rintros ((⟨_,_⟩|⟨_,_⟩)|(⟨_,_⟩|⟨_,_⟩)); refl } },
  { rintros (⟨i,(j|k)⟩|⟨i,(j|k)⟩),
    { calc
        xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)
            ≈ (xL i * y + xL i * z) + (x * yL j + x * z) - (xL i * yL j + xL i * z)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈ xL i * y + x * yL j - xL i * yL j + x * z : left_distrib_equiv_aux },
    { calc
        xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)
            ≈ (xL i * y + xL i * z) + (x * y + x * zL k) - (xL i * y + xL i * zL k)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈  x * y + (xL i * z + x * zL k - xL i * zL k) : left_distrib_equiv_aux' },
    { calc
        xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)
            ≈  (xR i * y + xR i * z) + (x * yR j + x * z) - (xR i * yR j + xR i * z)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈ xR i * y + x * yR j - xR i * yR j + x * z : left_distrib_equiv_aux },
    { calc
        xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)
            ≈ (xR i * y + xR i * z) + (x * y + x * zR k) - (xR i * y + xR i * zR k)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈ x * y + (xR i * z + x * zR k - xR i * zR k) : left_distrib_equiv_aux' } },
  { rintros ((⟨i,j⟩|⟨i,j⟩)|(⟨i,k⟩|⟨i,k⟩)),
    { calc
        xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)
            ≈ (xL i * y + xL i * z) + (x * yR j + x * z) - (xL i * yR j + xL i * z)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈ xL i * y + x * yR j - xL i * yR j + x * z : left_distrib_equiv_aux },
    { calc
        xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)
            ≈ (xR i * y + xR i * z) + (x * yL j + x * z) - (xR i * yL j + xR i * z)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈ xR i * y + x * yL j - xR i * yL j + x * z : left_distrib_equiv_aux },
    { calc
        xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)
            ≈ (xL i * y + xL i * z) + (x * y + x * zR k) - (xL i * y + xL i * zR k)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈  x * y + (xL i * z + x * zR k - xL i * zR k) : left_distrib_equiv_aux' },
    { calc
        xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)
            ≈ (xR i * y + xR i * z) + (x * y + x * zL k) - (xR i * y + xR i * zL k)
            : by { refine sub_congr (add_congr _ _) _; apply left_distrib_equiv }
        ... ≈ x * y + (xR i * z + x * zL k - xR i * zL k) : left_distrib_equiv_aux' } }
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : pgame) : (x + y) * z ≈ x * z + y * z :=
calc (x + y) * z ≈ z * (x + y)      : mul_comm_equiv _ _
             ... ≈ z * x + z * y    : left_distrib_equiv _ _ _
             ... ≈ (x * z + y * z)  : add_congr (mul_comm_equiv _ _) (mul_comm_equiv _ _)

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the indexing set for the function, and `inv_val` is the function part. -/
inductive inv_ty (l r : Type u) : bool → Type u
| zero : inv_ty ff
| left₁ : r → inv_ty ff → inv_ty ff
| left₂ : l → inv_ty tt → inv_ty ff
| right₁ : l → inv_ty ff → inv_ty tt
| right₂ : r → inv_ty tt → inv_ty tt

/-- Because the two halves of the definition of `inv` produce more elements
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

/-- The inverse of a surreal number in terms of the inverse on positive surreals. -/
noncomputable def inv (x : pgame) : pgame :=
by classical; exact
if x = 0 then 0 else if 0 < x then inv' x else inv' (-x)

noncomputable instance : has_inv pgame := ⟨inv⟩
noncomputable instance : has_div pgame := ⟨λ x y, x * y⁻¹⟩

end pgame 
