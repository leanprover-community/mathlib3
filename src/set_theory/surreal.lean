/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import set_theory.pgame

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
At this point, we have defined addition and negation (from pregames), and shown that surreals form
an additive semigroup. It would be very little work to finish showing that the surreals form an
ordered commutative group.

We define the operations of multiplication and inverse on surreals, but do not yet establish any of
the necessary properties to show the surreals form an ordered field.

## Embeddings
It would be nice projects to define the group homomorphism `surreal → game`, and also `ℤ → surreal`,
and then the homomorphic inclusion of the dyadic rationals into surreals, and finally
via dyadic Dedekind cuts the homomorphic inclusion of the reals into the surreals.

One can also map all the ordinals into the surreals!

## References
* [Conway, *On numbers and games*][conway2001]
-/

universes u

namespace pgame

local infix ` ≈ ` := pgame.equiv

/-! Multiplicative operations can be defined at the level of pre-games, but as
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

/-- If `a` has the same moves as `x`, `b` has the same moves as `y`,
and `c` has the same moves as `z`, then `a + b - c` has the same moves as `x + y - z`.
This lemma is repeatedly used for simplifying multiplication of surreal numbers. -/
def add_sub_relabelling {a b c x y z : pgame}
  (h₁ : a.relabelling x) (h₂ : b.relabelling y) (h₃ : c.relabelling z) :
  (a + b - c).relabelling (x + y - z) :=
(h₁.add_congr h₂).sub_congr h₃

/-- If `a` has the same moves as `x`, `b` has the same moves as `y`,
and `c` has the same moves as `z`, then `a + b - c` has the same moves as `y + x - z`.
This lemma is repeatedly used for simplifying multiplication of surreal numbers. -/
def add_comm_sub_relabelling {a b c x y z : pgame}
  (h₁ : a.relabelling x) (h₂ : b.relabelling y) (h₃ : c.relabelling z) :
  (a + b - c).relabelling (y + x - z) :=
((add_comm_relabelling a b).trans (h₂.add_congr h₁)).sub_congr h₃

/-- `x * y` has exactly the same moves as `y * x`. -/
def mul_comm_relabelling (x y : pgame.{u}) : (x * y).relabelling (y * x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  refine ⟨equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _), _, _, _⟩,
  calc
   (x * y).right_moves
       ≃ xl × yr ⊕ xr × yl : by refl
   ... ≃ xr × yl ⊕ xl × yr : equiv.sum_comm _ _
   ... ≃ yl × xr ⊕ yr × xl : equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _)
   ... ≃ (y * x).right_moves : by refl,
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_comm_sub_relabelling (IHxl i y) (IHyl j) (IHxl i (yL j)) },
    { exact add_comm_sub_relabelling (IHxr i y) (IHyr j) (IHxr i (yR j)) } },
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { exact add_comm_sub_relabelling (IHxr j y) (IHyl i) (IHxr j (yL i)) },
    { exact add_comm_sub_relabelling (IHxl j y) (IHyr i) (IHxl j (yR i)) } }
end

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : pgame) : x * y ≈ y * x :=
(mul_comm_relabelling x y).equiv

/-- `x * 0` has exactly the same moves as `0`. -/
def mul_zero_relabelling : Π (x : pgame), relabelling (x * 0) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨_,⟨⟩⟩|⟨_,⟨⟩⟩),
 by fsplit; rintro (⟨_,⟨⟩⟩|⟨_,⟨⟩⟩),
 by rintro (⟨_,⟨⟩⟩|⟨_,⟨⟩⟩),
 by rintro ⟨⟩⟩

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : pgame) : x * 0 ≈ 0 :=
(mul_zero_relabelling x).equiv

/-- `0 * x` has exactly the same moves as `0`. -/
def zero_mul_relabelling : Π (x : pgame), relabelling (0 * x) 0
| (mk xl xr xL xR) :=
⟨by fsplit; rintro (⟨⟨⟩,_⟩|⟨⟨⟩,_⟩),
 by fsplit; rintro (⟨⟨⟩,_⟩|⟨⟨⟩,_⟩),
 by rintro (⟨⟨⟩,_⟩|⟨⟨⟩,_⟩),
 by rintro ⟨⟩⟩

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : pgame) : 0 * x ≈ 0 :=
(zero_mul_relabelling x).equiv

lemma left_distrib_equiv_aux {a b c d e : pgame} : (a + b) + (c + d) - (e + b) ≈ a + c - e + d :=
begin
  have h₁ : b - (b + e) ≈ -e, from
    calc b - (b + e) ≈ b + (-b + -e) : add_congr (equiv_refl _) (neg_add_relabelling _ _).equiv
                 ... ≈ b - b + -e    : add_assoc_equiv.symm
                 ... ≈ 0 + -e        : add_congr add_right_neg_equiv (equiv_refl _)
                 ... ≈ -e            : zero_add_equiv _,
  calc
    (a + b) + (c + d) - (e + b)
        ≈ a + (b + (c + d)) - (e + b)
        : sub_congr add_assoc_equiv (equiv_refl _)
    ... ≈ a + ((c + d) + b) - (e + b)
        : sub_congr (add_congr (equiv_refl _) add_comm_equiv) (equiv_refl _)
    ... ≈ (a + (c + d)) + b - (e + b)
        : sub_congr add_assoc_equiv.symm (equiv_refl _)
    ... ≈ (a + (c + d)) + (b - (e + b))
        : add_assoc_equiv
    ... ≈ (a + (c + d)) + (b - (b + e))
        : add_congr (equiv_refl _) (sub_congr (equiv_refl _) add_comm_equiv)
    ... ≈ (a + (c + d)) + - e
        : add_congr (equiv_refl _) h₁
    ... ≈ a + ((c + d) + - e)
        : add_assoc_equiv
    ... ≈ a + (c + (d + - e))
        : add_congr (equiv_refl _) add_assoc_equiv
    ... ≈ a + (c + (-e + d))
        : add_congr (equiv_refl _) (add_congr (equiv_refl _) add_comm_equiv)
    ... ≈ (a + c) + (-e + d)
        : add_assoc_equiv.symm
    ... ≈ a + c - e + d
        : add_assoc_equiv.symm
end

lemma left_distrib_equiv_aux' {a b c d e : pgame} : (b + a) + (d + c) - (b + e) ≈ d + (a + c - e) :=
calc (b + a) + (d + c) - (b + e)
      ≈ (a + b) + (c + d) - (e + b)
      : by {refine (add_sub_relabelling _ _ _).equiv, repeat {apply add_comm_relabelling} }
  ... ≈ a + c - e + d     : left_distrib_equiv_aux
  ... ≈ d + (a + c - e)   : (add_comm_relabelling _ _).equiv

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
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xL i * y + x * yL j - xL i * yL j + x * z : left_distrib_equiv_aux },
    { calc
        xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)
            ≈ (xL i * y + xL i * z) + (x * y + x * zL k) - (xL i * y + xL i * zL k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈  x * y + (xL i * z + x * zL k - xL i * zL k) : left_distrib_equiv_aux' },
    { calc
        xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)
            ≈  (xR i * y + xR i * z) + (x * yR j + x * z) - (xR i * yR j + xR i * z)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xR i * y + x * yR j - xR i * yR j + x * z : left_distrib_equiv_aux },
    { calc
        xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)
            ≈ (xR i * y + xR i * z) + (x * y + x * zR k) - (xR i * y + xR i * zR k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ x * y + (xR i * z + x * zR k - xR i * zR k) : left_distrib_equiv_aux' } },
  { rintros ((⟨i,j⟩|⟨i,j⟩)|(⟨i,k⟩|⟨i,k⟩)),
    { calc
        xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)
            ≈ (xL i * y + xL i * z) + (x * yR j + x * z) - (xL i * yR j + xL i * z)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xL i * y + x * yR j - xL i * yR j + x * z : left_distrib_equiv_aux },
    { calc
        xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)
            ≈ (xR i * y + xR i * z) + (x * yL j + x * z) - (xR i * yL j + xR i * z)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈ xR i * y + x * yL j - xR i * yL j + x * z : left_distrib_equiv_aux },
    { calc
        xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)
            ≈ (xL i * y + xL i * z) + (x * y + x * zR k) - (xL i * y + xL i * zR k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
        ... ≈  x * y + (xL i * z + x * zR k - xL i * zR k) : left_distrib_equiv_aux' },
    { calc
        xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)
            ≈ (xR i * y + xR i * z) + (x * y + x * zL k) - (xR i * y + xR i * zL k)
            : by { refine add_congr (add_congr _ _) (neg_congr _); apply left_distrib_equiv }
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

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def numeric : pgame → Prop
| ⟨l, r, L, R⟩ :=
  (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ (∀ i, numeric (R i))

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

/-- Pre-games defined by natural numbers are numeric. -/
theorem numeric_nat : Π (n : ℕ), numeric n
| 0 := numeric_zero
| (n + 1) := numeric_add (numeric_nat n) numeric_one

/-- The pre-game omega is numeric. -/
theorem numeric_omega : numeric omega :=
⟨by rintros ⟨⟩ ⟨⟩, λ i, numeric_nat i.down, by rintros ⟨⟩⟩

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
  (λ (x y : pgame) (ox) (oy), ⟦⟨x + y, numeric_add ox oy⟩⟧)
  (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, quotient.sound (pgame.add_congr hx hy))

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
def neg : surreal → surreal :=
surreal.lift
  (λ x ox, ⟦⟨-x, pgame.numeric_neg ox⟩⟧)
  (λ _ _ _ _ a, quotient.sound (pgame.neg_congr a))

instance : has_le surreal   := ⟨le⟩
instance : has_lt surreal   := ⟨lt⟩
instance : has_add surreal  := ⟨add⟩
instance : has_neg surreal  := ⟨neg⟩

instance : ordered_add_comm_group surreal :=
{ add               := (+),
  add_assoc         := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, exact quotient.sound add_assoc_equiv },
  zero              := 0,
  zero_add          := by { rintros ⟨_⟩, exact quotient.sound (pgame.zero_add_equiv _) },
  add_zero          := by { rintros ⟨_⟩, exact quotient.sound (pgame.add_zero_equiv _) },
  neg               := has_neg.neg,
  add_left_neg      := by { rintros ⟨_⟩, exact quotient.sound pgame.add_left_neg_equiv },
  add_comm          := by { rintros ⟨_⟩ ⟨_⟩, exact quotient.sound pgame.add_comm_equiv },
  le                := (≤),
  lt                := (<),
  le_refl           := by { rintros ⟨_⟩, refl },
  le_trans          := by { rintros ⟨_⟩ ⟨_⟩ ⟨_⟩, exact pgame.le_trans },
  lt_iff_le_not_le  := by { rintros ⟨_, ox⟩ ⟨_, oy⟩, exact pgame.lt_iff_le_not_le ox oy },
  le_antisymm       := by { rintros ⟨_⟩ ⟨_⟩ h₁ h₂, exact quotient.sound ⟨h₁, h₂⟩ },
  add_le_add_left   := by { rintros ⟨_⟩ ⟨_⟩ hx ⟨_⟩, exact pgame.add_le_add_left hx } }

noncomputable instance : linear_ordered_add_comm_group surreal :=
{ le_total := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; classical; exact
    or_iff_not_imp_left.2 (λ h, le_of_lt oy ox (pgame.not_le.1 h)),
  decidable_le := classical.dec_rel _,
  ..surreal.ordered_add_comm_group }

-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO define the inclusion of groups `surreal → game`

-- TODO define the dyadic rationals, and show they map into the surreals via the formula
--   m / 2^n ↦ { (m-1) / 2^n | (m+1) / 2^n }
-- TODO show this is a group homomorphism, and injective

-- TODO map the reals into the surreals, using dyadic Dedekind cuts
-- TODO show this is a group homomorphism, and injective

-- TODO define the field structure on the surreals
-- TODO show the maps from the dyadic rationals and from the reals
-- into the surreals are multiplicative

end surreal
