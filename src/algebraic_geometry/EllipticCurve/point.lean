/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.EllipticCurve
import field_theory.galois -- temporary import to enable point notation
import tactic.field_simp

/-!
# The group of rational points on an elliptic curve over a field

Let $E$ be an elliptic curve over a field $F$. A rational point on $E$ is simply a point $[X:Y:Z]$
in the projective plane cubic $Y^2Z + a_1XYZ + a_3YZ^2 = X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3$. This
file defines the type of rational points on $E$ as an inductive, since any such point either lies in
the affine chart $Z \ne 0$ and satisfies the Weierstrass equation obtained by setting $x := X/Z$ and
$y := Y/Z$, or is the unique point at infinity $\mathcal{O} = [0:1:0]$ obtained by setting $Z := 0$.
For a field extension $K$ of $F$, a $K$-rational point is simply a point on $E$ base changed to $K$.

The set of rational points on $E$ forms an abelian group under a chord-and-tangent process.
 * The identity point is $\mathcal{O}$.
 * Given a point $P$, its negation $-P$ is defined to be the unique third point of intersection
    between $E$ and the line joining $\mathcal{O}$ and $P$, which exists by Bézout's theorem.
    Explicitly, if $P = (x, y)$, then $-P := (x, -y - a_1x - a_3)$.
 * Given two points $P$ and $Q$, their addition $P + Q$ is defined to be the negation of the unique
    third point of intersection between $E$ and the line joining $P$ and $Q$, which again exists by
    Bézout's theorem. Explicitly, let $P = (x_1, y_1)$ and $Q = (x_2, y_2)$.
      * If $x_1 = x_2$ and $P = -Q$ then this line is vertical and $P + Q := \mathcal{O}$.
      * If $x_1 = x_2$ and $P \ne -Q$ then this line is the tangent of $E$ at $P = Q$ and has
        gradient $\ell := (3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$.
      * Otherwise $x_1 \ne x_2$ then this line has gradient $\ell := (y_1 - y_2) / (x_1 - x_2)$.
    In the latter two cases, the $x$-coordinate of $P + Q$ is then the unique third solution of the
    equation obtained by substituting the line $y = \ell(x - x_1) + y_1$ into the Weierstrass
    equation, and can be written down explicitly as $x := \ell^2 + a_1\ell - a_2 - x_1 - x_2$ by
    inspecting the $x^2$ terms. The $y$-coordinate of $P + Q$, after applying the final negation
    that maps $y$ to $-y - a_1x - a_3$, is precisely $y := -(\ell(x - x_1) + y_1) - x - a_3$.
The group law on this set is then uniquely determined by these constructions. This file defines the
group operations by explicit equations and proves that the set is an abelian group (TODO).

## Main definitions

 * `EllipticCurve.point`: a rational point on `E`.
 * `EllipticCurve.point.add`: the addition of two rational points on `E`.

## Main statements

 * `EllipticCurve.point.add_comm`: the addition of two rational points on `E` is commutative.
 * TODO: the addition of two rational points on `E` is associative (HARD), and hence forms a group.

## Notations

 * `E⟮K⟯`: the group of `K`-rational points on an elliptic curve `E` over `F` base changed to `K`.

## Implementation notes

The proofs of `EllipticCurve.point.weierstrass_dbl'`, `EllipticCurve.point.weierstrass_add'`, and
`EllipticCurve.point.add_assoc` (TODO) are slow due to the sheer size of the polynomials involved,
but they can be hastened considerably by breaking the computations into multiple steps if necessary.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, group law
-/

namespace EllipticCurve

open polynomial

open_locale polynomial

universes u v

section basic

/-!
### The type of rational points

Use `0` instead of `EllipticCurve.point.zero`.
-/

variables {F : Type u} [comm_ring F] (E : EllipticCurve F)

section weierstrass

/-- The Weierstrass polynomial $w_E(X, Y) := Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$. -/
noncomputable def weierstrass_polynomial : F[X][X] :=
X ^ 2 + C (C E.a₁ * X) * X + C (C E.a₃) * X - C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)

/-- The proposition that an affine point $(x, y)$ lies in `E`, that is $w_E(x, y) = 0$. -/
def weierstrass_equation (x y : F) : Prop := eval x (eval (C y) E.weierstrass_polynomial) = 0

@[simp] lemma eval_weierstrass_polynomial (x y : F) :
  eval x (eval (C y) E.weierstrass_polynomial)
    = y ^ 2 + E.a₁ * x * y + E.a₃ * y - (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) :=
by simp only [weierstrass_polynomial, eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow]

lemma weierstrass_equation_iff' (x y : F) :
  E.weierstrass_equation x y
    ↔ y ^ 2 + E.a₁ * x * y + E.a₃ * y - (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) = 0 :=
by rw [weierstrass_equation, eval_weierstrass_polynomial]

@[simp] lemma weierstrass_equation_iff (x y : F) :
  E.weierstrass_equation x y
    ↔ y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ :=
by rw [weierstrass_equation_iff', sub_eq_zero]

/-- The polynomial $-Y - a_1X - a_3$ associated to negation. -/
noncomputable def neg_polynomial : F[X][X] := -X - C (C E.a₁ * X) - C (C E.a₃)

/-- The polynomial $3X^2 + 2a_2X + a_4 - a_1Y$ associated to doubling. -/
noncomputable def dbl_polynomial : F[X][X] :=
C (C 3 * X ^ 2) + C (C 2 * C E.a₂ * X) + C (C E.a₄) - C (C E.a₁) * X

end weierstrass

/-- The type of rational points on an elliptic curve `E` over `F`. This consists of the unique
point at infinity `EllipticCurve.point.zero`and the other affine points `EllipticCurve.point.some`
satisfying the Weierstrass equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ of `E`.
For a field extension `K` over `F`, the type of `K`-rational points on `E` is denoted `E⟮K⟯`. -/
inductive point
| zero
| some {x y : F} (h : E.weierstrass_equation x y)

localized "notation E⟮K⟯ := (E.base_change K).point" in EllipticCurve

namespace point

variables {E}

instance : inhabited E.point := ⟨zero⟩

instance : has_zero E.point := ⟨zero⟩

@[simp] lemma zero_def : (zero : E.point) = 0 := rfl

section negation

variables {x y : F} (h : E.weierstrass_equation x y)

include h

/-- The $y$-coordinate of the negation of an affine point. -/
@[nolint unused_arguments] def neg_y : F := -y - E.a₁ * x - E.a₃

@[simp] lemma neg_y_def : neg_y h = -y - E.a₁ * x - E.a₃ := rfl

lemma eval_neg_polynomial : eval x (eval (C y) E.neg_polynomial) = neg_y h :=
by simp only [neg_polynomial, eval_C, eval_X, eval_neg, eval_sub, eval_mul, neg_y_def]

/-- The negation of an affine point in `E` lies in `E`. -/
lemma weierstrass_equation_neg : E.weierstrass_equation x $ neg_y h :=
by { rw [weierstrass_equation_iff] at h, rw [weierstrass_equation_iff, neg_y_def, ← h], ring1 }

omit h

/-- The negation of a rational point.
Given a rational point `P`, use `-P` instead of `neg P`. -/
def neg : E.point → E.point
| 0        := 0
| (some h) := some $ weierstrass_equation_neg h

instance : has_neg E.point := ⟨neg⟩

@[simp] lemma neg_def (P : E.point) : neg P = -P := rfl

@[simp] lemma neg_zero : (-0 : E.point) = 0 := rfl

@[simp] lemma neg_some : -some h = some (weierstrass_equation_neg h) := rfl

instance : has_involutive_neg E.point := ⟨neg, by { rintro (_ | _), { refl }, { simp, ring1 } }⟩

end negation

end point

end basic

open_locale EllipticCurve

variables {F : Type u} [field F] {E : EllipticCurve F}

section dbl_add

/-!
### The addition law on rational points

Given rational points `P` and `Q`, use `P + Q` instead of `add P Q`.
-/

namespace point

section doubling

variables {x y : F} (h : E.weierstrass_equation x y)

include h

/-- The gradient of the tangent line of `E` at an affine point $(x, y)$. This is not well-defined
only in the case of $y = -y - a_1x - a_3$, which is precisely when the tangent is vertical. -/
def dbl_L : F := (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (y - neg_y h)

@[simp] lemma dbl_L_def : dbl_L h = (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (y - neg_y h) :=
rfl

lemma eval_dbl_polynomial : eval x (eval (C y) E.dbl_polynomial) / (y - neg_y h) = dbl_L h :=
by simp only [dbl_polynomial, eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow, dbl_L_def]

/-- The $x$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
def dbl_x : F := dbl_L h ^ 2 + E.a₁ * dbl_L h - E.a₂ - 2 * x

@[simp] lemma dbl_x_def : dbl_x h = dbl_L h ^ 2 + E.a₁ * dbl_L h - E.a₂ - 2 * x := rfl

/-- The $y$-coordinate of the doubling of an affine point whose tangent is not vertical,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$. -/
def dbl_y' : F := dbl_L h * (dbl_x h - x) + y

@[simp] lemma dbl_y'_def : dbl_y' h = dbl_L h * (dbl_x h - x) + y := rfl

/-- The $y$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
def dbl_y : F := -dbl_y' h - E.a₁ * dbl_x h - E.a₃

@[simp] lemma dbl_y_def : dbl_y h = -dbl_y' h - E.a₁ * dbl_x h - E.a₃ := rfl

/-- The doubling of an affine point in `E` whose tangent is not vertical,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$, lies in `E`. -/
lemma weierstrass_equation_dbl' (hy : y ≠ neg_y h) : E.weierstrass_equation (dbl_x h) (dbl_y' h) :=
begin
  rw [weierstrass_equation_iff'],
  convert_to
    dbl_L h * (dbl_L h * (dbl_L h * (y - neg_y h)
                          + (-3 * x ^ 2 + E.a₁ ^ 2 * x - 2 * E.a₂ * x + 3 * E.a₁ * y + E.a₁ * E.a₃
                              - E.a₄))
                + (-6 * E.a₁ * x ^ 2 - 6 * x * y - 3 * E.a₁ * E.a₂ * x - 3 * E.a₃ * x + E.a₁ ^ 2 * y
                    - 2 * E.a₂ * y - E.a₁ * E.a₄ - E.a₂ * E.a₃))
    + (8 * x ^ 3 + 8 * E.a₂ * x ^ 2 - 2 * E.a₁ * x * y + y ^ 2 + 2 * E.a₂ ^ 2 * x + 2 * E.a₄ * x
        - E.a₁ * E.a₂ * y + E.a₃ * y + E.a₂ * E.a₄ - E.a₆) = 0,
  { simp only [dbl_x_def, dbl_y'_def, neg_y_def], ring1 },
  field_simp [-neg_y_def, sub_ne_zero_of_ne hy],
  rw [weierstrass_equation_iff'] at h,
  linear_combination (2 * y + E.a₁ * x + E.a₃) ^ 2 * h
    with { normalization_tactic := `[rw [neg_y_def], ring1] }
end

/-- The doubling of an affine point in `E` whose tangent is not vertical lies in `E`. -/
lemma weierstrass_equation_dbl (hy : y ≠ neg_y h) : E.weierstrass_equation (dbl_x h) (dbl_y h) :=
weierstrass_equation_neg $ weierstrass_equation_dbl' h hy

end doubling

section addition

variables {x₁ x₂ y₁ y₂ : F} (h₁ : E.weierstrass_equation x₁ y₁) (h₂ : E.weierstrass_equation x₂ y₂)

include h₁ h₂

/-- The gradient of the line joining two affine points $(x_1, y_1)$ and $(x_2, y_2)$. This is not
well-defined only in the case of $x_1 = x_2$, where the line becomes a tangent of `E`. -/
@[nolint unused_arguments] def add_L : F := (y₁ - y₂) / (x₁ - x₂)

@[simp] lemma add_L_def : add_L h₁ h₂ = (y₁ - y₂) / (x₁ - x₂) := rfl

/-- The $x$-coordinate of the addition of two affine points with distinct $x$-coordinates. -/
def add_x : F := add_L h₁ h₂ ^ 2 + E.a₁ * add_L h₁ h₂ - E.a₂ - x₁ - x₂

@[simp] lemma add_x_def : add_x h₁ h₂ = add_L h₁ h₂ ^ 2 + E.a₁ * add_L h₁ h₂ - E.a₂ - x₁ - x₂ := rfl

/-- The $y$-coordinate of the addition of two affine points with distinct $x$-coordinates,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$. -/
def add_y' : F := add_L h₁ h₂ * (add_x h₁ h₂ - x₁) + y₁

@[simp] lemma add_y'_def : add_y' h₁ h₂ = add_L h₁ h₂ * (add_x h₁ h₂ - x₁) + y₁ := rfl

/-- The $y$-coordinate of the addition of two affine points with distinct $x$-coordinates. -/
def add_y : F := -add_y' h₁ h₂ - E.a₁ * add_x h₁ h₂ - E.a₃

@[simp] lemma add_y_def : add_y h₁ h₂ = -add_y' h₁ h₂ - E.a₁ * add_x h₁ h₂ - E.a₃ := rfl

/-- The addition of two affine points in `E` with distinct $x$-coordinates,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$, lies in `E`. -/
lemma weierstrass_equation_add' (hx : x₁ ≠ x₂) :
  E.weierstrass_equation (add_x h₁ h₂) (add_y' h₁ h₂) :=
begin
  rw [weierstrass_equation_iff'],
  convert_to
    add_L h₁ h₂ * (add_L h₁ h₂ * (add_L h₁ h₂ * (add_L h₁ h₂ * (x₁ - x₂) * -1
                                                  + (-E.a₁ * x₁ + 2 * E.a₁ * x₂ + 2 * y₁ + E.a₃))
                                  + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + E.a₁ ^ 2 * x₂
                                      - 2 * E.a₂ * x₂ + 3 * E.a₁ * y₁ + E.a₁ * E.a₃ - E.a₄))
                    + (-E.a₁ * x₁ ^ 2 - 3 * E.a₁ * x₁ * x₂ - 4 * x₁ * y₁ - 2 * E.a₁ * x₂ ^ 2
                        - 2 * x₂ * y₁ - E.a₁ * E.a₂ * x₁ - 2 * E.a₃ * x₁ - 2 * E.a₁ * E.a₂ * x₂
                        - E.a₃ * x₂ + E.a₁ ^ 2 * y₁ - 2 * E.a₂ * y₁ - E.a₁ * E.a₄ - E.a₂ * E.a₃))
    + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * E.a₂ * x₁ ^ 2 + 4 * E.a₂ * x₁ * x₂
        - E.a₁ * x₁ * y₁ + 2 * E.a₂ * x₂ ^ 2 - E.a₁ * x₂ * y₁ + y₁ ^ 2 + E.a₂ ^ 2 * x₁ + E.a₄ * x₁
        + E.a₂ ^ 2 * x₂ + E.a₄ * x₂ - E.a₁ * E.a₂ * y₁ + E.a₃ * y₁ + E.a₂ * E.a₄ - E.a₆) = 0,
  { simp only [add_x_def, add_y'_def], ring1 },
  field_simp [sub_ne_zero_of_ne hx],
  rw [weierstrass_equation_iff'] at h₁ h₂,
  linear_combination
    -((x₁ - x₂) ^ 2 * (x₁ + 2 * x₂ + E.a₂) - (x₁ - x₂) * (y₁ - y₂) * E.a₁ - (y₁ - y₂) ^ 2) * h₁
    + ((x₁ - x₂) ^ 2 * (2 * x₁ + x₂ + E.a₂) - (x₁ - x₂) * (y₁ - y₂) * E.a₁ - (y₁ - y₂) ^ 2) * h₂
    with { normalization_tactic := `[ring1] }
end

/-- The addition of two affine points in `E` with distinct $x$-coordinates lies in `E`. -/
lemma weierstrass_equation_add (hx : x₁ ≠ x₂) :
  E.weierstrass_equation (add_x h₁ h₂) (add_y h₁ h₂) :=
weierstrass_equation_neg $ weierstrass_equation_add' h₁ h₂ hx

lemma y_eq_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) : y₁ = y₂ :=
begin
  rw [neg_y] at hy,
  rw [weierstrass_equation_iff] at h₂,
  rw [weierstrass_equation_iff', hx, ← h₂] at h₁,
  apply eq_of_sub_eq_zero ∘ eq_zero_of_ne_zero_of_mul_right_eq_zero (sub_ne_zero.mpr hy),
  convert h₁,
  ring1
end

lemma y_ne_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) : y₁ ≠ neg_y h₁ :=
by { convert hy, exact y_eq_of_y_ne h₁ h₂ hx hy }

omit h₁ h₂

open_locale classical

/-- The addition of two rational points.
Given two rational points `P` and `Q`, use `P + Q` instead of `add P Q`. -/
noncomputable def add : E.point → E.point → E.point
| 0                      P                      := P
| P                      0                      := P
| (@some _ _ _ x₁ y₁ h₁) (@some _ _ _ x₂ y₂ h₂) :=
if hx : x₁ = x₂ then if hy : y₁ = neg_y h₂ then 0
else some $ weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy
else some $ weierstrass_equation_add h₁ h₂ hx

noncomputable instance : has_add E.point := ⟨add⟩

@[simp] lemma add_def (P Q : E.point) : add P Q = P + Q := rfl

noncomputable instance : add_zero_class E.point :=
⟨0, (+), by rintro (_ | _); refl, by rintro (_ | _); refl⟩

@[simp] lemma some_add_some_of_y_eq (hx : x₁ = x₂) (hy : y₁ = neg_y h₂) : some h₁ + some h₂ = 0 :=
by rw [← add_def, add, dif_pos hx, dif_pos hy]

@[simp] lemma some_add_self_of_y_eq (hy : y₁ = neg_y h₁) : some h₁ + some h₁ = 0 :=
some_add_some_of_y_eq h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) :
  some h₁ + some h₂ = some (weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
by rw [← add_def, add, dif_pos hx, dif_neg hy]

lemma some_add_some_of_y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) :
  some h₁ + some h₂ = -some (weierstrass_equation_dbl' h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
some_add_some_of_y_ne h₁ h₂ hx hy

@[simp] lemma some_add_self_of_y_ne (hy : y₁ ≠ neg_y h₁) :
  some h₁ + some h₁ = some (weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

lemma some_add_self_of_y_ne' (hy : y₁ ≠ neg_y h₁) :
  some h₁ + some h₁ = -some (weierstrass_equation_dbl' h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_x_ne (hx : x₁ ≠ x₂) :
  some h₁ + some h₂ = some (weierstrass_equation_add h₁ h₂ hx) :=
by rw [← add_def, add, dif_neg hx]

lemma some_add_some_of_x_ne' (hx : x₁ ≠ x₂) :
  some h₁ + some h₂ = -some (weierstrass_equation_add' h₁ h₂ hx) :=
some_add_some_of_x_ne h₁ h₂ hx

end addition

end point

end dbl_add

section group_law

/-!
### The axioms of rational points

TODO: Associativity of addition.
-/

namespace point

@[simp] lemma add_eq_zero (P Q : E.point) : P + Q = 0 ↔ P = -Q :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | ⟨x₁, y₁, h₁⟩, _ | ⟨x₂, y₂, h₂⟩⟩,
  { refl },
  { rw [zero_def, zero_add, eq_neg_iff_eq_neg, neg_zero] },
  { refl },
  { simp only [neg_some],
    split,
    { intro h,
      by_cases hx : x₁ = x₂,
      { by_cases hy : y₁ = neg_y h₂,
        { exact ⟨hx, hy⟩ },
        { rw [some_add_some_of_y_ne h₁ h₂ hx hy] at h,
          contradiction } },
      { rw [some_add_some_of_x_ne h₁ h₂ hx] at h,
        contradiction } },
    { exact λ ⟨hx, hy⟩, some_add_some_of_y_eq h₁ h₂ hx hy } }
end

@[simp] lemma add_neg_eq_zero (P Q : E.point) : P + -Q = 0 ↔ P = Q := by rw [add_eq_zero, neg_neg]

@[simp] lemma add_left_neg (P : E.point) : -P + P = 0 := by rw [add_eq_zero]

lemma add_comm (P Q : E.point) : P + Q = Q + P :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | ⟨x₁, y₁, h₁⟩, _ | ⟨x₂, y₂, h₂⟩⟩,
  any_goals { refl },
  by_cases hx : x₁ = x₂,
  { by_cases hy : y₁ = neg_y h₂,
    { rw [some_add_some_of_y_eq h₁ h₂ hx hy,
          some_add_some_of_y_eq h₂ h₁ hx.symm $ by { simp only [neg_y_def, hx, hy], ring1 }] },
    { simp only [hx, y_eq_of_y_ne h₁ h₂ hx hy] } },
  { rw [some_add_some_of_x_ne' h₁ h₂ hx, some_add_some_of_x_ne' h₂ h₁ $ ne.symm hx, neg_inj],
    field_simp [sub_ne_zero_of_ne hx, sub_ne_zero_of_ne (ne.symm hx)],
    exact ⟨by ring1, by ring1⟩ }
end

end point

end group_law

end EllipticCurve
