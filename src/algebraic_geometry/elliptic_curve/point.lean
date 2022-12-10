/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.elliptic_curve.weierstrass
import field_theory.galois -- temporary import to enable point notation
import tactic.field_simp

/-!
# The group of rational points on an elliptic curve over a field

Let $E$ be an elliptic curve over a field $F$. A rational point on $E$ is simply a point $[X:Y:Z]$
in the projective plane cubic $Y^2Z + a_1XYZ + a_3YZ^2 = X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3$. This
file defines the type of rational points on $E$ as an inductive, since any such point either lies in
the affine chart $Z \ne 0$ and satisfies the Weierstrass equation obtained by setting $X := X/Z$ and
$Y := Y/Z$, or is the unique point at infinity $\mathcal{O} = [0:1:0]$ obtained by setting $Z := 0$.
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
    In the latter two cases, the $X$-coordinate of $P + Q$ is then the unique third solution of the
    equation obtained by substituting the line $Y = \ell(X - x_1) + y_1$ into the Weierstrass
    equation, and can be written down explicitly as $x := \ell^2 + a_1\ell - a_2 - x_1 - x_2$ by
    inspecting the $x^2$ terms. The $Y$-coordinate of $P + Q$, after applying the final negation
    that maps $Y$ to $-Y - a_1X - a_3$, is precisely $y := -(\ell(x - x_1) + y_1) - x - a_3$.
The group law on this set is then uniquely determined by these constructions. This file defines the
group operations by explicit equations and proves that the set is an abelian group (TODO).

## Main definitions

 * `elliptic_curve.point`: the type of rational points on an elliptic curve.
 * `elliptic_curve.point.add`: the addition of two rational points.

## Main statements

 * `elliptic_curve.point.add_comm`: the addition of two rational points is commutative.
 * TODO: the addition of two rational points is associative, and hence forms a group.

## Notations

 * `E⟮K⟯`: the type of rational points on an elliptic curve `E` base changed to `K`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, group law
-/

namespace elliptic_curve

open polynomial weierstrass_curve

open_locale polynomial

universe u

section basic

/-! ### The type of rational points on an elliptic curve -/

variables {F : Type u} [comm_ring F] (E : elliptic_curve F)

/-- A rational point on an elliptic curve `E` over `F`. This is either the point at infinity
`elliptic_curve.point.zero` or an affine point `elliptic_curve.point.some` $(x, y)$ satisfying the
equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ of `E`. For a field extension `K` over
`F`, the type of `K`-rational points on `E` is denoted `E⟮K⟯`. -/
inductive point
| zero
| some {x y : F} (h : E.equation x y)

localized "notation E⟮K⟯ := (E.base_change K).point" in elliptic_curve

namespace point

instance : inhabited E.point := ⟨zero⟩

instance : has_zero E.point := ⟨zero⟩

@[simp] lemma zero_def : (zero : E.point) = 0 := rfl

end point

section negation

variables (x y : F)

/-- The $Y$-coordinate of the negation of an affine point. -/
def neg_Y : F := -y - E.a₁ * x - E.a₃

@[simp] lemma neg_Y_def : E.neg_Y x y = -y - E.a₁ * x - E.a₃ := rfl

lemma neg_Y_neg_Y : -E.neg_Y x y - E.a₁ * x - E.a₃ = y := by { rw [neg_Y_def], ring1 }

/-- The polynomial $-Y - a_1X - a_3$ associated to negation. -/
noncomputable def neg_polynomial : F[X][X] := -X - C (C E.a₁ * X) - C (C E.a₃)

lemma neg_Y_eq_eval : E.neg_Y x y = eval x (eval (C y) E.neg_polynomial) :=
by simp only [neg_Y_def, neg_polynomial, eval_C, eval_X, eval_neg, eval_sub, eval_mul]

variables {E x y} (h : E.equation x y)

include h

/-- The negation of an affine point in `E` lies in `E`. -/
lemma equation_neg : E.equation x $ E.neg_Y x y :=
by { rw [equation_iff] at h, rw [equation_iff, neg_Y_def, ← h], ring1 }

omit h

namespace point

/-- The negation of a rational point.

Given a rational point `P`, use `-P` instead of `neg P`. -/
def neg : E.point → E.point
| 0        := 0
| (some h) := some $ equation_neg h

instance : has_neg E.point := ⟨neg⟩

@[simp] lemma neg_def (P : E.point) : P.neg = -P := rfl

@[simp] lemma neg_zero : (-0 : E.point) = 0 := rfl

@[simp] lemma neg_some (h : E.equation x y) : -some h = some (equation_neg h) := rfl

instance : has_involutive_neg E.point := ⟨neg, by { rintro (_ | _), { refl }, { simp, ring1 } }⟩

end point

end negation

end basic

variables {F : Type u} [field F] (E : elliptic_curve F)

section dbl_add

/-! ### The addition law on rational points on an elliptic curve -/

section doubling

variables (E) (x y : F)

/-- The gradient of the tangent line of `E` at an affine point $(x, y)$. This is not well-defined
only in the case of $y = -y - a_1x - a_3$, where the tangent is vertical. -/
def dbl_L : F := (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (y - E.neg_Y x y)

@[simp] lemma dbl_L_def :
  E.dbl_L x y = (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (y - E.neg_Y x y) :=
rfl

lemma dbl_L_eq_eval :
  E.dbl_L x y = -eval x (eval (C y) E.polynomial_X) / eval x (eval (C y) E.polynomial_Y) :=
by { rw [dbl_L, eval_polynomial_X, neg_sub], congr' 1, rw [neg_Y, eval_polynomial_Y], ring1 }

/-- The $X$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
def dbl_X : F := E.dbl_L x y ^ 2 + E.a₁ * E.dbl_L x y - E.a₂ - 2 * x

@[simp] lemma dbl_X_def : E.dbl_X x y = E.dbl_L x y ^ 2 + E.a₁ * E.dbl_L x y - E.a₂ - 2 * x := rfl

/-- The $Y$-coordinate of the doubling of an affine point whose tangent is not vertical,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$. -/
def dbl_Y' : F := E.dbl_L x y * (E.dbl_X x y - x) + y

@[simp] lemma dbl_Y'_def : E.dbl_Y' x y = E.dbl_L x y * (E.dbl_X x y - x) + y := rfl

/-- The $Y$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
def dbl_Y : F := -E.dbl_Y' x  y - E.a₁ * E.dbl_X x y - E.a₃

@[simp] lemma dbl_Y_def : E.dbl_Y x y = -E.dbl_Y' x y - E.a₁ * E.dbl_X x y - E.a₃ := rfl

variables {E x y} (h : E.equation x y)

include h

/-- The doubling of an affine point in `E` whose tangent is not vertical,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `E`. -/
lemma equation_dbl' (hy : y ≠ E.neg_Y x y) : E.equation (E.dbl_X x y) (E.dbl_Y' x y) :=
begin
  rw [equation_iff'],
  convert_to
    E.dbl_L x y * (E.dbl_L x y * (E.dbl_L x y * (y - E.neg_Y x y)
                                  + (-3 * x ^ 2 + E.a₁ ^ 2 * x - 2 * E.a₂ * x + 3 * E.a₁ * y
                                      + E.a₁ * E.a₃ - E.a₄))
                    + (-6 * E.a₁ * x ^ 2 - 6 * x * y - 3 * E.a₁ * E.a₂ * x - 3 * E.a₃ * x
                        + E.a₁ ^ 2 * y - 2 * E.a₂ * y - E.a₁ * E.a₄ - E.a₂ * E.a₃))
    + (8 * x ^ 3 + 8 * E.a₂ * x ^ 2 - 2 * E.a₁ * x * y + y ^ 2 + 2 * E.a₂ ^ 2 * x + 2 * E.a₄ * x
        - E.a₁ * E.a₂ * y + E.a₃ * y + E.a₂ * E.a₄ - E.a₆) = 0,
  { simp only [dbl_X_def, dbl_Y'_def, neg_Y_def], ring1 },
  field_simp [-neg_Y_def, sub_ne_zero_of_ne hy],
  rw [equation_iff'] at h,
  linear_combination (2 * y + E.a₁ * x + E.a₃) ^ 2 * h
    with { normalization_tactic := `[rw [neg_Y_def], ring1] }
end

/-- The doubling of an affine point in `E` whose tangent is not vertical lies in `E`. -/
lemma equation_dbl (hy : y ≠ E.neg_Y x y) : E.equation (E.dbl_X x y) (E.dbl_Y x y) :=
equation_neg $ equation_dbl' h hy

omit h

end doubling

section addition

variables (E) (x₁ x₂ y₁ y₂ : F)

/-- The gradient of the line joining two affine points $(x_1, y_1)$ and $(x_2, y_2)$. This is not
well-defined only in the case of $x_1 = x_2$, where the line becomes a tangent of `E`. -/
def add_L : F := (y₁ - y₂) / (x₁ - x₂)

@[simp] lemma add_L_def : add_L x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := rfl

/-- The $X$-coordinate of the addition of two affine points with distinct $X$-coordinates. -/
def add_X : F := add_L x₁ x₂ y₁ y₂ ^ 2 + E.a₁ * add_L x₁ x₂ y₁ y₂ - E.a₂ - x₁ - x₂

@[simp] lemma add_X_def :
  E.add_X x₁ x₂ y₁ y₂ = add_L x₁ x₂ y₁ y₂ ^ 2 + E.a₁ * add_L x₁ x₂ y₁ y₂ - E.a₂ - x₁ - x₂ :=
rfl

/-- The $Y$-coordinate of the addition of two affine points with distinct $X$-coordinates,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$. -/
def add_Y' : F := add_L x₁ x₂ y₁ y₂ * (E.add_X x₁ x₂ y₁ y₂ - x₁) + y₁

@[simp] lemma add_Y'_def :
  E.add_Y' x₁ x₂ y₁ y₂ = add_L x₁ x₂ y₁ y₂ * (E.add_X x₁ x₂ y₁ y₂ - x₁) + y₁ :=
rfl

/-- The $Y$-coordinate of the addition of two affine points with distinct $X$-coordinates. -/
def add_Y : F := -E.add_Y' x₁ x₂ y₁ y₂ - E.a₁ * E.add_X x₁ x₂ y₁ y₂ - E.a₃

@[simp] lemma add_Y_def :
  E.add_Y x₁ x₂ y₁ y₂ = -E.add_Y' x₁ x₂ y₁ y₂ - E.a₁ * E.add_X x₁ x₂ y₁ y₂ - E.a₃ :=
rfl

variables {E x₁ x₂ y₁ y₂} (h₁ : E.equation x₁ y₁) (h₂ : E.equation x₂ y₂)

include h₁ h₂

/-- The addition of two affine points in `E` with distinct $X$-coordinates,
before applying the final negation that maps $$ to $-Y - a_1X - a_3$, lies in `E`. -/
lemma equation_add' (hx : x₁ ≠ x₂) : E.equation (E.add_X x₁ x₂ y₁ y₂) (E.add_Y' x₁ x₂ y₁ y₂) :=
begin
  rw [equation_iff'],
  convert_to
    add_L x₁ x₂ y₁ y₂ * (add_L x₁ x₂ y₁ y₂ * (add_L x₁ x₂ y₁ y₂ * (add_L x₁ x₂ y₁ y₂
                                                                    * (x₁ - x₂) * -1
                                                                    + (-E.a₁ * x₁ + 2 * E.a₁ * x₂
                                                                        + 2 * y₁ + E.a₃))
                                              + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + E.a₁ ^ 2 * x₂
                                                  - 2 * E.a₂ * x₂ + 3 * E.a₁ * y₁ + E.a₁ * E.a₃
                                                  - E.a₄))
                          + (-E.a₁ * x₁ ^ 2 - 3 * E.a₁ * x₁ * x₂ - 4 * x₁ * y₁ - 2 * E.a₁ * x₂ ^ 2
                              - 2 * x₂ * y₁ - E.a₁ * E.a₂ * x₁ - 2 * E.a₃ * x₁
                              - 2 * E.a₁ * E.a₂ * x₂ - E.a₃ * x₂ + E.a₁ ^ 2 * y₁ - 2 * E.a₂ * y₁
                              - E.a₁ * E.a₄ - E.a₂ * E.a₃))
    + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * E.a₂ * x₁ ^ 2 + 4 * E.a₂ * x₁ * x₂
        - E.a₁ * x₁ * y₁ + 2 * E.a₂ * x₂ ^ 2 - E.a₁ * x₂ * y₁ + y₁ ^ 2 + E.a₂ ^ 2 * x₁ + E.a₄ * x₁
        + E.a₂ ^ 2 * x₂ + E.a₄ * x₂ - E.a₁ * E.a₂ * y₁ + E.a₃ * y₁ + E.a₂ * E.a₄ - E.a₆) = 0,
  { simp only [add_X_def, add_Y'_def], ring1 },
  field_simp [sub_ne_zero_of_ne hx],
  rw [equation_iff'] at h₁ h₂,
  linear_combination
    -((x₁ - x₂) ^ 2 * (x₁ + 2 * x₂ + E.a₂) - (x₁ - x₂) * (y₁ - y₂) * E.a₁ - (y₁ - y₂) ^ 2) * h₁
    + ((x₁ - x₂) ^ 2 * (2 * x₁ + x₂ + E.a₂) - (x₁ - x₂) * (y₁ - y₂) * E.a₁ - (y₁ - y₂) ^ 2) * h₂
    with { normalization_tactic := `[ring1] }
end

/-- The addition of two affine points in `E` with distinct $X$-coordinates lies in `E`. -/
lemma equation_add (hx : x₁ ≠ x₂) : E.equation (E.add_X x₁ x₂ y₁ y₂) (E.add_Y x₁ x₂ y₁ y₂) :=
equation_neg $ equation_add' h₁ h₂ hx

lemma y_eq_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ E.neg_Y x₂ y₂) : y₁ = y₂ :=
begin
  rw [neg_Y] at hy,
  rw [equation_iff] at h₂,
  rw [equation_iff', hx, ← h₂] at h₁,
  apply eq_of_sub_eq_zero ∘ eq_zero_of_ne_zero_of_mul_right_eq_zero (sub_ne_zero.mpr hy),
  convert h₁,
  ring1
end

lemma y_ne_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ E.neg_Y x₂ y₂) : y₁ ≠ E.neg_Y x₁ y₁ :=
by { convert hy, exact y_eq_of_y_ne h₁ h₂ hx hy }

omit h₁ h₂

namespace point

open_locale classical

/-- The addition of two rational points.

Given two rational points `P` and `Q`, use `P + Q` instead of `add P Q`. -/
noncomputable def add : E.point → E.point → E.point
| 0                      P                      := P
| P                      0                      := P
| (@some _ _ _ x₁ y₁ h₁) (@some _ _ _ x₂ y₂ h₂) :=
if hx : x₁ = x₂ then if hy : y₁ = E.neg_Y x₂ y₂ then 0
else some $ equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy
else some $ equation_add h₁ h₂ hx

noncomputable instance : has_add E.point := ⟨add⟩

@[simp] lemma add_def (P Q : E.point) : P.add Q = P + Q := rfl

noncomputable instance : add_zero_class E.point :=
⟨0, (+), by rintro (_ | _); refl, by rintro (_ | _); refl⟩

@[simp] lemma some_add_some_of_y_eq (hx : x₁ = x₂) (hy : y₁ = E.neg_Y x₂ y₂) :
  some h₁ + some h₂ = 0 :=
by rw [← add_def, add, dif_pos hx, dif_pos hy]

@[simp] lemma some_add_self_of_y_eq (hy : y₁ = E.neg_Y x₁ y₁) : some h₁ + some h₁ = 0 :=
some_add_some_of_y_eq h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ E.neg_Y x₂ y₂) :
  some h₁ + some h₂ = some (equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
by rw [← add_def, add, dif_pos hx, dif_neg hy]

lemma some_add_some_of_y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ E.neg_Y x₂ y₂) :
  some h₁ + some h₂ = -some (equation_dbl' h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
some_add_some_of_y_ne h₁ h₂ hx hy

@[simp] lemma some_add_self_of_y_ne (hy : y₁ ≠ E.neg_Y x₁ y₁) :
  some h₁ + some h₁ = some (equation_dbl h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

lemma some_add_self_of_y_ne' (hy : y₁ ≠ E.neg_Y x₁ y₁) :
  some h₁ + some h₁ = -some (equation_dbl' h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_x_ne (hx : x₁ ≠ x₂) :
  some h₁ + some h₂ = some (equation_add h₁ h₂ hx) :=
by rw [← add_def, add, dif_neg hx]

lemma some_add_some_of_x_ne' (hx : x₁ ≠ x₂) : some h₁ + some h₂ = -some (equation_add' h₁ h₂ hx) :=
some_add_some_of_x_ne h₁ h₂ hx

end point

end addition

end dbl_add

section group_law

/-! ### The axioms of rational points -/

namespace point

@[simp] lemma add_eq_zero (P Q : E.point) : P + Q = 0 ↔ P = -Q :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | @⟨x₁, y₁, h₁⟩, _ | @⟨x₂, y₂, h₂⟩⟩,
  { refl },
  { rw [zero_def, zero_add, eq_neg_iff_eq_neg, neg_zero] },
  { refl },
  { simp only [neg_some],
    split,
    { intro h,
      by_cases hx : x₁ = x₂,
      { by_cases hy : y₁ = E.neg_Y x₂ y₂,
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
  rcases ⟨P, Q⟩ with ⟨_ | @⟨x₁, y₁, h₁⟩, _ | @⟨x₂, y₂, h₂⟩⟩,
  any_goals { refl },
  by_cases hx : x₁ = x₂,
  { by_cases hy : y₁ = E.neg_Y x₂ y₂,
    { rw [some_add_some_of_y_eq h₁ h₂ hx hy,
          some_add_some_of_y_eq h₂ h₁ hx.symm $ by { simp only [neg_Y_def, hx, hy], ring1 }] },
    { simp only [hx, y_eq_of_y_ne h₁ h₂ hx hy] } },
  { rw [some_add_some_of_x_ne' h₁ h₂ hx, some_add_some_of_x_ne' h₂ h₁ $ ne.symm hx, neg_inj],
    field_simp [sub_ne_zero_of_ne hx, sub_ne_zero_of_ne (ne.symm hx)],
    exact ⟨by ring1, by ring1⟩ }
end

end point

end group_law

end elliptic_curve
