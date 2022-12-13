/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.elliptic_curve.weierstrass
import field_theory.galois -- temporary import to enable point notation
import tactic.field_simp

/-!
# The group of nonsingular rational points on a Weierstrass curve over a field

This file defines the type of nonsingular rational points on a Weierstrass curve over a field and
(TODO) proves that it forms an abelian group under a chord-and-tangent process.

## Mathematical background

Let `W` be an Weierstrass curve over a field `F`. A rational point on `W` is simply a point
$[A:B:C]$ defined over `F` in the projective plane satisfying the homogeneous cubic equation
$B^2C + a_1ABC + a_3BC^2 = A^3 + a_2A^2C + a_4AC^2 + a_6C^3$. Any such point either lies in the
affine chart $C \ne 0$ and satisfies the Weierstrass equation obtained by setting $X := A/C$ and
$Y := B/C$, or is the unique point at infinity $0 := [0:1:0]$ when $C = 0$. With this new
description, a nonsingular rational point on `W` is either $\mathcal{O}$ or an affine point $(x, y)$
where the partial derivatives $W_X(X, Y)$ and $W_Y(X, Y)$ do not both vanish. For a field extension
`K` of `F`, a `K`-rational point is simply a rational point on `W` base changed to `K`.

The set of nonsingular rational points forms an abelian group under a chord-and-tangent process.
 * The identity point is `0`.
 * Given a point `P`, its negation `-P` is defined to be the unique third point of intersection
    between `W` and the line through `0` and `P`, which exists by Bézout's theorem.
    Explicitly, if `P` is $(x, y)$, then `-P` is $(x, -y - a_1x - a_3)$.
 * Given two points `P` and `Q`, their addition `P + Q` is defined to be the negation of the unique
    third point of intersection between `W` and the line through `P` and `Q`, which again exists by
    Bézout's theorem. Explicitly, let `P` be $(x_1, y_1)$ and let `Q` be $(x_2, y_2)$.
      * If $x_1 = x_2$ and `P = -Q` then this line is vertical and `P + Q` is `0`.
      * If $x_1 = x_2$ and `P ≠ -Q` then this line is the tangent of `W` at `P = Q` and has
        gradient $\ell := (3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$.
      * Otherwise $x_1 \ne x_2$ then this line has gradient $\ell := (y_1 - y_2) / (x_1 - x_2)$.
    In the latter two cases, the $X$-coordinate of `P + Q` is then the unique third solution of the
    equation obtained by substituting the line $Y = \ell(X - x_1) + y_1$ into the Weierstrass
    equation, and can be written down explicitly as $x := \ell^2 + a_1\ell - a_2 - x_1 - x_2$ by
    inspecting the $X^2$ terms. The $Y$-coordinate of `P + Q`, after applying the final negation
    that maps $Y$ to $-Y - a_1X - a_3$, is precisely $y := -(\ell(x - x_1) + y_1) - x - a_3$.
The group law on this set is then uniquely determined by these constructions.

## Main definitions

 * `weierstrass_curve.point`: the type of nonsingular rational points on a Weierstrass curve `W`.
 * `weierstrass_curve.point.add`: the addition of two nonsingular rational points on `W`.

## Main statements

 * TODO: the addition of two nonsingular rational points on `W` forms a group.

## Notations

 * `W⟮K⟯`: the group of nonsingular rational points on a Weierstrass curve `W` base changed to `K`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, group law
-/

private meta def eval_simp : tactic unit :=
`[simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow]]

private meta def C_simp : tactic unit :=
`[simp only [C_1, C_bit0, C_neg, C_add, C_sub, C_mul, C_pow]]

private meta def derivative_simp : tactic unit :=
`[simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
             derivative_sub, derivative_mul, derivative_sq]]

universe u

namespace weierstrass_curve

open polynomial

open_locale polynomial

section basic

/-! ### Polynomials associated to nonsingular rational points on a Weierstrass curve -/

variables {F : Type u} [comm_ring F] (W : weierstrass_curve F) (x x₁ x₂ y y₁ y₂ L : F)

/-- The polynomial $-Y - a_1X - a_3$ associated to negation. -/
noncomputable def neg_polynomial : _root_.polynomial $ _root_.polynomial F :=
-X - C (C W.a₁ * X) - C (C W.a₃)

/-- The $Y$-coordinate of the negation of an affine point. -/
@[simp] def neg_Y : F := -y - W.a₁ * x - W.a₃

lemma neg_Y_neg_Y : -W.neg_Y x y - W.a₁ * x - W.a₃ = y := by { rw [neg_Y], ring1 }

lemma neg_Y_eq_eval : W.neg_Y x y = eval x (eval (C y) W.neg_polynomial) :=
by simp only [neg_Y, neg_polynomial, eval_C, eval_X, eval_neg, eval_sub, eval_mul]

/-- The polynomial obtained by substituting the line $Y := L*(X - x_1) + y_1$, with a gradient of
$L$ and contains a point $(x_1, y_1)$ of `W`, into the polynomial $W(X, Y)$ associated to `W`.
If such a line intersects `W` at a point $(x_2, y_2)$ of `W`, then the roots of this polynomial are
precisely $x_1$, $x_2$, and the $X$-coordinate of the addition of $(x_1, y_1)$ and $(x_2, y_2)$. -/
noncomputable def add_polynomial : _root_.polynomial F :=
eval (C L * (X - C x₁) + C y₁) W.polynomial

lemma add_polynomial_eq : W.add_polynomial x₁ y₁ L = -cubic.to_poly
  ⟨1, -L ^ 2 - W.a₁ * L + W.a₂,
    2 * x₁ * L ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * L + (-W.a₁ * y₁ + W.a₄),
    -x₁ ^ 2 * L ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * L - (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)⟩ :=
by { rw [add_polynomial, weierstrass_curve.polynomial, cubic.to_poly], eval_simp, C_simp, ring1 }

/-- The $X$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$,
where the line through them is not vertical and has gradient $L$.
This depends on `W`, and has the argument order $x_1$, $x_2$, and $L$. -/
@[simp] def add_X : F := L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂

/-- The $Y$-coordinate, before applying the final negation, of the addition of two affine points
$(x_1, y_1)$ and $(x_2, y_2)$, where the line through them is not vertical and has gradient $L$.
This depends on `W`, and has the argument order $x_1$, $x_2$, $y_1$, and $L$. -/
@[simp] def add_Y' : F := L * (W.add_X x₁ x₂ L - x₁) + y₁

/-- The $Y$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$,
where the line through them is not vertical and has gradient $L$.
This depends on `W`, and has the argument order $x_1$, $x_2$, $y_1$, and $L$. -/
@[simp] def add_Y : F := -W.add_Y' x₁ x₂ y₁ L - W.a₁ * W.add_X x₁ x₂ L - W.a₃

lemma equation_add_iff :
  W.equation (W.add_X x₁ x₂ L) (W.add_Y' x₁ x₂ y₁ L)
    ↔ eval (W.add_X x₁ x₂ L) (W.add_polynomial x₁ y₁ L) = 0 :=
by { rw [equation, add_Y', add_polynomial, weierstrass_curve.polynomial], eval_simp }

lemma nonsingular_add_of_eval_derivative_ne_zero
  (hx : eval (W.add_X x₁ x₂ L) (derivative $ W.add_polynomial x₁ y₁ L) ≠ 0) :
  W.nonsingular (W.add_X x₁ x₂ L) (W.add_Y' x₁ x₂ y₁ L) :=
begin
  rw [nonsingular, add_Y', polynomial_X, polynomial_Y],
  eval_simp,
  contrapose! hx,
  rw [add_polynomial, weierstrass_curve.polynomial],
  eval_simp,
  derivative_simp,
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one],
  eval_simp,
  linear_combination hx.left + L * hx.right with { normalization_tactic := `[norm_num1, ring1] }
end

/-! ### The type of nonsingular rational points on a Weierstrass curve -/

/-- A nonsingular rational point on a Weierstrass curve `W` over `F`. This is either the point at
infinity `weierstrass_curve.point.zero` or an affine point `weierstrass_curve.point.some` $(x, y)$
satisfying the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ of `W`. For a field
extension `K` of `F`, the type of nonsingular `K`-rational points on `W` is denoted `W⟮K⟯`. -/
inductive point
| zero
| some {x y : F} (h : W.equation x y) (h' : W.nonsingular x y)

localized "notation W⟮K⟯ := (W.base_change K).point" in weierstrass_curve

namespace point

instance : inhabited W.point := ⟨zero⟩

instance : has_zero W.point := ⟨zero⟩

@[simp] lemma zero_def : (zero : W.point) = 0 := rfl

end point

variables {W x y}

/-- The negation of an affine point in `W` lies in `W`. -/
lemma equation_neg (h : W.equation x y) : W.equation x $ W.neg_Y x y :=
by { rw [equation_iff] at h, rw [equation_iff, neg_Y, ← h], ring1 }

/-- The negation of a nonsingular affine point is nonsingular. -/
lemma nonsingular_neg (h' : W.nonsingular x y) : W.nonsingular x $ W.neg_Y x y :=
begin
  rw [nonsingular_iff] at h',
  rw [nonsingular_iff, neg_Y_neg_Y, ← @ne_comm _ y],
  contrapose! h',
  convert h',
  exact h'.right
end

namespace point

/-- The negation of a nonsingular rational point.

Given a nonsingular rational point `P`, use `-P` instead of `neg P`. -/
def neg : W.point → W.point
| 0           := 0
| (some h h') := some (equation_neg h) (nonsingular_neg h')

instance : has_neg W.point := ⟨neg⟩

@[simp] lemma neg_def (P : W.point) : P.neg = -P := rfl

@[simp] lemma neg_zero : (-0 : W.point) = 0 := rfl

@[simp] lemma neg_some (h : W.equation x y) (h' : W.nonsingular x y) :
  -some h h' = some (equation_neg h) (nonsingular_neg h') :=
rfl

instance : has_involutive_neg W.point := ⟨neg, by { rintro (_ | _), { refl }, { simp, ring1 } }⟩

end point

end basic

section addition

/-! ### The addition law on nonsingular rational points on a Weierstrass curve -/

variables {F : Type u} [field F] (W : weierstrass_curve F) (x₁ x₂ y₁ y₂ L : F)

/-- The gradient of the tangent line of `W` at an affine point $(x_1, y_1)$. This is not
well-defined only in the case of $y_1 = -y_1 - a_1x_1 - a_3$, where the tangent is vertical.
This depends on `W`, and has the argument order $x_1$ and $y_1$. -/
@[simp] def grad_of_eq : F := (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.neg_Y x₁ y₁)

lemma grad_of_eq_eq_eval :
  W.grad_of_eq x₁ y₁
    = -eval x₁ (eval (C y₁) W.polynomial_X) / eval x₁ (eval (C y₁) W.polynomial_Y) :=
by { rw [grad_of_eq, eval_polynomial_X, neg_sub], congr' 1, rw [neg_Y, eval_polynomial_Y], ring1 }

/-- The gradient of the line through two affine points $(x_1, y_1)$ and $(x_2, y_2)$. This is not
well-defined only in the case of $x_1 = x_2$, where the line is a tangent or is vertical.
This does not depend on `W`, and has the argument order $x_1$, $x_2$, $y_1$, and $y_2$. -/
@[simp] def grad_of_ne : F := (y₁ - y₂) / (x₁ - x₂)

variables {W x₁ x₂ y₁ y₂} (h₁ : W.equation x₁ y₁) (h₂ : W.equation x₂ y₂)
  (h₁' : W.nonsingular x₁ y₁) (h₂' : W.nonsingular x₂ y₂) (hy : y₁ ≠ W.neg_Y x₁ y₁) (hx : x₁ ≠ x₂)

include h₁ hy

lemma add_polynomial_of_eq :
  W.add_polynomial x₁ y₁ (W.grad_of_eq x₁ y₁)
    = -(X - C x₁) * (X - C x₁) * (X - C (W.add_X x₁ x₁ $ W.grad_of_eq x₁ y₁)) :=
begin
  rw [equation_iff] at h₁,
  rw [neg_Y, ← sub_ne_zero] at hy,
  rw [add_polynomial_eq, neg_eq_iff_neg_eq, neg_mul, neg_mul, neg_neg, cubic.prod_X_sub_C_eq,
      cubic.to_poly_injective],
  ext,
  { refl },
  { simp only [add_X],
    ring1 },
  { field_simp [hy],
    ring1 },
  { linear_combination h₁ with { normalization_tactic := `[field_simp [hy], ring1] } }
end

lemma derivative_add_polynomial_of_eq :
  derivative (W.add_polynomial x₁ y₁ $ W.grad_of_eq x₁ y₁)
    = -((X - C x₁) * (X - C x₁) + 2 * (X - C x₁) * (X - C (W.add_X x₁ x₁ $ W.grad_of_eq x₁ y₁))) :=
by { rw [add_polynomial_of_eq h₁ hy], derivative_simp, ring1 }

/-- The doubling of an affine point in `W` whose tangent is not vertical,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `W`. -/
lemma equation_add_of_eq' :
  W.equation (W.add_X x₁ x₁ $ W.grad_of_eq x₁ y₁) (W.add_Y' x₁ x₁ y₁ $ W.grad_of_eq x₁ y₁) :=
by { rw [equation_add_iff, add_polynomial_of_eq h₁ hy], eval_simp, rw [sub_self, mul_zero] }

/-- The doubling of an affine point in `W` whose tangent is not vertical lies in `W`. -/
lemma equation_add_of_eq :
  W.equation (W.add_X x₁ x₁ $ W.grad_of_eq x₁ y₁) (W.add_Y x₁ x₁ y₁ $ W.grad_of_eq x₁ y₁) :=
equation_neg $ equation_add_of_eq' h₁ hy

include h₁'

/-- The doubling of a nonsingular point in `W` whose tangent is not vertical,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, is nonsingular. -/
lemma nonsingular_add_of_eq' :
  W.nonsingular (W.add_X x₁ x₁ $ W.grad_of_eq x₁ y₁) (W.add_Y' x₁ x₁ y₁ $ W.grad_of_eq x₁ y₁) :=
begin
  by_cases hx : W.add_X x₁ x₁ (W.grad_of_eq x₁ y₁) = x₁,
  { rwa [add_Y', hx, sub_self, mul_zero, zero_add] },
  { apply nonsingular_add_of_eval_derivative_ne_zero,
    rw [derivative_add_polynomial_of_eq h₁ hy],
    eval_simp,
    rwa [neg_ne_zero, sub_self, mul_zero, add_zero, mul_self_ne_zero, sub_ne_zero] }
end

/-- The doubling of a nonsingular point in `W` whose tangent is not vertical is nonsingular. -/
lemma nonsingular_add_of_eq :
  W.nonsingular (W.add_X x₁ x₁ $ W.grad_of_eq x₁ y₁) (W.add_Y x₁ x₁ y₁ $ W.grad_of_eq x₁ y₁) :=
nonsingular_neg $ nonsingular_add_of_eq' h₁ h₁' hy

omit h₁' hy

include h₂

lemma Y_eq_of_X_eq (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.neg_Y x₂ y₂ :=
begin
  rw [equation_iff] at h₁ h₂,
  rw [← sub_eq_zero, ← @sub_eq_zero _ _ y₁, ← mul_eq_zero, neg_Y],
  linear_combination h₁ - h₂ with { normalization_tactic := `[rw [hx], ring1] }
end

lemma Y_eq_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) : y₁ = y₂ :=
or.resolve_right (Y_eq_of_X_eq h₁ h₂ hx) hy

lemma Y_ne_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) : y₁ ≠ W.neg_Y x₁ y₁ :=
by { convert hy, exact Y_eq_of_Y_ne h₁ h₂ hx hy }

include hx

lemma add_polynomial_of_ne :
  W.add_polynomial x₁ y₁ (grad_of_ne x₁ x₂ y₁ y₂)
    = -(X - C x₁) * (X - C x₂) * (X - C (W.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂)) :=
begin
  rw [equation_iff] at h₁ h₂,
  rw [← sub_ne_zero] at hx,
  rw [add_polynomial_eq, neg_eq_iff_neg_eq, neg_mul, neg_mul, neg_neg, cubic.prod_X_sub_C_eq,
      cubic.to_poly_injective],
  ext,
  { refl },
  { simp only [add_X],
    ring1 },
  { apply mul_right_injective₀ hx,
    linear_combination h₁ - h₂ with { normalization_tactic := `[field_simp [hx], ring1] } },
  { apply mul_right_injective₀ hx,
    linear_combination x₁ * h₂ - x₂ * h₁
      with { normalization_tactic := `[field_simp [hx], ring1] } }
end

lemma derivative_add_polynomial_of_ne :
  derivative (W.add_polynomial x₁ y₁ $ grad_of_ne x₁ x₂ y₁ y₂)
    = -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂))
        + (X - C x₂) * (X - C (W.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂))) :=
by { rw [add_polynomial_of_ne h₁ h₂ hx], derivative_simp, ring1 }

/-- The addition of two affine points in `W` with distinct $X$-coordinates,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `W`. -/
lemma equation_add_of_ne' :
  W.equation (W.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂)
    (W.add_Y' x₁ x₂ y₁ $ grad_of_ne x₁ x₂ y₁ y₂) :=
by { rw [equation_add_iff, add_polynomial_of_ne h₁ h₂ hx], eval_simp, rw [sub_self, mul_zero] }

/-- The addition of two affine points in `W` with distinct $X$-coordinates lies in `W`. -/
lemma equation_add_of_ne :
  W.equation (W.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂) (W.add_Y x₁ x₂ y₁ $ grad_of_ne x₁ x₂ y₁ y₂) :=
equation_neg $ equation_add_of_ne' h₁ h₂ hx

include h₁' h₂'

/-- The addition of two nonsingular points in `W` with distinct $X$-coordinates,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, is nonsingular. -/
lemma nonsingular_add_of_ne' :
  W.nonsingular (W.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂)
    (W.add_Y' x₁ x₂ y₁ $ grad_of_ne x₁ x₂ y₁ y₂) :=
begin
  by_cases hx₁ : W.add_X x₁ x₂ (grad_of_ne x₁ x₂ y₁ y₂) = x₁,
  { rwa [add_Y', hx₁, sub_self, mul_zero, zero_add] },
  { by_cases hx₂ : W.add_X x₁ x₂ (grad_of_ne x₁ x₂ y₁ y₂) = x₂,
    { rwa [add_Y', ← neg_sub, mul_neg, hx₂, grad_of_ne, div_mul_cancel _ $ sub_ne_zero_of_ne hx,
           neg_sub, sub_add_cancel] },
    { apply nonsingular_add_of_eval_derivative_ne_zero,
      rw [derivative_add_polynomial_of_ne h₁ h₂ hx],
      eval_simp,
      simpa only [neg_ne_zero, sub_self, mul_zero, add_zero]
        using mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂) } }
end

/-- The addition of two nonsingular points in `W` with distinct $X$-coordinates is nonsingular. -/
lemma nonsingular_add_of_ne :
  W.nonsingular (W.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂)
    (W.add_Y x₁ x₂ y₁ $ grad_of_ne x₁ x₂ y₁ y₂) :=
nonsingular_neg $ nonsingular_add_of_ne' h₁ h₂ h₁' h₂' hx

omit h₁ h₂ h₁' h₂' hx

namespace point

open_locale classical

/-- The addition of two nonsingular rational points.

Given two nonsingular rational points `P` and `Q`, use `P + Q` instead of `add P Q`. -/
noncomputable def add : W.point → W.point → W.point
| 0                          P                          := P
| P                          0                          := P
| (@some _ _ _ x₁ y₁ h₁ h₁') (@some _ _ _ x₂ y₂ h₂ h₂') :=
if hx : x₁ = x₂ then if hy : y₁ = W.neg_Y x₂ y₂ then 0
else some (equation_add_of_eq h₁ $ Y_ne_of_Y_ne h₁ h₂ hx hy)
  (nonsingular_add_of_eq h₁ h₁' $ Y_ne_of_Y_ne h₁ h₂ hx hy)
else some (equation_add_of_ne h₁ h₂ hx) (nonsingular_add_of_ne h₁ h₂ h₁' h₂' hx)

noncomputable instance : has_add W.point := ⟨add⟩

@[simp] lemma add_def (P Q : W.point) : P.add Q = P + Q := rfl

noncomputable instance : add_zero_class W.point :=
⟨0, (+), by rintro (_ | _); refl, by rintro (_ | _); refl⟩

@[simp] lemma some_add_some_of_y_eq (hx : x₁ = x₂) (hy : y₁ = W.neg_Y x₂ y₂) :
  some h₁ h₁' + some h₂ h₂' = 0 :=
by rw [← add_def, add, dif_pos hx, dif_pos hy]

@[simp] lemma some_add_self_of_y_eq (hy : y₁ = W.neg_Y x₁ y₁) : some h₁ h₁' + some h₁ h₁' = 0 :=
some_add_some_of_y_eq h₁ h₁ h₁' h₁' rfl hy

@[simp] lemma some_add_some_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) :
  some h₁ h₁' + some h₂ h₂'
    = some (equation_add_of_eq h₁ $ Y_ne_of_Y_ne h₁ h₂ hx hy)
      (nonsingular_add_of_eq h₁ h₁' $ Y_ne_of_Y_ne h₁ h₂ hx hy) :=
by rw [← add_def, add, dif_pos hx, dif_neg hy]

lemma some_add_some_of_y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) :
  some h₁ h₁' + some h₂ h₂'
    = -some (equation_add_of_eq' h₁ $ Y_ne_of_Y_ne h₁ h₂ hx hy)
      (nonsingular_add_of_eq' h₁ h₁' $ Y_ne_of_Y_ne h₁ h₂ hx hy) :=
some_add_some_of_y_ne h₁ h₂ h₁' h₂' hx hy

@[simp] lemma some_add_self_of_y_ne :
  some h₁ h₁' + some h₁ h₁'
    = some (equation_add_of_eq h₁ $ Y_ne_of_Y_ne h₁ h₁ rfl hy)
      (nonsingular_add_of_eq h₁ h₁' $ Y_ne_of_Y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ h₁' h₁' rfl hy

lemma some_add_self_of_y_ne' :
  some h₁ h₁' + some h₁ h₁'
    = -some (equation_add_of_eq' h₁ $ Y_ne_of_Y_ne h₁ h₁ rfl hy)
      (nonsingular_add_of_eq' h₁ h₁' $ Y_ne_of_Y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ h₁' h₁' rfl hy

@[simp] lemma some_add_some_of_x_ne :
  some h₁ h₁' + some h₂ h₂'
    = some (equation_add_of_ne h₁ h₂ hx) (nonsingular_add_of_ne h₁ h₂ h₁' h₂' hx) :=
by rw [← add_def, add, dif_neg hx]

lemma some_add_some_of_x_ne' : some h₁ h₁' + some h₂ h₂'
  = -some (equation_add_of_ne' h₁ h₂ hx) (nonsingular_add_of_ne' h₁ h₂ h₁' h₂' hx) :=
some_add_some_of_x_ne h₁ h₂ h₁' h₂' hx

/-! ### The axioms for nonsingular rational points on a Weierstrass curve -/

@[simp] lemma add_eq_zero (P Q : W.point) : P + Q = 0 ↔ P = -Q :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | @⟨x₁, y₁, h₁, h₁'⟩, _ | @⟨x₂, y₂, h₂, h₂'⟩⟩,
  any_goals { refl },
  { rw [zero_def, zero_add, eq_neg_iff_eq_neg, neg_zero] },
  { simp only [neg_some],
    split,
    { intro h,
      by_cases hx : x₁ = x₂,
      { by_cases hy : y₁ = W.neg_Y x₂ y₂,
        { exact ⟨hx, hy⟩ },
        { rw [some_add_some_of_y_ne h₁ h₂ h₁' h₂' hx hy] at h,
          contradiction } },
      { rw [some_add_some_of_x_ne h₁ h₂ h₁' h₂' hx] at h,
        contradiction } },
    { exact λ ⟨hx, hy⟩, some_add_some_of_y_eq h₁ h₂ h₁' h₂' hx hy } }
end

@[simp] lemma add_neg_eq_zero (P Q : W.point) : P + -Q = 0 ↔ P = Q := by rw [add_eq_zero, neg_neg]

@[simp] lemma add_left_neg (P : W.point) : -P + P = 0 := by rw [add_eq_zero]

lemma add_comm (P Q : W.point) : P + Q = Q + P :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | @⟨x₁, y₁, h₁, h₁'⟩, _ | @⟨x₂, y₂, h₂, h₂'⟩⟩,
  any_goals { refl },
  by_cases hx : x₁ = x₂,
  { by_cases hy : y₁ = W.neg_Y x₂ y₂,
    { rw [some_add_some_of_y_eq h₁ h₂ h₁' h₂' hx hy,
          some_add_some_of_y_eq h₂ h₁ h₂' h₁' hx.symm $ by { simp only [neg_Y, hx, hy], ring1 }] },
    { simp only [hx, Y_eq_of_Y_ne h₁ h₂ hx hy] } },
  { rw [some_add_some_of_x_ne' h₁ h₂ h₁' h₂' hx,
        some_add_some_of_x_ne' h₂ h₁ h₂' h₁' $ ne.symm hx, neg_inj],
    field_simp [sub_ne_zero_of_ne hx, sub_ne_zero_of_ne (ne.symm hx)],
    exact ⟨by ring1, by ring1⟩ }
end

end point

end addition

end weierstrass_curve
