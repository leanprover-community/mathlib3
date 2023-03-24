/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.elliptic_curve.weierstrass
import field_theory.galois -- temporary import to enable point notation
import ring_theory.class_group

/-!
# The group of nonsingular rational points on a Weierstrass curve over a field

This file defines the type of nonsingular rational points on a Weierstrass curve over a field and
(TODO) proves that it forms an abelian group under a geometric secant-and-tangent process.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A rational point on `W` is simply a point
$[A:B:C]$ defined over `F` in the projective plane satisfying the homogeneous cubic equation
$B^2C + a_1ABC + a_3BC^2 = A^3 + a_2A^2C + a_4AC^2 + a_6C^3$. Any such point either lies in the
affine chart $C \ne 0$ and satisfies the Weierstrass equation obtained by setting $X := A/C$ and
$Y := B/C$, or is the unique point at infinity $0 := [0:1:0]$ when $C = 0$. With this new
description, a nonsingular rational point on `W` is either $0$ or an affine point $(x, y)$ where
the partial derivatives $W_X(X, Y)$ and $W_Y(X, Y)$ do not vanish simultaneously. For a field
extension `K` of `F`, a `K`-rational point is simply a rational point on `W` base changed to `K`.

The set of nonsingular rational points forms an abelian group under a secant-and-tangent process.
 * The identity rational point is `0`.
 * Given a nonsingular rational point `P`, its negation `-P` is defined to be the unique third
    point of intersection between `W` and the line through `0` and `P`.
    Explicitly, if `P` is $(x, y)$, then `-P` is $(x, -y - a_1x - a_3)$.
 * Given two points `P` and `Q`, their addition `P + Q` is defined to be the negation of the unique
    third point of intersection between `W` and the line `L` through `P` and `Q`.
    Explicitly, let `P` be $(x_1, y_1)$ and let `Q` be $(x_2, y_2)$.
      * If $x_1 = x_2$ and $y_1 = -y_2 - a_1x_2 - a_3$, then `L` is vertical and `P + Q` is `0`.
      * If $x_1 = x_2$ and $y_1 \ne -y_2 - a_1x_2 - a_3$, then `L` is the tangent of `W` at `P = Q`,
        and has slope $\ell := (3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$.
      * Otherwise $x_1 \ne x_2$, then `L` is the secant of `W` through `P` and `Q`, and has slope
        $\ell := (y_1 - y_2) / (x_1 - x_2)$.
    In the latter two cases, the $X$-coordinate of `P + Q` is then the unique third solution of the
    equation obtained by substituting the line $Y = \ell(X - x_1) + y_1$ into the Weierstrass
    equation, and can be written down explicitly as $x := \ell^2 + a_1\ell - a_2 - x_1 - x_2$ by
    inspecting the $X^2$ terms. The $Y$-coordinate of `P + Q`, after applying the final negation
    that maps $Y$ to $-Y - a_1X - a_3$, is precisely $y := -(\ell(x - x_1) + y_1) - a_1x - a_3$.
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

private meta def map_simp : tactic unit :=
`[simp only [map_one, map_bit0, map_bit1, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀]]

private meta def eval_simp : tactic unit :=
`[simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow]]

private meta def C_simp : tactic unit :=
`[simp only [C_1, C_bit0, C_bit1, C_neg, C_add, C_sub, C_mul, C_pow]]

private meta def derivative_simp : tactic unit :=
`[simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
             derivative_sub, derivative_mul, derivative_sq]]

universes u v w

namespace weierstrass_curve

open polynomial

open_locale polynomial polynomial_polynomial

section basic

/-! ### Polynomials associated to nonsingular rational points on a Weierstrass curve -/

variables {R : Type u} [comm_ring R] (W : weierstrass_curve R) (A : Type v) [comm_ring A]
  [algebra R A] (B : Type w) [comm_ring B] [algebra R B] [algebra A B] [is_scalar_tower R A B]
  (x₁ x₂ y₁ y₂ L : R)

/-- The polynomial $-Y - a_1X - a_3$ associated to negation. -/
noncomputable def neg_polynomial : R[X][Y] := -Y - C (C W.a₁ * X + C W.a₃)

/-- The $Y$-coordinate of the negation of an affine point in `W`.

This depends on `W`, and has argument order: $x_1$, $y_1$. -/
@[simp] def neg_Y : R := -y₁ - W.a₁ * x₁ - W.a₃

lemma neg_Y_neg_Y : W.neg_Y x₁ (W.neg_Y x₁ y₁) = y₁ := by { simp only [neg_Y], ring1 }

lemma base_change_neg_Y :
  (W.base_change A).neg_Y (algebra_map R A x₁) (algebra_map R A y₁)
    = algebra_map R A (W.neg_Y x₁ y₁) :=
by { simp only [neg_Y], map_simp, refl }

lemma base_change_neg_Y_of_base_change (x₁ y₁ : A) :
  (W.base_change B).neg_Y (algebra_map A B x₁) (algebra_map A B y₁)
    = algebra_map A B ((W.base_change A).neg_Y x₁ y₁) :=
by rw [← base_change_neg_Y, base_change_base_change]

@[simp] lemma eval_neg_polynomial : (W.neg_polynomial.eval $ C y₁).eval x₁ = W.neg_Y x₁ y₁ :=
by { rw [neg_Y, sub_sub, neg_polynomial], eval_simp }

/-- The polynomial $L(X - x_1) + y_1$ associated to the line $Y = L(X - x_1) + y_1$,
with a slope of $L$ that passes through an affine point $(x_1, y_1)$.

This does not depend on `W`, and has argument order: $x_1$, $y_1$, $L$. -/
noncomputable def line_polynomial : R[X] := C L * (X - C x₁) + C y₁

/-- The polynomial obtained by substituting the line $Y = L(X - x_1) + y_1$, with a slope of $L$
that passes through an affine point $(x_1, y_1)$, into the polynomial $W(X, Y)$ associated to `W`.
If such a line intersects `W` at another point $(x_2, y_2)$, then the roots of this polynomial are
precisely $x_1$, $x_2$, and the $X$-coordinate of the addition of $(x_1, y_1)$ and $(x_2, y_2)$.

This depends on `W`, and has argument order: $x_1$, $y_1$, $L$. -/
noncomputable def add_polynomial : R[X] := W.polynomial.eval $ line_polynomial x₁ y₁ L

lemma add_polynomial_eq : W.add_polynomial x₁ y₁ L = -cubic.to_poly
  ⟨1, -L ^ 2 - W.a₁ * L + W.a₂,
    2 * x₁ * L ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * L + (-W.a₁ * y₁ + W.a₄),
    -x₁ ^ 2 * L ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * L - (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)⟩ :=
by { rw [add_polynomial, line_polynomial, weierstrass_curve.polynomial, cubic.to_poly], eval_simp,
     C_simp, ring1 }

/-- The $X$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $L$. -/
@[simp] def add_X : R := L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂

lemma base_change_add_X :
  (W.base_change A).add_X (algebra_map R A x₁) (algebra_map R A x₂) (algebra_map R A L)
    = algebra_map R A (W.add_X x₁ x₂ L) :=
by { simp only [add_X], map_simp, refl }

lemma base_change_add_X_of_base_change (x₁ x₂ L : A) :
  (W.base_change B).add_X (algebra_map A B x₁) (algebra_map A B x₂) (algebra_map A B L)
    = algebra_map A B ((W.base_change A).add_X x₁ x₂ L) :=
by rw [← base_change_add_X, base_change_base_change]

/-- The $Y$-coordinate, before applying the final negation, of the addition of two affine points
$(x_1, y_1)$ and $(x_2, y_2)$, where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $L$. -/
@[simp] def add_Y' : R := L * (W.add_X x₁ x₂ L - x₁) + y₁

lemma base_change_add_Y' :
  (W.base_change A).add_Y' (algebra_map R A x₁) (algebra_map R A x₂) (algebra_map R A y₁)
    (algebra_map R A L) = algebra_map R A (W.add_Y' x₁ x₂ y₁ L) :=
by { simp only [add_Y', base_change_add_X], map_simp }

lemma base_change_add_Y'_of_base_change (x₁ x₂ y₁ L : A) :
  (W.base_change B).add_Y' (algebra_map A B x₁) (algebra_map A B x₂) (algebra_map A B y₁)
    (algebra_map A B L) = algebra_map A B ((W.base_change A).add_Y' x₁ x₂ y₁ L) :=
by rw [← base_change_add_Y', base_change_base_change]

/-- The $Y$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $L$. -/
@[simp] def add_Y : R := W.neg_Y (W.add_X x₁ x₂ L) (W.add_Y' x₁ x₂ y₁ L)

lemma base_change_add_Y :
  (W.base_change A).add_Y (algebra_map R A x₁) (algebra_map R A x₂) (algebra_map R A y₁)
    (algebra_map R A L) = algebra_map R A (W.add_Y x₁ x₂ y₁ L) :=
by simp only [add_Y, base_change_add_Y', base_change_add_X, base_change_neg_Y]

lemma base_change_add_Y_of_base_change (x₁ x₂ y₁ L : A) :
  (W.base_change B).add_Y (algebra_map A B x₁) (algebra_map A B x₂) (algebra_map A B y₁)
    (algebra_map A B L) = algebra_map A B ((W.base_change A).add_Y x₁ x₂ y₁ L) :=
by rw [← base_change_add_Y, base_change_base_change]

lemma equation_add_iff :
  W.equation (W.add_X x₁ x₂ L) (W.add_Y' x₁ x₂ y₁ L)
    ↔ (W.add_polynomial x₁ y₁ L).eval (W.add_X x₁ x₂ L) = 0 :=
by { rw [equation, add_Y', add_polynomial, line_polynomial, weierstrass_curve.polynomial],
     eval_simp }

lemma nonsingular_add_of_eval_derivative_ne_zero
  (hx' : W.equation (W.add_X x₁ x₂ L) (W.add_Y' x₁ x₂ y₁ L))
  (hx : (derivative $ W.add_polynomial x₁ y₁ L).eval (W.add_X x₁ x₂ L) ≠ 0) :
  W.nonsingular (W.add_X x₁ x₂ L) (W.add_Y' x₁ x₂ y₁ L) :=
begin
  rw [nonsingular, and_iff_right hx', add_Y', polynomial_X, polynomial_Y],
  eval_simp,
  contrapose! hx,
  rw [add_polynomial, line_polynomial, weierstrass_curve.polynomial],
  eval_simp,
  derivative_simp,
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one],
  eval_simp,
  linear_combination hx.left + L * hx.right with { normalization_tactic := `[norm_num1, ring1] }
end

/-! ### The type of nonsingular rational points on a Weierstrass curve -/

/-- A nonsingular rational point on a Weierstrass curve `W` over `R`. This is either the point at
infinity `weierstrass_curve.point.zero` or an affine point `weierstrass_curve.point.some` $(x, y)$
satisfying the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ of `W`. For an algebraic
extension `S` of `R`, the type of nonsingular `S`-rational points on `W` is denoted `W⟮S⟯`. -/
inductive point
| zero
| some {x y : R} (h : W.nonsingular x y)

localized "notation W⟮S⟯ := (W.base_change S).point" in weierstrass_curve

namespace point

instance : inhabited W.point := ⟨zero⟩

instance : has_zero W.point := ⟨zero⟩

@[simp] lemma zero_def : (zero : W.point) = 0 := rfl

end point

variables {W x₁ y₁}

lemma equation_neg_iff : W.equation x₁ (W.neg_Y x₁ y₁) ↔ W.equation x₁ y₁ :=
by { rw [equation_iff, equation_iff, neg_Y], congr' 2, ring1 }

lemma equation_neg_of (h : W.equation x₁ $ W.neg_Y x₁ y₁) : W.equation x₁ y₁ :=
equation_neg_iff.mp h

/-- The negation of an affine point in `W` lies in `W`. -/
lemma equation_neg (h : W.equation x₁ y₁) : W.equation x₁ $ W.neg_Y x₁ y₁ := equation_neg_iff.mpr h

lemma nonsingular_neg_iff : W.nonsingular x₁ (W.neg_Y x₁ y₁) ↔ W.nonsingular x₁ y₁ :=
begin
  rw [nonsingular_iff, equation_neg_iff, ← neg_Y, neg_Y_neg_Y, ← @ne_comm _ y₁, nonsingular_iff],
  exact and_congr_right' ((iff_congr not_and_distrib.symm not_and_distrib.symm).mpr $
                            not_iff_not_of_iff $ and_congr_left $ λ h, by rw [← h])
end

lemma nonsingular_neg_of (h : W.nonsingular x₁ $ W.neg_Y x₁ y₁) : W.nonsingular x₁ y₁ :=
nonsingular_neg_iff.mp h

/-- The negation of a nonsingular affine point in `W` is nonsingular. -/
lemma nonsingular_neg (h : W.nonsingular x₁ y₁) : W.nonsingular x₁ $ W.neg_Y x₁ y₁ :=
nonsingular_neg_iff.mpr h

namespace point

/-- The negation of a nonsingular rational point.

Given a nonsingular rational point `P`, use `-P` instead of `neg P`. -/
def neg : W.point → W.point
| 0        := 0
| (some h) := some $ nonsingular_neg h

instance : has_neg W.point := ⟨neg⟩

@[simp] lemma neg_def (P : W.point) : P.neg = -P := rfl

@[simp] lemma neg_zero : (-0 : W.point) = 0 := rfl

@[simp] lemma neg_some (h : W.nonsingular x₁ y₁) : -some h = some (nonsingular_neg h) := rfl

instance : has_involutive_neg W.point := ⟨neg, by { rintro (_ | _), { refl }, { simp, ring1 } }⟩

end point

end basic

section addition

/-! ### Slopes of lines through nonsingular rational points on a Weierstrass curve -/

open_locale classical

variables {F : Type u} [field F] (W : weierstrass_curve F) (K : Type v) [field K] [algebra F K]
  (x₁ x₂ y₁ y₂ : F)

/-- The slope of the line through two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`.
If $x_1 \ne x_2$, then this line is the secant of `W` through $(x_1, y_1)$ and $(x_2, y_2)$,
and has slope $(y_1 - y_2) / (x_1 - x_2)$. Otherwise, if $y_1 \ne -y_1 - a_1x_1 - a_3$,
then this line is the tangent of `W` at $(x_1, y_1) = (x_2, y_2)$, and has slope
$(3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$. Otherwise, this line is vertical,
and has undefined slope, in which case this function returns the value 0.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $y_2$. -/
noncomputable def slope : F :=
if hx : x₁ = x₂ then if hy : y₁ = W.neg_Y x₂ y₂ then 0
else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.neg_Y x₁ y₁)
else (y₁ - y₂) / (x₁ - x₂)

variables {W x₁ x₂ y₁ y₂} (h₁ : W.nonsingular x₁ y₁) (h₂ : W.nonsingular x₂ y₂)
  (h₁' : W.equation x₁ y₁) (h₂' : W.equation x₂ y₂)

@[simp] lemma slope_of_Y_eq (hx : x₁ = x₂) (hy : y₁ = W.neg_Y x₂ y₂) :
  W.slope x₁ x₂ y₁ y₂ = 0 :=
by rw [slope, dif_pos hx, dif_pos hy]

@[simp] lemma slope_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) :
  W.slope x₁ x₂ y₁ y₂ = (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.neg_Y x₁ y₁) :=
by rw [slope, dif_pos hx, dif_neg hy]

@[simp] lemma slope_of_X_ne (hx : x₁ ≠ x₂) : W.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
by rw [slope, dif_neg hx]

lemma slope_of_Y_ne_eq_eval (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) :
  W.slope x₁ x₂ y₁ y₂
    = -(W.polynomial_X.eval $ C y₁).eval x₁ / (W.polynomial_Y.eval $ C y₁).eval x₁ :=
by { rw [slope_of_Y_ne hx hy, eval_polynomial_X, neg_sub], congr' 1, rw [neg_Y, eval_polynomial_Y],
     ring1 }

lemma base_change_slope :
  (W.base_change K).slope (algebra_map F K x₁) (algebra_map F K x₂) (algebra_map F K y₁)
    (algebra_map F K y₂) = algebra_map F K (W.slope x₁ x₂ y₁ y₂) :=
begin
  by_cases hx : x₁ = x₂,
  { by_cases hy : y₁ = W.neg_Y x₂ y₂,
    { rw [slope_of_Y_eq hx hy, slope_of_Y_eq $ congr_arg _ hx, map_zero],
      { rw [hy, base_change_neg_Y] } },
    { rw [slope_of_Y_ne hx hy, slope_of_Y_ne $ congr_arg _ hx],
      { map_simp,
        simpa only [base_change_neg_Y] },
      { rw [base_change_neg_Y],
        contrapose! hy,
        exact no_zero_smul_divisors.algebra_map_injective F K hy } } },
  { rw [slope_of_X_ne hx, slope_of_X_ne],
    { map_simp },
    { contrapose! hx,
      exact no_zero_smul_divisors.algebra_map_injective F K hx } }
end

lemma base_change_slope_of_base_change {R : Type u} [comm_ring R] (W : weierstrass_curve R)
  (F : Type v) [field F] [algebra R F] (K : Type w) [field K] [algebra R K] [algebra F K]
  [is_scalar_tower R F K] (x₁ x₂ y₁ y₂ : F) :
  (W.base_change K).slope (algebra_map F K x₁) (algebra_map F K x₂) (algebra_map F K y₁)
    (algebra_map F K y₂) = algebra_map F K ((W.base_change F).slope x₁ x₂ y₁ y₂) :=
by rw [← base_change_slope, base_change_base_change]

include h₁' h₂'

lemma Y_eq_of_X_eq (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.neg_Y x₂ y₂ :=
begin
  rw [equation_iff] at h₁' h₂',
  rw [← sub_eq_zero, ← @sub_eq_zero _ _ y₁, ← mul_eq_zero, neg_Y],
  linear_combination h₁' - h₂' with { normalization_tactic := `[rw [hx], ring1] }
end

lemma Y_eq_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) : y₁ = y₂ :=
or.resolve_right (Y_eq_of_X_eq h₁' h₂' hx) hy

lemma add_polynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.neg_Y x₂ y₂) :
  W.add_polynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)
    = -((X - C x₁) * (X - C x₂) * (X - C (W.add_X x₁ x₂ $ W.slope x₁ x₂ y₁ y₂))) :=
begin
  rw [add_polynomial_eq, neg_inj, cubic.prod_X_sub_C_eq, cubic.to_poly_injective],
  by_cases hx : x₁ = x₂,
  { rcases ⟨hx, Y_eq_of_Y_ne h₁' h₂' hx (hxy hx)⟩ with ⟨rfl, rfl⟩,
    rw [equation_iff] at h₁' h₂',
    rw [slope_of_Y_ne rfl $ hxy rfl],
    rw [neg_Y, ← sub_ne_zero] at hxy,
    ext,
    { refl },
    { simp only [add_X],
      ring1 },
    { field_simp [hxy rfl],
      ring1 },
    { linear_combination -h₁' with { normalization_tactic := `[field_simp [hxy rfl], ring1] } } },
  { rw [equation_iff] at h₁' h₂',
    rw [slope_of_X_ne hx],
    rw [← sub_eq_zero] at hx,
    ext,
    { refl },
    { simp only [add_X],
      ring1 },
    { apply mul_right_injective₀ hx,
      linear_combination h₂' - h₁' with { normalization_tactic := `[field_simp [hx], ring1] } },
    { apply mul_right_injective₀ hx,
      linear_combination x₂ * h₁' - x₁ * h₂'
        with { normalization_tactic := `[field_simp [hx], ring1] } } }
end

lemma derivative_add_polynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.neg_Y x₂ y₂) :
  derivative (W.add_polynomial x₁ y₁ $ W.slope x₁ x₂ y₁ y₂)
    = -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W.add_X x₁ x₂ $ W.slope x₁ x₂ y₁ y₂))
        + (X - C x₂) * (X - C (W.add_X x₁ x₂ $ W.slope x₁ x₂ y₁ y₂))) :=
by { rw [add_polynomial_slope h₁' h₂' hxy], derivative_simp, ring1 }

/-! ### The addition law on nonsingular rational points on a Weierstrass curve -/

/-- The addition of two affine points in `W` on a sloped line,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `W`. -/
lemma equation_add' (hxy : x₁ = x₂ → y₁ ≠ W.neg_Y x₂ y₂) :
  W.equation (W.add_X x₁ x₂ $ W.slope x₁ x₂ y₁ y₂) (W.add_Y' x₁ x₂ y₁ $ W.slope x₁ x₂ y₁ y₂) :=
by { rw [equation_add_iff, add_polynomial_slope h₁' h₂' hxy], eval_simp,
     rw [neg_eq_zero, sub_self, mul_zero] }

/-- The addition of two affine points in `W` on a sloped line lies in `W`. -/
lemma equation_add (hxy : x₁ = x₂ → y₁ ≠ W.neg_Y x₂ y₂) :
  W.equation (W.add_X x₁ x₂ $ W.slope x₁ x₂ y₁ y₂) (W.add_Y x₁ x₂ y₁ $ W.slope x₁ x₂ y₁ y₂) :=
equation_neg $ equation_add' h₁' h₂' hxy

omit h₁' h₂'

include h₁ h₂

/-- The addition of two nonsingular affine points in `W` on a sloped line,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, is nonsingular. -/
lemma nonsingular_add' (hxy : x₁ = x₂ → y₁ ≠ W.neg_Y x₂ y₂) :
  W.nonsingular (W.add_X x₁ x₂ $ W.slope x₁ x₂ y₁ y₂) (W.add_Y' x₁ x₂ y₁ $ W.slope x₁ x₂ y₁ y₂) :=
begin
  by_cases hx₁ : W.add_X x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁,
  { rwa [add_Y', hx₁, sub_self, mul_zero, zero_add] },
  { by_cases hx₂ : W.add_X x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂,
    { by_cases hx : x₁ = x₂,
      { subst hx,
        contradiction },
      { rwa [add_Y', ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
             div_mul_cancel _ $ sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel] } },
    { apply W.nonsingular_add_of_eval_derivative_ne_zero _ _ _ _ (equation_add' h₁.1 h₂.1 hxy),
      rw [derivative_add_polynomial_slope h₁.left h₂.left hxy],
      eval_simp,
      simpa only [neg_ne_zero, sub_self, mul_zero, add_zero]
        using mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂) } }
end

/-- The addition of two nonsingular affine points in `W` on a sloped line is nonsingular. -/
lemma nonsingular_add (hxy : x₁ = x₂ → y₁ ≠ W.neg_Y x₂ y₂) :
  W.nonsingular (W.add_X x₁ x₂ $ W.slope x₁ x₂ y₁ y₂) (W.add_Y x₁ x₂ y₁ $ W.slope x₁ x₂ y₁ y₂) :=
nonsingular_neg $ nonsingular_add' h₁ h₂ hxy

omit h₁ h₂

namespace point

variables {h₁ h₂}

/-- The addition of two nonsingular rational points.

Given two nonsingular rational points `P` and `Q`, use `P + Q` instead of `add P Q`. -/
noncomputable def add : W.point → W.point → W.point
| 0                      P                      := P
| P                      0                      := P
| (@some _ _ _ x₁ y₁ h₁) (@some _ _ _ x₂ y₂ h₂) :=
if hx : x₁ = x₂ then if hy : y₁ = W.neg_Y x₂ y₂ then 0
else some $ nonsingular_add h₁ h₂ $ λ _, hy
else some $ nonsingular_add h₁ h₂ $ λ h, (hx h).elim

noncomputable instance : has_add W.point := ⟨add⟩

@[simp] lemma add_def (P Q : W.point) : P.add Q = P + Q := rfl

noncomputable instance : add_zero_class W.point :=
⟨0, (+), by rintro (_ | _); refl, by rintro (_ | _); refl⟩

@[simp] lemma some_add_some_of_Y_eq (hx : x₁ = x₂) (hy : y₁ = W.neg_Y x₂ y₂) :
  some h₁ + some h₂ = 0 :=
by rw [← add_def, add, dif_pos hx, dif_pos hy]

@[simp] lemma some_add_self_of_Y_eq (hy : y₁ = W.neg_Y x₁ y₁) : some h₁ + some h₁ = 0 :=
some_add_some_of_Y_eq rfl hy

@[simp] lemma some_add_some_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) :
  some h₁ + some h₂ = some (nonsingular_add h₁ h₂ $ λ _, hy) :=
by rw [← add_def, add, dif_pos hx, dif_neg hy]

lemma some_add_some_of_Y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ W.neg_Y x₂ y₂) :
  some h₁ + some h₂ = -some (nonsingular_add' h₁ h₂ $ λ _, hy) :=
some_add_some_of_Y_ne hx hy

@[simp] lemma some_add_self_of_Y_ne (hy : y₁ ≠ W.neg_Y x₁ y₁) :
  some h₁ + some h₁ = some (nonsingular_add h₁ h₁ $ λ _, hy) :=
some_add_some_of_Y_ne rfl hy

lemma some_add_self_of_Y_ne' (hy : y₁ ≠ W.neg_Y x₁ y₁) :
  some h₁ + some h₁ = -some (nonsingular_add' h₁ h₁ $ λ _, hy) :=
some_add_some_of_Y_ne rfl hy

@[simp] lemma some_add_some_of_X_ne (hx : x₁ ≠ x₂) :
  some h₁ + some h₂ = some (nonsingular_add h₁ h₂ $ λ h, (hx h).elim) :=
by rw [← add_def, add, dif_neg hx]

lemma some_add_some_of_X_ne' (hx : x₁ ≠ x₂) :
  some h₁ + some h₂ = -some (nonsingular_add' h₁ h₂ $ λ h, (hx h).elim) :=
some_add_some_of_X_ne hx

end point

end addition

section group

/-! ### The axioms for nonsingular rational points on a Weierstrass curve -/

variables {F : Type u} [field F] {W : weierstrass_curve F}

namespace point

@[simp] lemma add_eq_zero (P Q : W.point) : P + Q = 0 ↔ P = -Q :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | @⟨x₁, y₁, _⟩, _ | @⟨x₂, y₂, _⟩⟩,
  any_goals { refl },
  { rw [zero_def, zero_add, ← neg_eq_iff_eq_neg, neg_zero, eq_comm], },
  { simp only [neg_some],
    split,
    { intro h,
      by_cases hx : x₁ = x₂,
      { by_cases hy : y₁ = W.neg_Y x₂ y₂,
        { exact ⟨hx, hy⟩ },
        { rw [some_add_some_of_Y_ne hx hy] at h,
          contradiction } },
      { rw [some_add_some_of_X_ne hx] at h,
        contradiction } },
    { exact λ ⟨hx, hy⟩, some_add_some_of_Y_eq hx hy } }
end

@[simp] lemma add_left_neg (P : W.point) : -P + P = 0 := by rw [add_eq_zero]

@[simp] lemma neg_add_eq_zero (P Q : W.point) : -P + Q = 0 ↔ P = Q := by rw [add_eq_zero, neg_inj]

end point

end group

section base_change

/-! ### Nonsingular rational points on a base changed Weierstrass curve -/

variables {R : Type u} [comm_ring R] (W : weierstrass_curve R) (F : Type v) [field F] [algebra R F]
  (K : Type w) [field K] [algebra R K] [algebra F K] [is_scalar_tower R F K]

namespace point

open_locale weierstrass_curve

/-- The function from `W⟮F⟯` to `W⟮K⟯` induced by a base change from `F` to `K`. -/
def of_base_change_fun : W⟮F⟯ → W⟮K⟯
| 0        := 0
| (some h) := some $ (nonsingular_iff_base_change_of_base_change W F K _ _).mp h

/-- The group homomorphism from `W⟮F⟯` to `W⟮K⟯` induced by a base change from `F` to `K`. -/
@[simps] def of_base_change : W⟮F⟯ →+ W⟮K⟯ :=
{ to_fun    := of_base_change_fun W F K,
  map_zero' := rfl,
  map_add'  :=
  begin
    rintro (_ | @⟨x₁, y₁, _⟩) (_ | @⟨x₂, y₂, _⟩),
    any_goals { refl },
    by_cases hx : x₁ = x₂,
    { by_cases hy : y₁ = (W.base_change F).neg_Y x₂ y₂,
      { simp only [some_add_some_of_Y_eq hx hy, of_base_change_fun],
        rw [some_add_some_of_Y_eq $ congr_arg _ hx],
        { rw [hy, base_change_neg_Y_of_base_change] } },
      { simp only [some_add_some_of_Y_ne hx hy, of_base_change_fun],
        rw [some_add_some_of_Y_ne $ congr_arg _ hx],
        { simp only [base_change_add_X_of_base_change, base_change_add_Y_of_base_change,
                     base_change_slope_of_base_change],
          exact ⟨rfl, rfl⟩ },
        { rw [base_change_neg_Y_of_base_change],
          contrapose! hy,
          exact no_zero_smul_divisors.algebra_map_injective F K hy } } },
    { simp only [some_add_some_of_X_ne hx, of_base_change_fun],
      rw [some_add_some_of_X_ne],
      { simp only [base_change_add_X_of_base_change, base_change_add_Y_of_base_change,
                   base_change_slope_of_base_change],
        exact ⟨rfl, rfl⟩ },
      { contrapose! hx,
        exact no_zero_smul_divisors.algebra_map_injective F K hx } }
  end }

lemma of_base_change_injective : function.injective $ of_base_change W F K :=
begin
  rintro (_ | _) (_ | _) h,
  { refl },
  any_goals { contradiction },
  simp only,
  exact ⟨no_zero_smul_divisors.algebra_map_injective F K (some.inj h).left,
    no_zero_smul_divisors.algebra_map_injective F K (some.inj h).right⟩
end

end point

end base_change

end weierstrass_curve

namespace elliptic_curve

/-! ### Rational points on an elliptic curve -/

namespace point

variables {R : Type} [nontrivial R] [comm_ring R] (E : elliptic_curve R)

/-- An affine point on an elliptic curve `E` over `R`. -/
def mk {x y : R} (h : E.equation x y) : E.point := weierstrass_curve.point.some $ E.nonsingular h

end point

end elliptic_curve
