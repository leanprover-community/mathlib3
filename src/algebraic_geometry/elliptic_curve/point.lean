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
    between $E$ and the line through $\mathcal{O}$ and $P$, which exists by Bézout's theorem.
    Explicitly, if $P = (x, y)$, then $-P := (x, -y - a_1x - a_3)$.
 * Given two points $P$ and $Q$, their addition $P + Q$ is defined to be the negation of the unique
    third point of intersection between $E$ and the line through $P$ and $Q$, which again exists by
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

private meta def eval_simp : tactic unit :=
`[simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow]]

private meta def C_simp : tactic unit :=
`[simp only [C_1, C_bit0, C_neg, C_add, C_sub, C_mul, C_pow]]

namespace elliptic_curve

open polynomial weierstrass_curve

open_locale polynomial

universe u

section basic

/-! ### The type of rational points on an elliptic curve -/

variables {F : Type u} [comm_ring F] (E : elliptic_curve F) (x y : F)

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

/-- The $Y$-coordinate of the negation of an affine point. -/
@[simp] def neg_Y : F := -y - E.a₁ * x - E.a₃

lemma neg_Y_neg_Y : -E.neg_Y x y - E.a₁ * x - E.a₃ = y := by { rw [neg_Y], ring1 }

/-- The polynomial $-Y - a_1X - a_3$ associated to negation. -/
noncomputable def neg_polynomial : F[X][X] := -X - C (C E.a₁ * X) - C (C E.a₃)

lemma neg_Y_eq_eval : E.neg_Y x y = eval x (eval (C y) E.neg_polynomial) :=
by simp only [neg_Y, neg_polynomial, eval_C, eval_X, eval_neg, eval_sub, eval_mul]

variables {E x y} (h : E.equation x y)

include h

/-- The negation of an affine point in `E` lies in `E`. -/
lemma equation_neg : E.equation x $ E.neg_Y x y :=
by { rw [equation_iff] at h, rw [equation_iff, neg_Y, ← h], ring1 }

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

end basic

variables {F : Type u} [field F] (E : elliptic_curve F) (x₁ x₂ y₁ y₂ L : F)

section addition

/-! ### The addition law on rational points on an elliptic curve -/

/-- The $X$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$,
where the line through them is not vertical and has gradient $L$.
This depends on `E`, and has the argument order $x_1$, $x_2$, and $L$. -/
@[simp] def add_X : F := L ^ 2 + E.a₁ * L - E.a₂ - x₁ - x₂

/-- The $Y$-coordinate, before applying the final negation, of the addition of two affine points
$(x_1, y_1)$ and $(x_2, y_2)$, where the line through them is not vertical and has gradient $L$.
This depends on `E`, and has the argument order $x_1$, $x_2$, $y_1$, and $L$. -/
@[simp] def add_Y' : F := L * (E.add_X x₁ x₂ L - x₁) + y₁

/-- The $Y$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$,
where the line through them is not vertical and has gradient $L$.
This depends on `E`, and has the argument order $x_1$, $x_2$, $y_1$, and $L$.  -/
@[simp] def add_Y : F := -E.add_Y' x₁ x₂ y₁ L - E.a₁ * E.add_X x₁ x₂ L - E.a₃

/-- The polynomial obtained by substituting the line $Y := L*(X - x_1) + y_1$, with a gradient of
$L$ and contains a point $(x_1, y_1)$ of `E`, into the polynomial $E(X, Y)$ associated to `E`.
If such a line intersects $E$ at a point $(x_2, y_2)$ of `E`, then the roots of this polynomial are
precisely $x_1$, $x_2$, and the $X$-coordinate of the addition of $(x_1, y_1)$ and $(x_2, y_2)$. -/
noncomputable def add_polynomial : F[X] := eval (C L * (X - C x₁) + C y₁) E.polynomial

lemma add_polynomial_eq : E.add_polynomial x₁ y₁ L = -cubic.to_poly
  ⟨1, -L ^ 2 - E.a₁ * L + E.a₂,
    2 * x₁ * L ^ 2 + (E.a₁ * x₁ - 2 * y₁ - E.a₃) * L + (-E.a₁ * y₁ + E.a₄),
    -x₁ ^ 2 * L ^ 2 + (2 * x₁ * y₁ + E.a₃ * x₁) * L - (y₁ ^ 2 + E.a₃ * y₁ - E.a₆)⟩ :=
by { rw [add_polynomial, weierstrass_curve.polynomial, cubic.to_poly], eval_simp, C_simp, ring1 }

lemma equation_add_iff :
  E.equation (E.add_X x₁ x₂ L) (E.add_Y' x₁ x₂ y₁ L)
    ↔ eval (E.add_X x₁ x₂ L) (E.add_polynomial x₁ y₁ L) = 0 :=
by { rw [equation, add_Y', add_polynomial, weierstrass_curve.polynomial], eval_simp }

/-- The gradient of the tangent line of `E` at an affine point $(x_1, y_1)$. This is not
well-defined only in the case of $y_1 = -y_1 - a_1x_1 - a_3$, where the tangent is vertical.
This depends on `E`, and has the argument order $x_1$ and $y_1$. -/
@[simp] def grad_of_eq : F := (3 * x₁ ^ 2 + 2 * E.a₂ * x₁ + E.a₄ - E.a₁ * y₁) / (y₁ - E.neg_Y x₁ y₁)

lemma grad_of_eq_eq_eval :
  E.grad_of_eq x₁ y₁
    = -eval x₁ (eval (C y₁) E.polynomial_X) / eval x₁ (eval (C y₁) E.polynomial_Y) :=
by { rw [grad_of_eq, eval_polynomial_X, neg_sub], congr' 1, rw [neg_Y, eval_polynomial_Y], ring1 }

/-- The gradient of the line through two affine points $(x_1, y_1)$ and $(x_2, y_2)$. This is not
well-defined only in the case of $x_1 = x_2$, where the line is a tangent or is vertical.
This does not depend on `E`, and has the argument order $x_1$, $x_2$, $y_1$, and $y_2$. -/
@[simp] def grad_of_ne : F := (y₁ - y₂) / (x₁ - x₂)

variables {E x₁ x₂ y₁ y₂} (h₁ : E.equation x₁ y₁) (h₂ : E.equation x₂ y₂)

include h₁

lemma add_polynomial_eq_of_eq (hy : y₁ ≠ E.neg_Y x₁ y₁) :
  E.add_polynomial x₁ y₁ (E.grad_of_eq x₁ y₁)
    = -(X - C x₁) * (X - C x₁) * (X - C (E.add_X x₁ x₁ $ E.grad_of_eq x₁ y₁)) :=
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

/-- The doubling of an affine point in `E` whose tangent is not vertical,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `E`. -/
lemma equation_add_of_eq' (hy : y₁ ≠ E.neg_Y x₁ y₁) :
  E.equation (E.add_X x₁ x₁ $ E.grad_of_eq x₁ y₁) (E.add_Y' x₁ x₁ y₁ $ E.grad_of_eq x₁ y₁) :=
by { rw [equation_add_iff, add_polynomial_eq_of_eq h₁ hy], eval_simp, rw [sub_self, mul_zero] }

/-- The doubling of an affine point in `E` whose tangent is not vertical lies in `E`. -/
lemma equation_add_of_eq (hy : y₁ ≠ E.neg_Y x₁ y₁) :
  E.equation (E.add_X x₁ x₁ $ E.grad_of_eq x₁ y₁) (E.add_Y x₁ x₁ y₁ $ E.grad_of_eq x₁ y₁) :=
equation_neg $ equation_add_of_eq' h₁ hy

include h₂

lemma add_polynomial_eq_of_ne (hx : x₁ ≠ x₂) :
  E.add_polynomial x₁ y₁ (grad_of_ne x₁ x₂ y₁ y₂)
    = -(X - C x₁) * (X - C x₂) * (X - C (E.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂)) :=
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

/-- The addition of two affine points in `E` with distinct $X$-coordinates,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `E`. -/
lemma equation_add_of_ne' (hx : x₁ ≠ x₂) :
  E.equation (E.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂)
    (E.add_Y' x₁ x₂ y₁ $ grad_of_ne x₁ x₂ y₁ y₂) :=
by { rw [equation_add_iff, add_polynomial_eq_of_ne h₁ h₂ hx], eval_simp, rw [sub_self, mul_zero] }

/-- The addition of two affine points in `E` with distinct $X$-coordinates lies in `E`. -/
lemma equation_add_of_ne (hx : x₁ ≠ x₂) :
  E.equation (E.add_X x₁ x₂ $ grad_of_ne x₁ x₂ y₁ y₂) (E.add_Y x₁ x₂ y₁ $ grad_of_ne x₁ x₂ y₁ y₂) :=
equation_neg $ equation_add_of_ne' h₁ h₂ hx

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
else some $ equation_add_of_eq h₁ $ y_ne_of_y_ne h₁ h₂ hx hy
else some $ equation_add_of_ne h₁ h₂ hx

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
  some h₁ + some h₂ = some (equation_add_of_eq h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
by rw [← add_def, add, dif_pos hx, dif_neg hy]

lemma some_add_some_of_y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ E.neg_Y x₂ y₂) :
  some h₁ + some h₂ = -some (equation_add_of_eq' h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
some_add_some_of_y_ne h₁ h₂ hx hy

@[simp] lemma some_add_self_of_y_ne (hy : y₁ ≠ E.neg_Y x₁ y₁) :
  some h₁ + some h₁ = some (equation_add_of_eq h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

lemma some_add_self_of_y_ne' (hy : y₁ ≠ E.neg_Y x₁ y₁) :
  some h₁ + some h₁ = -some (equation_add_of_eq' h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_x_ne (hx : x₁ ≠ x₂) :
  some h₁ + some h₂ = some (equation_add_of_ne h₁ h₂ hx) :=
by rw [← add_def, add, dif_neg hx]

lemma some_add_some_of_x_ne' (hx : x₁ ≠ x₂) :
  some h₁ + some h₂ = -some (equation_add_of_ne' h₁ h₂ hx) :=
some_add_some_of_x_ne h₁ h₂ hx

end point

end addition

section group

/-! ### The axioms for rational points on an elliptic curve -/

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
          some_add_some_of_y_eq h₂ h₁ hx.symm $ by { simp only [neg_Y, hx, hy], ring1 }] },
    { simp only [hx, y_eq_of_y_ne h₁ h₂ hx hy] } },
  { rw [some_add_some_of_x_ne' h₁ h₂ hx, some_add_some_of_x_ne' h₂ h₁ $ ne.symm hx, neg_inj],
    field_simp [sub_ne_zero_of_ne hx, sub_ne_zero_of_ne (ne.symm hx)],
    exact ⟨by ring1, by ring1⟩ }
end

end point

end group

end elliptic_curve
