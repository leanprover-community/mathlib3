/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/

import algebra.cubic_discriminant
import ring_theory.adjoin_root
import tactic.linear_combination

/-!
# Weierstrass equations of elliptic curves

We give a working definition of an elliptic curve as a smooth Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map
is smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ for
some $a_i$ in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`.
If `R` is a field, this quantity divides the discriminant of a cubic polynomial whose roots over a
splitting field of `R` are precisely the x-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

 * `weierstrass_curve`: a Weierstrass curve over a commutative ring.
 * `weierstrass_curve.Δ`: the discriminant of a Weierstrass curve.
 * `weierstrass_curve.variable_change`: the Weierstrass curve induced by a change of variables.
 * `weierstrass_curve.base_change`: the Weierstrass curve base changed over an algebra.
 * `weierstrass_curve.two_torsion_polynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `weierstrass_curve.polynomial`: the polynomial associated to a Weierstrass curve.
 * `weierstrass_curve.equation`: the Weirstrass equation of a Weierstrass curve.
 * `weierstrass_curve.smooth`: the smoothness condition at a point on a Weierstrass curve.
 * `weierstrass_curve.coordinate_ring`: the coordinate ring of a Weierstrass curve.
 * `elliptic_curve`: an elliptic curve over a commutative ring.
 * `elliptic_curve.j`: the j-invariant of an elliptic curve.

## Main statements

 * `weierstrass_curve.two_torsion_polynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
 * `weierstrass_curve.smooth_of_Δ_ne_zero`: a Weierstrass curve is smooth at every point if its
    discriminant is non-zero.
 * `weierstrass_curve.coordinate_ring.is_domain`: the coordinate ring of a Weierstrass curve is
    an integral domain.
 * `elliptic_curve.variable_change_j`: the j-invariant of an elliptic curve is invariant under an
    admissible linear change of variables.

## Implementation notes

The definition of elliptic curves in this file makes sense for all commutative rings `R`, but it
only gives a type which can be beefed up to a category which is equivalent to the category of
elliptic curves over the spectrum $\mathrm{Spec}(R)$ of `R` in the case that `R` has trivial Picard
group $\mathrm{Pic}(R)$ or, slightly more generally, when its 12-torsion is trivial. The issue is
that for a general ring `R`, there might be elliptic curves over $\mathrm{Spec}(R)$ in the sense of
algebraic geometry which are not globally defined by a cubic equation valid over the entire base.

## References

 * [N Katz and B Mazur, *Arithmetic Moduli of Elliptic Curves*][katz_mazur]
 * [P Deligne, *Courbes Elliptiques: Formulaire (d'après J. Tate)*][deligne_formulaire]
 * [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

private meta def map_simp : tactic unit :=
`[simp only [map_one, map_bit0, map_bit1, map_neg, map_add, map_sub, map_mul, map_pow]]

private meta def eval_simp : tactic unit :=
`[simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow]]

universes u v

variable {R : Type u}

/-! ## Weierstrass curves -/

/-- A Weierstrass curve $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ with parameters $a_i$. -/
@[ext] structure weierstrass_curve (R : Type u) := (a₁ a₂ a₃ a₄ a₆ : R)

instance [inhabited R] : inhabited $ weierstrass_curve R :=
⟨⟨default, default, default, default, default⟩⟩

namespace weierstrass_curve

variables [comm_ring R] (W : weierstrass_curve R)

section quantity

/-! ### Standard quantities -/

/-- The `b₂` coefficient of a Weierstrass curve. -/
@[simp] def b₂ : R := W.a₁ ^ 2 + 4 * W.a₂

/-- The `b₄` coefficient of a Weierstrass curve. -/
@[simp] def b₄ : R := 2 * W.a₄ + W.a₁ * W.a₃

/-- The `b₆` coefficient of a Weierstrass curve. -/
@[simp] def b₆ : R := W.a₃ ^ 2 + 4 * W.a₆

/-- The `b₈` coefficient of a Weierstrass curve. -/
@[simp] def b₈ : R :=
W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2

lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by { simp only [b₂, b₄, b₆, b₈], ring1 }

/-- The `c₄` coefficient of a Weierstrass curve. -/
@[simp] def c₄ : R := W.b₂ ^ 2 - 24 * W.b₄

/-- The `c₆` coefficient of a Weierstrass curve. -/
@[simp] def c₆ : R := -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆

/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[simp] def Δ : R := -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆

lemma c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 :=
by { simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ], ring1 }

end quantity

section variable_change

/-! ### Variable changes -/

variables (u : Rˣ) (r s t : R)

/-- The Weierstrass curve over `R` induced by an admissible linear change of variables
$(x, y) \mapsto (u^2x + r, u^3y + u^2sx + t)$ for some $u \in R^\times$ and some $r, s, t \in R$. -/
@[simps] def variable_change : weierstrass_curve R :=
{ a₁ := ↑u⁻¹ * (W.a₁ + 2 * s),
  a₂ := ↑u⁻¹ ^ 2 * (W.a₂ - s * W.a₁ + 3 * r - s ^ 2),
  a₃ := ↑u⁻¹ ^ 3 * (W.a₃ + r * W.a₁ + 2 * t),
  a₄ := ↑u⁻¹ ^ 4 * (W.a₄ - s * W.a₃ + 2 * r * W.a₂ - (t + r * s) * W.a₁ + 3 * r ^ 2 - 2 * s * t),
  a₆ := ↑u⁻¹ ^ 6 * (W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁) }

@[simp] lemma variable_change_b₂ : (W.variable_change u r s t).b₂ = ↑u⁻¹ ^ 2 * (W.b₂ + 12 * r) :=
by { simp only [b₂, variable_change_a₁, variable_change_a₂], ring1 }

@[simp] lemma variable_change_b₄ :
  (W.variable_change u r s t).b₄ = ↑u⁻¹ ^ 4 * (W.b₄ + r * W.b₂ + 6 * r ^ 2) :=
by { simp only [b₂, b₄, variable_change_a₁, variable_change_a₃, variable_change_a₄], ring1 }

@[simp] lemma variable_change_b₆ :
  (W.variable_change u r s t).b₆ = ↑u⁻¹ ^ 6 * (W.b₆ + 2 * r * W.b₄ + r ^ 2 * W.b₂ + 4 * r ^ 3) :=
by { simp only [b₂, b₄, b₆, variable_change_a₃, variable_change_a₆], ring1 }

@[simp] lemma variable_change_b₈ :
  (W.variable_change u r s t).b₈
    = ↑u⁻¹ ^ 8 * (W.b₈ + 3 * r * W.b₆ + 3 * r ^ 2 * W.b₄ + r ^ 3 * W.b₂ + 3 * r ^ 4) :=
by { simp only [b₂, b₄, b₆, b₈, variable_change_a₁, variable_change_a₂, variable_change_a₃,
                variable_change_a₄, variable_change_a₆], ring1 }

@[simp] lemma variable_change_c₄ : (W.variable_change u r s t).c₄ = ↑u⁻¹ ^ 4 * W.c₄ :=
by { simp only [c₄, variable_change_b₂, variable_change_b₄], ring1 }

@[simp] lemma variable_change_c₆ : (W.variable_change u r s t).c₆ = ↑u⁻¹ ^ 6 * W.c₆ :=
by { simp only [c₆, variable_change_b₂, variable_change_b₄, variable_change_b₆], ring1 }

@[simp] lemma variable_change_Δ : (W.variable_change u r s t).Δ = ↑u⁻¹ ^ 12 * W.Δ :=
by { dsimp, ring1 }

end variable_change

section base_change

/-! ### Base changes -/

variables (A : Type v) [comm_ring A] [algebra R A]

/-- The Weierstrass curve over `R` base changed to `A`. -/
@[simps] def base_change : weierstrass_curve A :=
⟨algebra_map R A W.a₁, algebra_map R A W.a₂, algebra_map R A W.a₃, algebra_map R A W.a₄,
algebra_map R A W.a₆⟩

@[simp] lemma base_change_b₂ : (W.base_change A).b₂ = algebra_map R A W.b₂ :=
by { simp only [b₂, base_change_a₁, base_change_a₂], map_simp }

@[simp] lemma base_change_b₄ : (W.base_change A).b₄ = algebra_map R A W.b₄ :=
by { simp only [b₄, base_change_a₁, base_change_a₃, base_change_a₄], map_simp }

@[simp] lemma base_change_b₆ : (W.base_change A).b₆ = algebra_map R A W.b₆ :=
by { simp only [b₆, base_change_a₃, base_change_a₆], map_simp }

@[simp] lemma base_change_b₈ : (W.base_change A).b₈ = algebra_map R A W.b₈ :=
by { simp only [b₈, base_change_a₁, base_change_a₂, base_change_a₃, base_change_a₄, base_change_a₆],
     map_simp }

@[simp] lemma base_change_c₄ : (W.base_change A).c₄ = algebra_map R A W.c₄ :=
by { simp only [c₄, base_change_b₂, base_change_b₄], map_simp }

@[simp] lemma base_change_c₆ : (W.base_change A).c₆ = algebra_map R A W.c₆ :=
by { simp only [c₆, base_change_b₂, base_change_b₄, base_change_b₆], map_simp }

@[simp, nolint simp_nf] lemma base_change_Δ : (W.base_change A).Δ = algebra_map R A W.Δ :=
by { simp only [Δ, base_change_b₂, base_change_b₄, base_change_b₆, base_change_b₈], map_simp }

end base_change

section torsion_polynomial

/-! ### 2-torsion polynomials -/

/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant.
If `W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over
a splitting field of `R` are precisely the x-coordinates of the non-zero 2-torsion points of `W`. -/
def two_torsion_polynomial : cubic R := ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩

lemma two_torsion_polynomial_disc : W.two_torsion_polynomial.disc = 16 * W.Δ :=
by { dsimp [two_torsion_polynomial, cubic.disc], ring1 }

lemma two_torsion_polynomial_disc_is_unit [h2 : invertible (2 : R)] :
  is_unit W.two_torsion_polynomial.disc ↔ is_unit W.Δ :=
begin
  rw [two_torsion_polynomial_disc, is_unit.mul_iff, show (16 : R) = 2 ^ 4, by norm_num1],
  exact and_iff_right (is_unit_of_invertible $ 2 ^ 4)
end

end torsion_polynomial

section polynomial

/-! ### Weierstrass polynomials -/

open polynomial

open_locale polynomial

/-- The polynomial $W(X, Y) := Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$ associated to a
Weierstrass curve `W` over `R`. For ease of polynomial manipulation, this is represented as a term
of type `R[X][X]`, where the inner variable represents $X$ and the outer variable represents $Y$. -/
noncomputable def polynomial : R[X][X] :=
X ^ 2 + C (C W.a₁ * X + C W.a₃) * X - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

@[simp] lemma eval_polynomial (x y : R) :
  eval x (eval (C y) W.polynomial)
    = y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :=
by { simp only [polynomial], eval_simp, rw [add_mul, ← add_assoc] }

/-- The proposition that an affine point $(x, y)$ lies in `W`. In other words, $W(x, y) = 0$. -/
def equation (x y : R) : Prop := eval x (eval (C y) W.polynomial) = 0

lemma equation_iff' (x y : R) :
  W.equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
by rw [equation, eval_polynomial]

@[simp] lemma equation_iff (x y : R) :
  W.equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
by rw [equation_iff', sub_eq_zero]

/-- The partial derivative $W_X(X, Y)$ of $W(X, Y)$ with respect to $X$. -/
noncomputable def polynomial_X : R[X][X] :=
C (C W.a₁) * X - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)

@[simp] lemma eval_polynomial_X (x y : R) :
  eval x (eval (C y) W.polynomial_X) = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) :=
by { simp only [polynomial_X], eval_simp }

/-- The partial derivative $W_Y(X, Y)$ of $W(X, Y)$ with respect to $Y$. -/
noncomputable def polynomial_Y : R[X][X] := C (C 2) * X + C (C W.a₁ * X + C W.a₃)

@[simp] lemma eval_polynomial_Y (x y : R) :
  eval x (eval (C y) W.polynomial_Y) = 2 * y + W.a₁ * x + W.a₃ :=
by { simp only [polynomial_Y], eval_simp, rw [← add_assoc] }

/-- The proposition that an affine point $(x, y)$ on `W` is smooth or non-singular.
In other words, either $W_X(x, y) \ne 0$ or $W_Y(x, y) \ne 0$. -/
def smooth (x y : R) : Prop :=
eval x (eval (C y) W.polynomial_X) ≠ 0 ∨ eval x (eval (C y) W.polynomial_Y) ≠ 0

lemma smooth_iff' (x y : R) :
  W.smooth x y ↔ W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0 :=
by rw [smooth, eval_polynomial_X, eval_polynomial_Y]

@[simp] lemma smooth_iff (x y : R) :
  W.smooth x y ↔ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ≠ 0 ∨ y ≠ -y - W.a₁ * x - W.a₃ :=
by { rw [smooth_iff', ← neg_ne_zero, ← @sub_ne_zero _ _ y], congr' 3; ring1 }

/-- A Weierstrass curve is smooth at every point if its discriminant is non-zero. -/
lemma smooth_of_Δ_ne_zero {x y : R} (h : W.equation x y) (hΔ : W.Δ ≠ 0) : W.smooth x y :=
begin
  rw [equation_iff] at h,
  rw [Δ, b₂, b₄, b₆, b₈] at hΔ,
  rw [smooth_iff'],
  contrapose! hΔ,
  linear_combination
      (W.a₁ ^ 6 + 12 * W.a₁ ^ 4 * W.a₂ + 48 * W.a₁ ^ 2 * W.a₂ ^ 2 - 36 * W.a₁ ^ 3 * W.a₃
        + 72 * W.a₁ ^ 3 * y + 64 * W.a₂ ^ 3 - 144 * W.a₁ ^ 2 * W.a₄ + 32 * W.a₂ ^ 2 * x
        - 96 * W.a₂ * x ^ 2 + 272 * W.a₁ * W.a₂ * y + 504 * W.a₁ * x * y - 272 * W.a₂ * W.a₄
        - 288 * W.a₄ * x - 216 * W.a₃ * y + 432 * W.a₆) * h
    + (W.a₁ ^ 5 * y + 2 * W.a₁ ^ 3 * W.a₂ * W.a₃ - W.a₁ ^ 4 * W.a₄ + 12 * W.a₁ ^ 3 * W.a₂ * y
        + 16 * W.a₁ * W.a₂ ^ 2 * W.a₃ - 3 * W.a₁ ^ 2 * W.a₃ ^ 2 - 8 * W.a₁ ^ 2 * W.a₂ * W.a₄
        - 32 * W.a₂ ^ 3 * x + 32 * W.a₂ * x ^ 3 + 48 * W.a₁ * W.a₂ ^ 2 * y
        - 36 * W.a₁ ^ 2 * W.a₃ * y + 76 * W.a₁ ^ 2 * y ^ 2 - 16 * W.a₂ ^ 2 * W.a₄
        - 48 * W.a₁ * W.a₃ * W.a₄ + 72 * W.a₁ ^ 2 * W.a₆ + 144 * W.a₂ * W.a₄ * x + 96 * W.a₄ * x ^ 2
        + 160 * W.a₂ * W.a₃ * y - 224 * W.a₁ * W.a₄ * y + 240 * W.a₃ * x * y + 304 * W.a₂ * y ^ 2
        + 336 * x * y ^ 2 + 64 * W.a₄ ^ 2 - 16 * W.a₂ * W.a₆ - 144 * W.a₆ * x) * hΔ.left
    + (W.a₁ ^ 5 * W.a₂ * x + W.a₁ ^ 5 * x ^ 2 - W.a₁ ^ 6 * y - W.a₁ ^ 4 * W.a₂ * W.a₃
        + W.a₁ ^ 5 * W.a₄ + 12 * W.a₁ ^ 3 * W.a₂ ^ 2 * x - W.a₁ ^ 4 * W.a₃ * x
        + 12 * W.a₁ ^ 3 * W.a₂ * x ^ 2 - 12 * W.a₁ ^ 4 * W.a₂ * y + W.a₁ ^ 4 * x * y
        - 8 * W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ + W.a₁ ^ 3 * W.a₃ ^ 2 + 10 * W.a₁ ^ 3 * W.a₂ * W.a₄
        + 48 * W.a₁ * W.a₂ ^ 3 * x - 42 * W.a₁ ^ 2 * W.a₂ * W.a₃ * x - 3 * W.a₁ ^ 3 * W.a₄ * x
        + 48 * W.a₁ * W.a₂ ^ 2 * x ^ 2 - 36 * W.a₁ ^ 2 * W.a₃ * x ^ 2 - 48 * W.a₁ ^ 2 * W.a₂ ^ 2 * y
        + 37 * W.a₁ ^ 3 * W.a₃ * y + 84 * W.a₁ ^ 2 * W.a₂ * x * y + 72 * W.a₁ ^ 2 * x ^ 2 * y
        - 74 * W.a₁ ^ 3 * y ^ 2 - 16 * W.a₂ ^ 3 * W.a₃ + 36 * W.a₁ * W.a₂ * W.a₃ ^ 2
        + 32 * W.a₁ * W.a₂ ^ 2 * W.a₄ - 33 * W.a₁ ^ 2 * W.a₃ * W.a₄ + 27 * W.a₁ * W.a₃ ^ 2 * x
        - 168 * W.a₁ * W.a₂ * W.a₄ * x - 144 * W.a₁ * W.a₄ * x ^ 2 - 32 * W.a₂ ^ 3 * y
        - 72 * W.a₁ * W.a₂ * W.a₃ * y + 222 * W.a₁ ^ 2 * W.a₄ * y + 288 * W.a₂ ^ 2 * x * y
        - 108 * W.a₁ * W.a₃ * x * y + 840 * W.a₂ * x ^ 2 * y + 504 * x ^ 3 * y
        - 288 * W.a₁ * W.a₂ * y ^ 2 - 420 * W.a₁ * x * y ^ 2 - 27 * W.a₃ ^ 3
        + 72 * W.a₂ * W.a₃ * W.a₄ - 144 * W.a₁ * W.a₄ ^ 2 + 144 * W.a₁ * W.a₂ * W.a₆
        + 216 * W.a₁ * W.a₆ * x + 54 * W.a₃ ^ 2 * y + 288 * W.a₂ * W.a₄ * y + 312 * W.a₄ * x * y
        + 108 * W.a₃ * y ^ 2 - 216 * W.a₃ * W.a₆ - 216 * W.a₆ * y) * hΔ.right
  with { normalization_tactic := `[ring1] }
end

lemma polynomial_eq : W.polynomial = cubic.to_poly
  ⟨0, 1, cubic.to_poly ⟨0, 0, W.a₁, W.a₃⟩, cubic.to_poly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ :=
by { simp only [polynomial, cubic.to_poly, C_0, C_1, C_neg, C_add, C_mul], ring1 }

lemma polynomial_ne_zero [nontrivial R] : W.polynomial ≠ 0 :=
by { rw [polynomial_eq], exact cubic.ne_zero_of_b_ne_zero one_ne_zero }

lemma polynomial_nat_degree [nontrivial R] : W.polynomial.nat_degree = 2 :=
by { rw [polynomial_eq], exact cubic.nat_degree_of_b_ne_zero' one_ne_zero }

lemma polynomial_monic : W.polynomial.monic :=
by { nontriviality R, simpa only [polynomial_eq] using cubic.monic_of_b_eq_one' }

lemma polynomial_irreducible [nontrivial R] [no_zero_divisors R] : irreducible W.polynomial :=
begin
  by_contra h,
  rcases (W.polynomial_monic.not_irreducible_iff_exists_add_mul_eq_coeff W.polynomial_nat_degree).mp
          h with ⟨f, g, h0, h1⟩,
  simp only [polynomial_eq, cubic.coeff_eq_c, cubic.coeff_eq_d] at h0 h1,
  apply_fun degree at h0 h1,
  rw [cubic.degree_of_a_ne_zero' $ neg_ne_zero.mpr $ one_ne_zero' R, degree_mul] at h0,
  replace h1 := h1.symm.le.trans cubic.degree_of_b_eq_zero',
  contrapose! h1,
  rcases nat.with_bot.add_eq_three_iff.mp h0.symm with ⟨hf, hg⟩ | ⟨hf, hg⟩ | ⟨hf, hg⟩ | ⟨hf, hg⟩,
  any_goals { rw [degree_add_eq_left_of_degree_lt]; simp only [hf, hg]; dec_trivial },
  any_goals { rw [degree_add_eq_right_of_degree_lt]; simp only [hf, hg]; dec_trivial }
end

/-- The coordinate ring $R[W] := R[X, Y] / \langle W(X, Y) \rangle$ of `W`. -/
@[reducible] def coordinate_ring : Type u := adjoin_root W.polynomial

instance {F : Type u} [field F] (W : weierstrass_curve F) : is_domain $ W.coordinate_ring :=
(ideal.quotient.is_domain_iff_prime _).mpr
begin
  classical,
  simpa only [ideal.span_singleton_prime W.polynomial_ne_zero, ← gcd_monoid.irreducible_iff_prime]
    using W.polynomial_irreducible
end

end polynomial

end weierstrass_curve

/-! ## Elliptic curves -/

/-- An elliptic curve over a commutative ring. Note that this definition is only mathematically
accurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. -/
@[ext] structure elliptic_curve (R : Type u) [comm_ring R] extends weierstrass_curve R :=
(Δ' : Rˣ) (coe_Δ' : ↑Δ' = to_weierstrass_curve.Δ)

instance : inhabited $ elliptic_curve ℚ :=
⟨⟨⟨0, 0, 1, -1, 0⟩, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩, by { dsimp, ring1 }⟩⟩

namespace elliptic_curve

variables [comm_ring R] (E : elliptic_curve R)

/-- The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. -/
@[simp] def j : R := ↑E.Δ'⁻¹ * E.c₄ ^ 3

lemma two_torsion_polynomial.disc_ne_zero [nontrivial R] [invertible (2 : R)] :
  E.two_torsion_polynomial.disc ≠ 0 :=
(E.two_torsion_polynomial_disc_is_unit.mpr $ E.coe_Δ' ▸ E.Δ'.is_unit).ne_zero

section variable_change

/-! ### Variable changes -/

variables (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
$(x, y) \mapsto (u^2x + r, u^3y + u^2sx + t)$ for some $u \in R^\times$ and some $r, s, t \in R$.
When `R` is a field, any two Weierstrass equations isomorphic to `E` are related by this. -/
@[simps] def variable_change : elliptic_curve R :=
⟨E.variable_change u r s t, u⁻¹ ^ 12 * E.Δ',
by rw [units.coe_mul, units.coe_pow, coe_Δ', E.variable_change_Δ]⟩

lemma coe_variable_change_Δ' : (↑(E.variable_change u r s t).Δ' : R) = ↑u⁻¹ ^ 12 * E.Δ' :=
by rw [variable_change_Δ', units.coe_mul, units.coe_pow]

lemma coe_variable_change_Δ'_inv :
  (↑(E.variable_change u r s t).Δ'⁻¹ : R) = u ^ 12 * ↑E.Δ'⁻¹ :=
by rw [variable_change_Δ', mul_inv, inv_pow, inv_inv, units.coe_mul, units.coe_pow]

@[simp] lemma variable_change_j : (E.variable_change u r s t).j = E.j :=
begin
  rw [j, coe_variable_change_Δ'_inv],
  have hu : (u * ↑u⁻¹ : R) ^ 12 = 1 := by rw [u.mul_inv, one_pow],
  linear_combination E.j * hu with { normalization_tactic := `[dsimp, ring1] }
end

end variable_change

section base_change

/-! ### Base changes -/

variables (A : Type v) [comm_ring A] [algebra R A]

/-- The elliptic curve over `R` base changed to `A`. -/
@[simps] def base_change : elliptic_curve A :=
⟨E.base_change A, units.map ↑(algebra_map R A) E.Δ',
by rw [units.coe_map, ring_hom.coe_monoid_hom, coe_Δ', E.base_change_Δ]⟩

lemma coe_base_change_Δ' : ↑(E.base_change A).Δ' = algebra_map R A E.Δ' := rfl

lemma coe_base_change_Δ'_inv : ↑(E.base_change A).Δ'⁻¹ = algebra_map R A ↑E.Δ'⁻¹ := rfl

@[simp] lemma base_change_j : (E.base_change A).j = algebra_map R A E.j :=
by { simp only [j, coe_base_change_Δ'_inv, base_change_to_weierstrass_curve, E.base_change_c₄],
     map_simp }

end base_change

end elliptic_curve
