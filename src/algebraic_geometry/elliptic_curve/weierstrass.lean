/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/

import algebra.cubic_discriminant
import ring_theory.norm
import tactic.linear_combination

/-!
# Weierstrass equations of elliptic curves

We give a working definition of an elliptic curve as a nonsingular Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map
is smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ for
some $a_i$ in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`.
If `R` is a field, this quantity divides the discriminant of a cubic polynomial whose roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

 * `weierstrass_curve`: a Weierstrass curve over a commutative ring.
 * `weierstrass_curve.Δ`: the discriminant of a Weierstrass curve.
 * `weierstrass_curve.variable_change`: the Weierstrass curve induced by a change of variables.
 * `weierstrass_curve.base_change`: the Weierstrass curve base changed over an algebra.
 * `weierstrass_curve.two_torsion_polynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `weierstrass_curve.polynomial`: the polynomial associated to a Weierstrass curve.
 * `weierstrass_curve.equation`: the Weirstrass equation of a Weierstrass curve.
 * `weierstrass_curve.nonsingular`: the nonsingular condition at a point on a Weierstrass curve.
 * `weierstrass_curve.coordinate_ring`: the coordinate ring of a Weierstrass curve.
 * `weierstrass_curve.function_field`: the function field of a Weierstrass curve.
 * `weierstrass_curve.coordinate_ring.basis`: the power basis of the coordinate ring over `R[X]`.
 * `elliptic_curve`: an elliptic curve over a commutative ring.
 * `elliptic_curve.j`: the j-invariant of an elliptic curve.

## Main statements

 * `weierstrass_curve.two_torsion_polynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
 * `weierstrass_curve.nonsingular_of_Δ_ne_zero`: a Weierstrass curve is nonsingular at every point
    if its discriminant is non-zero.
 * `weierstrass_curve.coordinate_ring.is_domain`: the coordinate ring of a Weierstrass curve is
    an integral domain.
 * `weierstrass_curve.coordinate_ring.degree_norm_smul_basis`: the degree of the norm of an element
    in the coordinate ring in terms of the power basis.
 * `elliptic_curve.nonsingular`: an elliptic curve is nonsingular at every point.
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

private meta def C_simp : tactic unit := `[simp only [C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]]

universes u v w

variable {R : Type u}

/-! ## Weierstrass curves -/

/-- A Weierstrass curve $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ with parameters $a_i$. -/
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
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$. -/
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

variables (A : Type v) [comm_ring A] [algebra R A] (B : Type w) [comm_ring B] [algebra R B]
  [algebra A B] [is_scalar_tower R A B]

section base_change

/-! ### Base changes -/

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

lemma base_change_self : W.base_change R = W := by ext; refl

lemma base_change_base_change : (W.base_change A).base_change B = W.base_change B :=
by ext; exact (is_scalar_tower.algebra_map_apply R A B _).symm

end base_change

section torsion_polynomial

/-! ### 2-torsion polynomials -/

/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If
`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `W`. -/
def two_torsion_polynomial : cubic R := ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩

lemma two_torsion_polynomial_disc : W.two_torsion_polynomial.disc = 16 * W.Δ :=
by { dsimp [two_torsion_polynomial, cubic.disc], ring1 }

lemma two_torsion_polynomial_disc_is_unit [invertible (2 : R)] :
  is_unit W.two_torsion_polynomial.disc ↔ is_unit W.Δ :=
begin
  rw [two_torsion_polynomial_disc, is_unit.mul_iff, show (16 : R) = 2 ^ 4, by norm_num1],
  exact and_iff_right (is_unit_of_invertible $ 2 ^ 4)
end

lemma two_torsion_polynomial_disc_ne_zero [nontrivial R] [invertible (2 : R)] (hΔ : is_unit W.Δ) :
  W.two_torsion_polynomial.disc ≠ 0 :=
(W.two_torsion_polynomial_disc_is_unit.mpr hΔ).ne_zero

end torsion_polynomial

localized "notation (name := outer_variable) `Y` := polynomial.X" in polynomial_polynomial

localized "notation (name := polynomial_polynomial) R`[X][Y]` := polynomial (polynomial R)"
  in polynomial_polynomial

section polynomial

/-! ### Weierstrass equations -/

open polynomial

open_locale polynomial

/-- The polynomial $W(X, Y) := Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$ associated to a
Weierstrass curve `W` over `R`. For ease of polynomial manipulation, this is represented as a term
of type `R[X][X]`, where the inner variable represents $X$ and the outer variable represents $Y$.
For clarity, the alternative notations `Y` and `R[X][Y]` are provided in the `polynomial_polynomial`
locale to represent the outer variable and the bivariate polynomial ring `R[X][X]` respectively. -/
protected noncomputable def polynomial : R[X][Y] :=
Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

lemma polynomial_eq : W.polynomial = cubic.to_poly
  ⟨0, 1, cubic.to_poly ⟨0, 0, W.a₁, W.a₃⟩, cubic.to_poly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ :=
by { simp only [weierstrass_curve.polynomial, cubic.to_poly], C_simp, ring1 }

lemma polynomial_ne_zero [nontrivial R] : W.polynomial ≠ 0 :=
by { rw [polynomial_eq], exact cubic.ne_zero_of_b_ne_zero one_ne_zero }

@[simp] lemma degree_polynomial [nontrivial R] : W.polynomial.degree = 2 :=
by { rw [polynomial_eq], exact cubic.degree_of_b_ne_zero' one_ne_zero }

@[simp] lemma nat_degree_polynomial [nontrivial R] : W.polynomial.nat_degree = 2 :=
by { rw [polynomial_eq], exact cubic.nat_degree_of_b_ne_zero' one_ne_zero }

lemma monic_polynomial : W.polynomial.monic :=
by { nontriviality R, simpa only [polynomial_eq] using cubic.monic_of_b_eq_one' }

lemma irreducible_polynomial [is_domain R] : irreducible W.polynomial :=
begin
  by_contra h,
  rcases (W.monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff W.nat_degree_polynomial).mp
          h with ⟨f, g, h0, h1⟩,
  simp only [polynomial_eq, cubic.coeff_eq_c, cubic.coeff_eq_d] at h0 h1,
  apply_fun degree at h0 h1,
  rw [cubic.degree_of_a_ne_zero' $ neg_ne_zero.mpr $ one_ne_zero' R, degree_mul] at h0,
  apply (h1.symm.le.trans cubic.degree_of_b_eq_zero').not_lt,
  rcases nat.with_bot.add_eq_three_iff.mp h0.symm with h | h | h | h,
  any_goals { rw [degree_add_eq_left_of_degree_lt]; simp only [h]; dec_trivial },
  any_goals { rw [degree_add_eq_right_of_degree_lt]; simp only [h]; dec_trivial }
end

@[simp] lemma eval_polynomial (x y : R) :
  (W.polynomial.eval $ C y).eval x
    = y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :=
by { simp only [weierstrass_curve.polynomial], eval_simp, rw [add_mul, ← add_assoc] }

@[simp] lemma eval_polynomial_zero : (W.polynomial.eval 0).eval 0 = -W.a₆ :=
by simp only [← C_0, eval_polynomial, zero_add, zero_sub, mul_zero, zero_pow (nat.zero_lt_succ _)]

/-- The proposition that an affine point $(x, y)$ lies in `W`. In other words, $W(x, y) = 0$. -/
def equation (x y : R) : Prop := (W.polynomial.eval $ C y).eval x = 0

lemma equation_iff' (x y : R) :
  W.equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
by rw [equation, eval_polynomial]

@[simp] lemma equation_iff (x y : R) :
  W.equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
by rw [equation_iff', sub_eq_zero]

@[simp] lemma equation_zero : W.equation 0 0 ↔ W.a₆ = 0 :=
by rw [equation, C_0, eval_polynomial_zero, neg_eq_zero]

lemma equation_iff_variable_change (x y : R) :
  W.equation x y ↔ (W.variable_change 1 x 0 y).equation 0 0 :=
begin
  rw [equation_iff', ← neg_eq_zero, equation_zero, variable_change_a₆, inv_one, units.coe_one],
  congr' 2,
  ring1
end

lemma equation_iff_base_change [nontrivial A] [no_zero_smul_divisors R A] (x y : R) :
  W.equation x y ↔ (W.base_change A).equation (algebra_map R A x) (algebra_map R A y) :=
begin
  simp only [equation_iff],
  refine ⟨λ h, _, λ h, _⟩,
  { convert congr_arg (algebra_map R A) h; { map_simp, refl } },
  { apply no_zero_smul_divisors.algebra_map_injective R A, map_simp, exact h }
end

lemma equation_iff_base_change_of_base_change [nontrivial B] [no_zero_smul_divisors A B] (x y : A) :
  (W.base_change A).equation x y
    ↔ (W.base_change B).equation (algebra_map A B x) (algebra_map A B y) :=
by rw [equation_iff_base_change (W.base_change A) B, base_change_base_change]

/-! ### Nonsingularity of Weierstrass curves -/

/-- The partial derivative $W_X(X, Y)$ of $W(X, Y)$ with respect to $X$.

TODO: define this in terms of `polynomial.derivative`. -/
noncomputable def polynomial_X : R[X][Y] :=
C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)

@[simp] lemma eval_polynomial_X (x y : R) :
  (W.polynomial_X.eval $ C y).eval x = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) :=
by { simp only [polynomial_X], eval_simp }

@[simp] lemma eval_polynomial_X_zero : (W.polynomial_X.eval 0).eval 0 = -W.a₄ :=
by simp only [← C_0, eval_polynomial_X, zero_add, zero_sub, mul_zero, zero_pow zero_lt_two]

/-- The partial derivative $W_Y(X, Y)$ of $W(X, Y)$ with respect to $Y$.

TODO: define this in terms of `polynomial.derivative`. -/
noncomputable def polynomial_Y : R[X][Y] := C (C 2) * Y + C (C W.a₁ * X + C W.a₃)

@[simp] lemma eval_polynomial_Y (x y : R) :
  (W.polynomial_Y.eval $ C y).eval x = 2 * y + W.a₁ * x + W.a₃ :=
by { simp only [polynomial_Y], eval_simp, rw [← add_assoc] }

@[simp] lemma eval_polynomial_Y_zero : (W.polynomial_Y.eval 0).eval 0 = W.a₃ :=
by simp only [← C_0, eval_polynomial_Y, zero_add, mul_zero]

/-- The proposition that an affine point $(x, y)$ on `W` is nonsingular.
In other words, either $W_X(x, y) \ne 0$ or $W_Y(x, y) \ne 0$. -/
def nonsingular (x y : R) : Prop :=
W.equation x y ∧ ((W.polynomial_X.eval $ C y).eval x ≠ 0 ∨ (W.polynomial_Y.eval $ C y).eval x ≠ 0)

lemma nonsingular_iff' (x y : R) :
  W.nonsingular x y
    ↔ W.equation x y
      ∧ (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0) :=
by rw [nonsingular, equation_iff', eval_polynomial_X, eval_polynomial_Y]

@[simp] lemma nonsingular_iff (x y : R) :
  W.nonsingular x y
    ↔ W.equation x y ∧ (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃) :=
by { rw [nonsingular_iff', sub_ne_zero, ← @sub_ne_zero _ _ y], congr' 4; ring1 }

@[simp] lemma nonsingular_zero : W.nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ ≠ 0 ∨ W.a₄ ≠ 0) :=
by rw [nonsingular, equation_zero, C_0, eval_polynomial_X_zero, neg_ne_zero, eval_polynomial_Y_zero,
       or_comm]

lemma nonsingular_iff_variable_change (x y : R) :
  W.nonsingular x y ↔ (W.variable_change 1 x 0 y).nonsingular 0 0 :=
begin
  rw [nonsingular_iff', equation_iff_variable_change, equation_zero, ← neg_ne_zero, or_comm,
      nonsingular_zero, variable_change_a₃, variable_change_a₄, inv_one, units.coe_one],
  congr' 4; ring1
end

lemma nonsingular_iff_base_change [nontrivial A] [no_zero_smul_divisors R A] (x y : R) :
  W.nonsingular x y ↔ (W.base_change A).nonsingular (algebra_map R A x) (algebra_map R A y) :=
begin
  rw [nonsingular_iff, nonsingular_iff, and_congr $ W.equation_iff_base_change A x y],
  refine ⟨or.imp (not_imp_not.mpr $ λ h, _) (not_imp_not.mpr $ λ h, _),
    or.imp (not_imp_not.mpr $ λ h, _) (not_imp_not.mpr $ λ h, _)⟩,
  any_goals { apply no_zero_smul_divisors.algebra_map_injective R A, map_simp, exact h },
  any_goals { convert congr_arg (algebra_map R A) h; { map_simp, refl } }
end

lemma nonsingular_iff_base_change_of_base_change [nontrivial B] [no_zero_smul_divisors A B]
  (x y : A) : (W.base_change A).nonsingular x y
    ↔ (W.base_change B).nonsingular (algebra_map A B x) (algebra_map A B y) :=
by rw [nonsingular_iff_base_change (W.base_change A) B, base_change_base_change]

lemma nonsingular_zero_of_Δ_ne_zero (h : W.equation 0 0) (hΔ : W.Δ ≠ 0) : W.nonsingular 0 0 :=
by { simp only [equation_zero, nonsingular_zero] at *, contrapose! hΔ, simp [h, hΔ] }

/-- A Weierstrass curve is nonsingular at every point if its discriminant is non-zero. -/
lemma nonsingular_of_Δ_ne_zero {x y : R} (h : W.equation x y) (hΔ : W.Δ ≠ 0) : W.nonsingular x y :=
(W.nonsingular_iff_variable_change x y).mpr $
  nonsingular_zero_of_Δ_ne_zero _ ((W.equation_iff_variable_change x y).mp h) $
by rwa [variable_change_Δ, inv_one, units.coe_one, one_pow, one_mul]

/-! ### Ideals in the coordinate ring -/

/-- The coordinate ring $R[W] := R[X, Y] / \langle W(X, Y) \rangle$ of `W`.

Note that `derive comm_ring` generates a reducible instance of `comm_ring` for `coordinate_ring`.
In certain circumstances this might be extremely slow, because all instances in its definition are
unified exponentially many times. In this case, one solution is to manually add the local attribute
`local attribute [irreducible] coordinate_ring.comm_ring` to block this type-level unification.

TODO Lean 4: verify if the new def-eq cache (lean4#1102) fixed this issue.

See Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20class_group.2Emk -/
@[derive [inhabited, comm_ring]] def coordinate_ring : Type u := adjoin_root W.polynomial

/-- The function field $R(W) := \mathrm{Frac}(R[W])$ of `W`. -/
abbreviation function_field : Type u := fraction_ring W.coordinate_ring

namespace coordinate_ring

instance [is_domain R] [normalized_gcd_monoid R] : is_domain W.coordinate_ring :=
(ideal.quotient.is_domain_iff_prime _).mpr $
by simpa only [ideal.span_singleton_prime W.polynomial_ne_zero, ← gcd_monoid.irreducible_iff_prime]
   using W.irreducible_polynomial

instance is_domain_of_field {F : Type u} [field F] (W : weierstrass_curve F) :
  is_domain W.coordinate_ring :=
by { classical, apply_instance }

variables (x : R) (y : R[X])

/-- The class of the element $X - x$ in $R[W]$ for some $x \in R$. -/
@[simp] noncomputable def X_class : W.coordinate_ring := adjoin_root.mk W.polynomial $ C $ X - C x

lemma X_class_ne_zero [nontrivial R] : X_class W x ≠ 0 :=
adjoin_root.mk_ne_zero_of_nat_degree_lt W.monic_polynomial (C_ne_zero.mpr $ X_sub_C_ne_zero x) $
  by { rw [nat_degree_polynomial, nat_degree_C], norm_num1 }

/-- The class of the element $Y - y(X)$ in $R[W]$ for some $y(X) \in R[X]$. -/
@[simp] noncomputable def Y_class : W.coordinate_ring := adjoin_root.mk W.polynomial $ Y - C y

lemma Y_class_ne_zero [nontrivial R] : Y_class W y ≠ 0 :=
adjoin_root.mk_ne_zero_of_nat_degree_lt W.monic_polynomial (X_sub_C_ne_zero y) $
  by { rw [nat_degree_polynomial, nat_degree_X_sub_C], norm_num1 }

/-- The ideal $\langle X - x \rangle$ of $R[W]$ for some $x \in R$. -/
@[simp] noncomputable def X_ideal : ideal W.coordinate_ring := ideal.span {X_class W x}

/-- The ideal $\langle Y - y(X) \rangle$ of $R[W]$ for some $y(X) \in R[X]$. -/
@[simp] noncomputable def Y_ideal : ideal W.coordinate_ring := ideal.span {Y_class W y}

/-! ### The coordinate ring as an `R[X]`-algebra -/

noncomputable instance : algebra R[X] W.coordinate_ring := ideal.quotient.algebra R[X]

noncomputable instance algebra' : algebra R W.coordinate_ring := ideal.quotient.algebra R

instance : is_scalar_tower R R[X] W.coordinate_ring := ideal.quotient.is_scalar_tower R R[X] _

instance [subsingleton R] : subsingleton W.coordinate_ring := module.subsingleton R[X] _

/-- The basis $\{1, Y\}$ for the coordinate ring $R[W]$ over the polynomial ring $R[X]$.

Given a Weierstrass curve `W`, write `W^.coordinate_ring.basis` for this basis. -/
protected noncomputable def basis : basis (fin 2) R[X] W.coordinate_ring :=
(subsingleton_or_nontrivial R).by_cases (λ _, by exactI default) $ λ _, by exactI
  ((adjoin_root.power_basis' W.monic_polynomial).basis.reindex $
    fin_congr W.nat_degree_polynomial)

lemma basis_apply (n : fin 2) :
  W^.coordinate_ring.basis n = (adjoin_root.power_basis' W.monic_polynomial).gen ^ (n : ℕ) :=
begin
  classical,
  nontriviality R,
  simpa only [coordinate_ring.basis, or.by_cases, dif_neg (not_subsingleton R),
              basis.reindex_apply, power_basis.basis_eq_pow]
end

lemma basis_zero : W^.coordinate_ring.basis 0 = 1 := by simpa only [basis_apply] using pow_zero _

lemma basis_one : W^.coordinate_ring.basis 1 = adjoin_root.mk W.polynomial Y :=
by simpa only [basis_apply] using pow_one _

@[simp] lemma coe_basis :
  (W^.coordinate_ring.basis : fin 2 → W.coordinate_ring) = ![1, adjoin_root.mk W.polynomial Y] :=
by { ext n, fin_cases n, exacts [basis_zero W, basis_one W] }

variable {W}

lemma smul (x : R[X]) (y : W.coordinate_ring) : x • y = adjoin_root.mk W.polynomial (C x) * y :=
(algebra_map_smul W.coordinate_ring x y).symm

lemma smul_basis_eq_zero {p q : R[X]}
  (hpq : p • 1 + q • adjoin_root.mk W.polynomial Y = 0) : p = 0 ∧ q = 0 :=
begin
  have h := fintype.linear_independent_iff.mp (coordinate_ring.basis W).linear_independent ![p, q],
  erw [fin.sum_univ_succ, basis_zero, fin.sum_univ_one, basis_one] at h,
  exact ⟨h hpq 0, h hpq 1⟩
end

lemma exists_smul_basis_eq (x : W.coordinate_ring) :
  ∃ p q : R[X], p • 1 + q • adjoin_root.mk W.polynomial Y = x :=
begin
  have h := (coordinate_ring.basis W).sum_equiv_fun x,
  erw [fin.sum_univ_succ, fin.sum_univ_one, basis_zero, basis_one] at h,
  exact ⟨_, _, h⟩
end

variable (W)

lemma smul_basis_mul_C (p q : R[X]) :
  (p • 1 + q • adjoin_root.mk W.polynomial Y) * adjoin_root.mk W.polynomial (C y)
    = ((p * y) • 1 + (q * y) • adjoin_root.mk W.polynomial Y) :=
by { simp only [smul, map_mul], ring1 }

lemma smul_basis_mul_Y (p q : R[X]) :
  (p • 1 + q • adjoin_root.mk W.polynomial Y) * adjoin_root.mk W.polynomial Y
    = (q * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) • 1
      + (p - q * (C W.a₁ * X + C W.a₃)) • adjoin_root.mk W.polynomial Y :=
begin
  have Y_sq : adjoin_root.mk W.polynomial Y ^ 2 = adjoin_root.mk W.polynomial
    (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) - C (C W.a₁ * X + C W.a₃) * Y) :=
  adjoin_root.mk_eq_mk.mpr ⟨1, by { simp only [weierstrass_curve.polynomial], ring1 }⟩,
  simp only [smul, add_mul, mul_assoc, ← sq, Y_sq, map_sub, map_mul],
  ring1
end

/-! ### Norms on the coordinate ring -/

lemma norm_smul_basis (p q : R[X]) :
  algebra.norm R[X] (p • 1 + q • adjoin_root.mk W.polynomial Y)
    = p ^ 2 - p * q * (C W.a₁ * X + C W.a₃)
      - q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) :=
begin
  simp_rw [algebra.norm_eq_matrix_det W^.coordinate_ring.basis, matrix.det_fin_two,
           algebra.left_mul_matrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y,
           map_add, finsupp.add_apply, map_smul, finsupp.smul_apply, ← basis_zero, ← basis_one,
           basis.repr_self_apply, if_pos, if_neg one_ne_zero, if_neg zero_ne_one, smul_eq_mul],
  ring1
end

lemma coe_norm_smul_basis (p q : R[X]) :
  ↑(algebra.norm R[X] $ p • 1 + q • adjoin_root.mk W.polynomial Y)
    = adjoin_root.mk W.polynomial
      ((C p + C q * X) * (C p + C q * (-X - C (C W.a₁ * X + C W.a₃)))) :=
adjoin_root.mk_eq_mk.mpr
  ⟨C q ^ 2, by { rw [norm_smul_basis, weierstrass_curve.polynomial], C_simp, ring1 }⟩

lemma degree_norm_smul_basis [is_domain R] (p q : R[X]) :
  (algebra.norm R[X] $ p • 1 + q • adjoin_root.mk W.polynomial Y).degree
    = max (2 • p.degree) (2 • q.degree + 3) :=
begin
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2,
  have hdpq : (p * q * (C W.a₁ * X + C W.a₃)).degree ≤ p.degree + q.degree + 1,
  { simpa only [degree_mul] using add_le_add_left degree_linear_le (p.degree + q.degree) },
  have hdq : (q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)).degree = 2 • q.degree + 3,
  { rw [degree_mul, degree_pow, ← one_mul $ X ^ 3, ← C_1, degree_cubic $ one_ne_zero' R] },
  rw [norm_smul_basis],
  by_cases hp : p = 0, { simpa only [hp, hdq, neg_zero, zero_sub, zero_mul, zero_pow zero_lt_two,
                                     degree_neg] using (max_bot_left _).symm },
  by_cases hq : q = 0, { simpa only [hq, hdp, sub_zero, zero_mul, mul_zero, zero_pow zero_lt_two]
                           using (max_bot_right _).symm },
  rw [← not_iff_not_of_iff degree_eq_bot] at hp hq,
  cases p.degree with dp, { exact (hp rfl).elim },
  cases q.degree with dq, { exact (hq rfl).elim },
  cases le_or_lt dp (dq + 1) with hpq hpq,
  { convert (degree_sub_eq_right_of_degree_lt $ (degree_sub_le _ _).trans_lt $
      max_lt_iff.mpr ⟨hdp.trans_lt _, hdpq.trans_lt _⟩).trans (max_eq_right_of_lt _).symm; rw [hdq];
      exact with_bot.coe_lt_coe.mpr (by linarith only [hpq]) },
  { rw [sub_sub],
    convert (degree_sub_eq_left_of_degree_lt $ (degree_add_le _ _).trans_lt $
      max_lt_iff.mpr ⟨hdpq.trans_lt _, hdq.trans_lt _⟩).trans (max_eq_left_of_lt _).symm; rw [hdp];
      exact with_bot.coe_lt_coe.mpr (by linarith only [hpq]) }
end

variable {W}

lemma degree_norm_ne_one [is_domain R] (x : W.coordinate_ring) : (algebra.norm R[X] x).degree ≠ 1 :=
begin
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩,
  rw [degree_norm_smul_basis],
  rcases p.degree with (_ | _ | _ | _); cases q.degree,
  any_goals { rintro (_ | _) },
  exact (lt_max_of_lt_right dec_trivial).ne'
end

lemma nat_degree_norm_ne_one [is_domain R] (x : W.coordinate_ring) :
  (algebra.norm R[X] x).nat_degree ≠ 1 :=
mt (degree_eq_iff_nat_degree_eq_of_pos zero_lt_one).mpr $ degree_norm_ne_one x

end coordinate_ring

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

lemma two_torsion_polynomial_disc_ne_zero [nontrivial R] [invertible (2 : R)] :
  E.two_torsion_polynomial.disc ≠ 0 :=
E.two_torsion_polynomial_disc_ne_zero $ E.coe_Δ' ▸ E.Δ'.is_unit

lemma nonsingular [nontrivial R] {x y : R} (h : E.equation x y) : E.nonsingular x y :=
E.nonsingular_of_Δ_ne_zero h $ E.coe_Δ' ▸ E.Δ'.ne_zero

section variable_change

/-! ### Variable changes -/

variables (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$.
When `R` is a field, any two Weierstrass equations isomorphic to `E` are related by this. -/
@[simps] def variable_change : elliptic_curve R :=
⟨E.variable_change u r s t, u⁻¹ ^ 12 * E.Δ',
by rw [units.coe_mul, units.coe_pow, coe_Δ', E.variable_change_Δ]⟩

lemma coe_variable_change_Δ' : (↑(E.variable_change u r s t).Δ' : R) = ↑u⁻¹ ^ 12 * E.Δ' :=
by rw [variable_change_Δ', units.coe_mul, units.coe_pow]

lemma coe_inv_variable_change_Δ' : (↑(E.variable_change u r s t).Δ'⁻¹ : R) = u ^ 12 * ↑E.Δ'⁻¹ :=
by rw [variable_change_Δ', mul_inv, inv_pow, inv_inv, units.coe_mul, units.coe_pow]

@[simp] lemma variable_change_j : (E.variable_change u r s t).j = E.j :=
begin
  rw [j, coe_inv_variable_change_Δ'],
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

lemma coe_inv_base_change_Δ' : ↑(E.base_change A).Δ'⁻¹ = algebra_map R A ↑E.Δ'⁻¹ := rfl

@[simp] lemma base_change_j : (E.base_change A).j = algebra_map R A E.j :=
by { simp only [j, coe_inv_base_change_Δ', base_change_to_weierstrass_curve, E.base_change_c₄],
     map_simp }

end base_change

end elliptic_curve
