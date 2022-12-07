/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/

import algebra.cubic_discriminant
import tactic.linear_combination

/-!
# Weierstrass equations of elliptic curves

We give a working definition of an elliptic curve as a non-singular Weierstrass curve given by a
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
 * `weierstrass_curve.variable_change`: the Weierstrass curve induced by a change of variables.
 * `weierstrass_curve.base_change`: the Weierstrass curve base changed over an algebra.
 * `weierstrass_curve.two_torsion_polynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `elliptic_curve`: an elliptic curve over a commutative ring.
 * `elliptic_curve.j`: the j-invariant of an elliptic curve.

## Main statements

 * `weierstrass_curve.two_torsion_polynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
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

universes u v

variable {R : Type u}

/-! ## Weierstrass curves -/

/-- A Weierstrass curve $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ with parameters $a_i$. -/
@[ext] structure weierstrass_curve (R : Type u) := (a₁ a₂ a₃ a₄ a₆ : R)

instance [inhabited R] : inhabited $ weierstrass_curve R :=
⟨⟨default, default, default, default, default⟩⟩

namespace weierstrass_curve

variables [comm_ring R] (C : weierstrass_curve R)

section quantity

/-! ### Standard quantities -/

/-- The `b₂` coefficient of a Weierstrass curve. -/
@[simp] def b₂ : R := C.a₁ ^ 2 + 4 * C.a₂

/-- The `b₄` coefficient of a Weierstrass curve. -/
@[simp] def b₄ : R := 2 * C.a₄ + C.a₁ * C.a₃

/-- The `b₆` coefficient of a Weierstrass curve. -/
@[simp] def b₆ : R := C.a₃ ^ 2 + 4 * C.a₆

/-- The `b₈` coefficient of a Weierstrass curve. -/
@[simp] def b₈ : R :=
C.a₁ ^ 2 * C.a₆ + 4 * C.a₂ * C.a₆ - C.a₁ * C.a₃ * C.a₄ + C.a₂ * C.a₃ ^ 2 - C.a₄ ^ 2

lemma b_relation : 4 * C.b₈ = C.b₂ * C.b₆ - C.b₄ ^ 2 := by { simp only [b₂, b₄, b₆, b₈], ring1 }

/-- The `c₄` coefficient of a Weierstrass curve. -/
@[simp] def c₄ : R := C.b₂ ^ 2 - 24 * C.b₄

/-- The `c₆` coefficient of a Weierstrass curve. -/
@[simp] def c₆ : R := -C.b₂ ^ 3 + 36 * C.b₂ * C.b₄ - 216 * C.b₆

/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[simp] def Δ : R := -C.b₂ ^ 2 * C.b₈ - 8 * C.b₄ ^ 3 - 27 * C.b₆ ^ 2 + 9 * C.b₂ * C.b₄ * C.b₆

lemma c_relation : 1728 * C.Δ = C.c₄ ^ 3 - C.c₆ ^ 2 :=
by { simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ], ring1 }

end quantity

section variable_change

/-! ### Variable changes -/

variables (u : Rˣ) (r s t : R)

/-- The Weierstrass curve over `R` induced by an admissible linear change of variables
$(x, y) \mapsto (u^2x + r, u^3y + u^2sx + t)$ for some $u \in R^\times$ and some $r, s, t \in R$. -/
@[simps] def variable_change : weierstrass_curve R :=
{ a₁ := ↑u⁻¹ * (C.a₁ + 2 * s),
  a₂ := ↑u⁻¹ ^ 2 * (C.a₂ - s * C.a₁ + 3 * r - s ^ 2),
  a₃ := ↑u⁻¹ ^ 3 * (C.a₃ + r * C.a₁ + 2 * t),
  a₄ := ↑u⁻¹ ^ 4 * (C.a₄ - s * C.a₃ + 2 * r * C.a₂ - (t + r * s) * C.a₁ + 3 * r ^ 2 - 2 * s * t),
  a₆ := ↑u⁻¹ ^ 6 * (C.a₆ + r * C.a₄ + r ^ 2 * C.a₂ + r ^ 3 - t * C.a₃ - t ^ 2 - r * t * C.a₁) }

@[simp] lemma variable_change_b₂ : (C.variable_change u r s t).b₂ = ↑u⁻¹ ^ 2 * (C.b₂ + 12 * r) :=
by { simp only [b₂, variable_change_a₁, variable_change_a₂], ring1 }

@[simp] lemma variable_change_b₄ :
  (C.variable_change u r s t).b₄ = ↑u⁻¹ ^ 4 * (C.b₄ + r * C.b₂ + 6 * r ^ 2) :=
by { simp only [b₂, b₄, variable_change_a₁, variable_change_a₃, variable_change_a₄], ring1 }

@[simp] lemma variable_change_b₆ :
  (C.variable_change u r s t).b₆ = ↑u⁻¹ ^ 6 * (C.b₆ + 2 * r * C.b₄ + r ^ 2 * C.b₂ + 4 * r ^ 3) :=
by { simp only [b₂, b₄, b₆, variable_change_a₃, variable_change_a₆], ring1 }

@[simp] lemma variable_change_b₈ :
  (C.variable_change u r s t).b₈
    = ↑u⁻¹ ^ 8 * (C.b₈ + 3 * r * C.b₆ + 3 * r ^ 2 * C.b₄ + r ^ 3 * C.b₂ + 3 * r ^ 4) :=
by { simp only [b₂, b₄, b₆, b₈, variable_change_a₁, variable_change_a₂, variable_change_a₃,
                variable_change_a₄, variable_change_a₆], ring1 }

@[simp] lemma variable_change_c₄ : (C.variable_change u r s t).c₄ = ↑u⁻¹ ^ 4 * C.c₄ :=
by { simp only [c₄, variable_change_b₂, variable_change_b₄], ring1 }

@[simp] lemma variable_change_c₆ : (C.variable_change u r s t).c₆ = ↑u⁻¹ ^ 6 * C.c₆ :=
by { simp only [c₆, variable_change_b₂, variable_change_b₄, variable_change_b₆], ring1 }

@[simp] lemma variable_change_Δ : (C.variable_change u r s t).Δ = ↑u⁻¹ ^ 12 * C.Δ :=
by { dsimp, ring1 }

end variable_change

section base_change

/-! ### Base changes -/

variables (A : Type v) [comm_ring A] [algebra R A]

/-- The Weierstrass curve over `R` base changed to `A`. -/
@[simps] def base_change : weierstrass_curve A :=
⟨algebra_map R A C.a₁, algebra_map R A C.a₂, algebra_map R A C.a₃, algebra_map R A C.a₄,
algebra_map R A C.a₆⟩

@[simp] lemma base_change_b₂ : (C.base_change A).b₂ = algebra_map R A C.b₂ :=
by { simp only [b₂, base_change_a₁, base_change_a₂], map_simp }

@[simp] lemma base_change_b₄ : (C.base_change A).b₄ = algebra_map R A C.b₄ :=
by { simp only [b₄, base_change_a₁, base_change_a₃, base_change_a₄], map_simp }

@[simp] lemma base_change_b₆ : (C.base_change A).b₆ = algebra_map R A C.b₆ :=
by { simp only [b₆, base_change_a₃, base_change_a₆], map_simp }

@[simp] lemma base_change_b₈ : (C.base_change A).b₈ = algebra_map R A C.b₈ :=
by { simp only [b₈, base_change_a₁, base_change_a₂, base_change_a₃, base_change_a₄, base_change_a₆],
     map_simp }

@[simp] lemma base_change_c₄ : (C.base_change A).c₄ = algebra_map R A C.c₄ :=
by { simp only [c₄, base_change_b₂, base_change_b₄], map_simp }

@[simp] lemma base_change_c₆ : (C.base_change A).c₆ = algebra_map R A C.c₆ :=
by { simp only [c₆, base_change_b₂, base_change_b₄, base_change_b₆], map_simp }

@[simp, nolint simp_nf] lemma base_change_Δ : (C.base_change A).Δ = algebra_map R A C.Δ :=
by { simp only [Δ, base_change_b₂, base_change_b₄, base_change_b₆, base_change_b₈], map_simp }

end base_change

section torsion_polynomial

/-! ### 2-torsion polynomials -/

/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant.
If `C` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over
a splitting field of `R` are precisely the x-coordinates of the non-zero 2-torsion points of `C`. -/
def two_torsion_polynomial : cubic R := ⟨4, C.b₂, 2 * C.b₄, C.b₆⟩

lemma two_torsion_polynomial_disc : C.two_torsion_polynomial.disc = 16 * C.Δ :=
by { dsimp [two_torsion_polynomial, cubic.disc], ring1 }

lemma two_torsion_polynomial_disc_is_unit [invertible (2 : R)] :
  is_unit C.two_torsion_polynomial.disc ↔ is_unit C.Δ :=
begin
  rw [two_torsion_polynomial_disc, is_unit.mul_iff, show (16 : R) = 2 ^ 4, by norm_num1],
  exact and_iff_right (is_unit_of_invertible $ 2 ^ 4)
end

end torsion_polynomial

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
