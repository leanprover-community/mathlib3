/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/

import algebra.cubic_discriminant
import tactic.linear_combination

/-!
# The category of elliptic curves (over a field or a PID)

We give a working definition of elliptic curves which is mathematically accurate in many cases,
and also good for computation. The type of `K`-rational points on an elliptic curve over a field
is defined as `EllipticCurve.point` in `src/algebraic_geometry/EllipticCurve/point.lean`.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map
is smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is
trivial (this includes all fields, all PIDs, and many other commutative rings) it can be shown
(using a lot of algebro-geometric machinery) that every elliptic curve is, up to isomorphism, a
projective plane cubic defined by the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$,
with $a_i \in R$, and such that the discriminant of the $a_i$ is a unit in `R`.

## Main definitions

 * `EllipticCurve`: an elliptic curve `E` over a ring `R`.
 * `EllipticCurve.j`: the j-invariant of `E`.
 * `EllipticCurve.two_torsion_polynomial`: the 2-torsion polynomial of `E`.
 * `EllipticCurve.change_of_variable`: an elliptic curve induced by a change of variables on `E`.

## Main statements

 * `EllipticCurve.two_torsion_polynomial.disc_eq`: the discriminant of `E` is a constant factor of
    the cubic discriminant of the 2-torsion polynomial of `E`.
 * `EllipticCurve.change_of_variable.j_eq`: the j-invariant of `E` is invariant under an admissible
    linear change of variables.

## Implementation notes

The definition in this file makes sense for all commutative rings `R`, but it only gives a type
which can be beefed up to a category which is equivalent to the category of elliptic curves over the
spectrum $\mathrm{Spec}(R)$ of `R` in the case that `R` has trivial Picard group $\mathrm{Pic}(R)$
or, slightly more generally, when its 12-torsion is trivial. The issue is that for a general ring
`R`, there might be elliptic curves over $\mathrm{Spec}(R)$ in the sense of algebraic geometry which
are not globally defined by a cubic equation valid over the entire base.

## References

 * [N. Katz and B. Mazur, *Arithmetic moduli of elliptic curves*][katz_mazur]
 * [P. Deligne, *Courbes elliptiques: formulaire d'après J. Tate*][deligne_formulaire]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

universes u v

/-- The discriminant of an elliptic curve given by the long Weierstrass equation
$y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ for some $a_i$ in `R`. If `R` is a field, then this
polynomial vanishes iff the cubic curve cut out by this equation is singular. Sometimes only defined
up to sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[simp] def EllipticCurve.Δ_aux {R : Type u} [comm_ring R] (a₁ a₂ a₃ a₄ a₆ : R) : R :=
let b₂ : R := a₁ ^ 2 + 4 * a₂,
    b₄ : R := 2 * a₄ + a₁ * a₃,
    b₆ : R := a₃ ^ 2 + 4 * a₆,
    b₈ : R := a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2
in  -b₂ ^ 2 * b₈ - 8 * b₄ ^ 3 - 27 * b₆ ^ 2 + 9 * b₂ * b₄ * b₆

/-- The category of elliptic curves over `R` (note that this definition is only mathematically
correct for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID). -/
structure EllipticCurve (R : Type u) [comm_ring R] :=
(a₁ a₂ a₃ a₄ a₆ : R) (Δ : Rˣ) (Δ_eq : ↑Δ = EllipticCurve.Δ_aux a₁ a₂ a₃ a₄ a₆)

namespace EllipticCurve

instance : inhabited (EllipticCurve ℚ) :=
⟨⟨0, 0, 1, -1, 0, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩, show (37 : ℚ) = _ + _, by norm_num1 ⟩⟩

variables {R : Type u} [comm_ring R] (E : EllipticCurve R)

section quantity

/-! ### Standard quantities -/

/-- The `b₂` coefficient of an elliptic curve. -/
@[simp] def b₂ : R := E.a₁ ^ 2 + 4 * E.a₂

/-- The `b₄` coefficient of an elliptic curve. -/
@[simp] def b₄ : R := 2 * E.a₄ + E.a₁ * E.a₃

/-- The `b₆` coefficient of an elliptic curve. -/
@[simp] def b₆ : R := E.a₃ ^ 2 + 4 * E.a₆

/-- The `b₈` coefficient of an elliptic curve. -/
@[simp] def b₈ : R :=
E.a₁ ^ 2 * E.a₆ + 4 * E.a₂ * E.a₆ - E.a₁ * E.a₃ * E.a₄ + E.a₂ * E.a₃ ^ 2 - E.a₄ ^ 2

lemma b_relation : 4 * E.b₈ = E.b₂ * E.b₆ - E.b₄ ^ 2 := by { simp, ring1 }

/-- The `c₄` coefficient of an elliptic curve. -/
@[simp] def c₄ : R := E.b₂ ^ 2 - 24 * E.b₄

/-- The `c₆` coefficient of an elliptic curve. -/
@[simp] def c₆ : R := -E.b₂ ^ 3 + 36 * E.b₂ * E.b₄ - 216 * E.b₆

@[simp] lemma coe_Δ :
  ↑E.Δ = -E.b₂ ^ 2 * E.b₈ - 8 * E.b₄ ^ 3 - 27 * E.b₆ ^ 2 + 9 * E.b₂ * E.b₄ * E.b₆ :=
E.Δ_eq

lemma c_relation : 1728 * ↑E.Δ = E.c₄ ^ 3 - E.c₆ ^ 2 := by { simp, ring1 }

/-- The j-invariant of an elliptic curve, which is invariant under isomorphisms over `R`. -/
@[simp] def j : R := ↑E.Δ⁻¹ * E.c₄ ^ 3

end quantity

section torsion_polynomial

/-! ### 2-torsion polynomials -/

/-- The polynomial whose roots over a splitting field of `R` are precisely the 2-torsion points of
the elliptic curve when `R` is a field of characteristic different from 2, and whose discriminant
happens to be a multiple of the discriminant of the elliptic curve. -/
def two_torsion_polynomial : cubic R := ⟨4, E.b₂, 2 * E.b₄, E.b₆⟩

lemma two_torsion_polynomial.disc_eq : E.two_torsion_polynomial.disc = 16 * E.Δ :=
by { simp only [two_torsion_polynomial, cubic.disc, coe_Δ, b₂, b₄, b₆, b₈], ring1 }

lemma two_torsion_polynomial.disc_ne_zero [nontrivial R] [invertible (2 : R)] :
  E.two_torsion_polynomial.disc ≠ 0 :=
λ hdisc, E.Δ.ne_zero $ (is_unit_of_invertible $ 2 ^ 4).mul_left_cancel $
by linear_combination hdisc - two_torsion_polynomial.disc_eq E
    with { normalization_tactic := `[ring1] }

end torsion_polynomial

section base_change

/-! ### Base changes -/

variables (A : Type v) [comm_ring A] [algebra R A]

private meta def simp_map : tactic unit :=
`[simp only [map_one, map_bit0, map_bit1, map_neg, map_add, map_sub, map_mul, map_pow]]

/-- The elliptic curve over `R` base changed to `A`. -/
@[simps] def base_change : EllipticCurve A :=
{ a₁   := algebra_map R A E.a₁,
  a₂   := algebra_map R A E.a₂,
  a₃   := algebra_map R A E.a₃,
  a₄   := algebra_map R A E.a₄,
  a₆   := algebra_map R A E.a₆,
  Δ    := units.map ↑(algebra_map R A) E.Δ,
  Δ_eq := by { simp only [units.coe_map, ring_hom.coe_monoid_hom, Δ_eq, Δ_aux], simp_map } }

@[simp] lemma base_change_b₂ : (E.base_change A).b₂ = algebra_map R A E.b₂ :=
by { simp only [b₂, base_change_a₁, base_change_a₂], simp_map }

@[simp] lemma base_change_b₄ : (E.base_change A).b₄ = algebra_map R A E.b₄ :=
by { simp only [b₄, base_change_a₁, base_change_a₃, base_change_a₄], simp_map }

@[simp] lemma base_change_b₆ : (E.base_change A).b₆ = algebra_map R A E.b₆ :=
by { simp only [b₆, base_change_a₃, base_change_a₆], simp_map }

@[simp] lemma base_change_b₈ : (E.base_change A).b₈ = algebra_map R A E.b₈ :=
by { simp only [b₈, base_change_a₁, base_change_a₂, base_change_a₃, base_change_a₄, base_change_a₆],
     simp_map }

@[simp] lemma base_change_c₄ : (E.base_change A).c₄ = algebra_map R A E.c₄ :=
by { simp only [c₄, base_change_b₂, base_change_b₄], simp_map }

@[simp] lemma base_change_c₆ : (E.base_change A).c₆ = algebra_map R A E.c₆ :=
by { simp only [c₆, base_change_b₂, base_change_b₄, base_change_b₆], simp_map }

lemma base_change_Δ_coe : ↑(E.base_change A).Δ = algebra_map R A E.Δ := rfl

lemma base_change_Δ_inv_coe : ↑(E.base_change A).Δ⁻¹ = algebra_map R A ↑E.Δ⁻¹ := rfl

@[simp] lemma base_change_j : (E.base_change A).j = algebra_map R A E.j :=
by { simp only [j, base_change_c₄, base_change_Δ_inv_coe], simp_map }

end base_change

section variable_change

/-! ### Variable changes -/

variables (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
$(x, y) \mapsto (u^2x + r, u^3y + u^2sx + t)$ for some $u \in R^\times$ and some $r, s, t \in R$.
When `R` is a field, any two isomorphic long Weierstrass equations are related by this. -/
@[simps] def variable_change : EllipticCurve R :=
{ a₁   := ↑u⁻¹ * (E.a₁ + 2 * s),
  a₂   := ↑u⁻¹ ^ 2 * (E.a₂ - s * E.a₁ + 3 * r - s ^ 2),
  a₃   := ↑u⁻¹ ^ 3 * (E.a₃ + r * E.a₁ + 2 * t),
  a₄   := ↑u⁻¹ ^ 4 * (E.a₄ - s * E.a₃ + 2 * r * E.a₂ - (t + r * s) * E.a₁ + 3 * r ^ 2 - 2 * s * t),
  a₆   := ↑u⁻¹ ^ 6 * (E.a₆ + r * E.a₄ + r ^ 2 * E.a₂ + r ^ 3 - t * E.a₃ - t ^ 2 - r * t * E.a₁),
  Δ    := u⁻¹ ^ 12 * E.Δ,
  Δ_eq := by { simp [-inv_pow], ring1 } }

@[simp] lemma variable_change_b₂ : (E.variable_change u r s t).b₂ = ↑u⁻¹ ^ 2 * (E.b₂ + 12 * r) :=
by { simp only [b₂, variable_change_a₁, variable_change_a₂], ring1 }

@[simp] lemma variable_change_b₄ :
  (E.variable_change u r s t).b₄ = ↑u⁻¹ ^ 4 * (E.b₄ + r * E.b₂ + 6 * r ^ 2) :=
by { simp only [b₂, b₄, variable_change_a₁, variable_change_a₃, variable_change_a₄], ring1 }

@[simp] lemma variable_change_b₆ :
  (E.variable_change u r s t).b₆ = ↑u⁻¹ ^ 6 * (E.b₆ + 2 * r * E.b₄ + r ^ 2 * E.b₂ + 4 * r ^ 3) :=
by { simp only [b₂, b₄, b₆, variable_change_a₃, variable_change_a₆], ring1 }

@[simp] lemma variable_change_b₈ :
  (E.variable_change u r s t).b₈
    = ↑u⁻¹ ^ 8 * (E.b₈ + 3 * r * E.b₆ + 3 * r ^ 2 * E.b₄ + r ^ 3 * E.b₂ + 3 * r ^ 4) :=
by { simp only [b₂, b₄, b₆, b₈, variable_change_a₁, variable_change_a₂, variable_change_a₃,
                variable_change_a₄, variable_change_a₆], ring1 }

@[simp] lemma variable_change_c₄ : (E.variable_change u r s t).c₄ = ↑u⁻¹ ^ 4 * E.c₄ :=
by { simp only [c₄, variable_change_b₂, variable_change_b₄], ring1 }

@[simp] lemma variable_change_c₆ : (E.variable_change u r s t).c₆ = ↑u⁻¹ ^ 6 * E.c₆ :=
by { simp only [c₆, variable_change_b₂, variable_change_b₄, variable_change_b₆], ring1 }

lemma variable_change_Δ_coe : (↑(E.variable_change u r s t).Δ : R) = ↑u⁻¹ ^ 12 * E.Δ :=
by rw [variable_change_Δ, units.coe_mul, units.coe_pow]

lemma variable_change_Δ_inv_coe : (↑(E.variable_change u r s t).Δ⁻¹ : R) = u ^ 12 * ↑E.Δ⁻¹ :=
by rw [variable_change_Δ, mul_inv, inv_pow, inv_inv, units.coe_mul, units.coe_pow]

@[simp] lemma variable_change_j : (E.variable_change u r s t).j = E.j :=
begin
  simp only [b₂, b₄, c₄, j, variable_change_c₄, variable_change_Δ, mul_inv, inv_pow, inv_inv,
             units.coe_mul, u.coe_pow],
  have hu : (u * ↑u⁻¹ : R) ^ 12 = 1 := by rw [u.mul_inv, one_pow],
  linear_combination ↑E.Δ⁻¹ * ((E.a₁ ^ 2 + 4 * E.a₂) ^ 2 - 24 * (2 * E.a₄ + E.a₁ * E.a₃)) ^ 3 * hu
    with { normalization_tactic := `[ring1] }
end

end variable_change

end EllipticCurve
