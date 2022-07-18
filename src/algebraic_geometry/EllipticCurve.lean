/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/

import algebra.cubic_discriminant
import tactic.linear_combination

/-!
# The category of elliptic curves (over a field or a PID)

We give a working definition of elliptic curves which is mathematically accurate
in many cases, and also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category,
whose objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some
axioms (the map is smooth and proper and the fibres are geometrically connected group varieties
of dimension one). In the special case where `S` is `Spec R` for some commutative ring `R`
whose Picard group is trivial (this includes all fields, all principal ideal domains, and many
other commutative rings) then it can be shown (using rather a lot of algebro-geometric machinery)
that every elliptic curve is, up to isomorphism, a projective plane cubic defined by
the equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, with `aᵢ : R`, and such that
the discriminant of the aᵢ is a unit in `R`.

Some more details of the construction can be found on pages 66-69 of
[N. Katz and B. Mazur, *Arithmetic moduli of elliptic curves*][katz_mazur] or pages
53-56 of [P. Deligne, *Courbes elliptiques: formulaire d'après J. Tate*][deligne_formulaire].

## Warning

The definition in this file makes sense for all commutative rings `R`, but it only gives
a type which can be beefed up to a category which is equivalent to the category of elliptic
curves over `Spec R` in the case that `R` has trivial Picard group `Pic R` or, slightly more
generally, when its `12`-torsion is trivial. The issue is that for a general ring `R`, there
might be elliptic curves over `Spec R` in the sense of algebraic geometry which are not
globally defined by a cubic equation valid over the entire base.

## TODO

Define the `R`-points (or even `A`-points if `A` is an `R`-algebra). Care will be needed at infinity
if `R` is not a field. Define the group law on the `R`-points. Prove associativity (hard).
-/

universe u

/-- The discriminant of the plane cubic `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. If `R` is a
  field, then this polynomial vanishes iff the cubic curve cut out by this equation is singular. -/
def EllipticCurve.disc_aux {R : Type u} [comm_ring R] (a₁ a₂ a₃ a₄ a₆ : R) : R :=
-(a₁ ^ 2 + 4 * a₂) ^ 2 * (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2)
  - 8 * (2 * a₄ + a₁ * a₃) ^ 3 - 27 * (a₃ ^ 2 + 4 * a₆) ^ 2
  + 9 * (a₁ ^ 2 + 4 * a₂) * (2 * a₄ + a₁ * a₃) * (a₃ ^ 2 + 4 * a₆)

-- If Pic(R)[12] = 0 then this definition is mathematically correct
/-- The category of elliptic curves over `R` (note that this definition is only mathematically
  correct for certain rings, for example if `R` is a field or a PID). -/
structure EllipticCurve (R : Type u) [comm_ring R] :=
(a₁ a₂ a₃ a₄ a₆ : R) (disc_unit : Rˣ)
(disc_unit_eq : ↑disc_unit = EllipticCurve.disc_aux a₁ a₂ a₃ a₄ a₆)

namespace EllipticCurve

instance : inhabited (EllipticCurve ℚ) :=
⟨⟨0, 0, 1, -1, 0, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩, show (37 : ℚ) = _ + _, by norm_num1 ⟩⟩

variables {R : Type u} [comm_ring R] (E : EllipticCurve R)

/-! ### Standard quantities -/

/-- The discriminant of an elliptic curve given by the long Weierstrass equation.
  Sometimes only defined up to sign in the literature; we choose the sign used by the LMFDB. See
  [the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant)
  for more discussion. -/
def disc : R := disc_aux E.a₁ E.a₂ E.a₃ E.a₄ E.a₆

lemma disc_is_unit : is_unit E.disc :=
by { convert units.is_unit E.disc_unit, exact E.disc_unit_eq.symm }

/-- The j-invariant of an elliptic curve. -/
def j : R := ↑E.disc_unit⁻¹
  * (-48 * E.a₄ - 24 * E.a₁ * E.a₃ + 16 * E.a₂ ^ 2 + 8 * E.a₁ ^ 2 * E.a₂ + E.a₁ ^ 4) ^ 3

/-! ### `2`-torsion polynomials -/

section torsion_polynomial

variables (A : Type u) [comm_ring A] [algebra R A]

/-- The polynomial whose roots over a splitting field of `R` are the `2`-torsion points of the
  elliptic curve when `R` is a field of characteristic different from `2`, and whose discriminant
  happens to be a multiple of the discriminant of the elliptic curve. -/
def two_torsion_polynomial : cubic A :=
⟨4, algebra_map R A E.a₁ ^ 2 + 4 * algebra_map R A E.a₂,
  4 * algebra_map R A E.a₄ + 2 * algebra_map R A E.a₁ * algebra_map R A E.a₃,
  algebra_map R A E.a₃ ^ 2 + 4 * algebra_map R A E.a₆⟩

lemma two_torsion_polynomial.disc_eq_disc :
  (two_torsion_polynomial E A).disc = 16 * algebra_map R A E.disc :=
begin
  rw [cubic.disc, two_torsion_polynomial, disc, disc_aux],
  simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_one, map_bit0, map_bit1],
  ring1
end

lemma two_torsion_polynomial.disc_ne_zero {K : Type u} [field K] [invertible (2 : K)]
  (E : EllipticCurve K) (A : Type u) [comm_ring A] [nontrivial A] [no_zero_divisors A]
  [algebra K A] : (two_torsion_polynomial E A).disc ≠ 0 :=
begin
  haveI : invertible (2 : A) :=
  begin
    rw [← nat.cast_two],
    exact @is_scalar_tower.invertible_algebra_coe_nat _ _ _ _ _ _ (by rwa [nat.cast_two])
  end,
  rw [two_torsion_polynomial.disc_eq_disc],
  convert_to 2 ^ 4 * algebra_map K A E.disc ≠ 0,
  { norm_num1,
    refl },
  refine mul_ne_zero (pow_ne_zero 4 _) _,
  { exact nonzero_of_invertible 2 },
  rw [ring_hom.map_ne_zero $ algebra_map K A, disc, ← disc_unit_eq],
  exact units.ne_zero E.disc_unit
end

end torsion_polynomial

/-! ### Changes of variables -/

section change_of_variables

variables (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` for some `u ∈ Rˣ` and some `r, s, t ∈ R`.
  When `R` is a field, any two isomorphic long Weierstrass equations are related by this. -/
def change_of_variable : EllipticCurve R :=
{ a₁           := ↑u⁻¹ * (E.a₁ + 2 * s),
  a₂           := ↑u⁻¹ ^ 2 * (E.a₂ - s * E.a₁ + 3 * r - s ^ 2),
  a₃           := ↑u⁻¹ ^ 3 * (E.a₃ + r * E.a₁ + 2 * t),
  a₄           := ↑u⁻¹ ^ 4 * (E.a₄ - s * E.a₃ + 2 * r * E.a₂ - (t + r * s) * E.a₁ + 3 * r ^ 2
                              - 2 * s * t),
  a₆           := ↑u⁻¹ ^ 6 * (E.a₆ + r * E.a₄ + r ^ 2 * E.a₂ + r ^ 3 - t * E.a₃ - t ^ 2
                              - r * t * E.a₁),
  disc_unit    := u⁻¹ ^ 12 * E.disc_unit,
  disc_unit_eq := by { simp only [units.coe_mul, units.coe_pow, disc_unit_eq, disc_aux], ring1 } }

lemma change_of_variable.j_eq_j : (E.change_of_variable u r s t).j = E.j :=
begin
  simp only [change_of_variable, j, mul_inv, units.coe_mul, inv_pow, inv_inv, units.coe_pow],
  have hvi : (u * ↑u⁻¹ : R) ^ 12 = 1 := by rw [u.mul_inv, one_pow],
  linear_combination ↑E.disc_unit⁻¹
    * (-48 * E.a₄ - 24 * E.a₁ * E.a₃ + 16 * E.a₂ ^ 2 + 8 * E.a₁ ^ 2 * E.a₂ + E.a₁ ^ 4) ^ 3 * hvi
end

end change_of_variables

end EllipticCurve
