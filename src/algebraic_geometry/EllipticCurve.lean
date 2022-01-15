/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import algebra.algebra.basic
import data.rat.basic

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
generally, when its 12-torsion is trivial. The issue is that for a general ring `R`, there
might be elliptic curves over `Spec R` in the sense of algebraic geometry which are not
globally defined by a cubic equation valid over the entire base.

## TODO

Define the `R`-points (or even `A`-points if `A` is an `R`-algebra). Care will be needed at infinity
if `R` is not a field. Define the group law on the `R`-points. Prove associativity (hard).
-/

/-- The discriminant of the plane cubic `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. If `R` is a
  field, then this polynomial vanishes iff the cubic curve cut out by this equation is singular. -/
def EllipticCurve.disc_aux {R : Type*} [comm_ring R] (a₁ a₂ a₃ a₄ a₆ : R) : R :=
-(a₁ ^ 2 + 4 * a₂) ^ 2 * (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2)
  - 8 * (2 * a₄ + a₁ * a₃) ^ 3 - 27 * (a₃ ^ 2 + 4 * a₆) ^ 2
  + 9 * (a₁ ^ 2 + 4 * a₂) * (2 * a₄ + a₁ * a₃) * (a₃ ^ 2 + 4 * a₆)

-- If Pic(R)[12] = 0 then this definition is mathematically correct
/-- The category of elliptic curves over `R` (note that this definition is only mathematically
  correct for certain rings, for example if `R` is a field or a PID). -/
structure EllipticCurve (R : Type*) [comm_ring R] :=
(a₁ a₂ a₃ a₄ a₆ : R) (disc_unit : Rˣ)
(disc_unit_eq : disc_unit.val = EllipticCurve.disc_aux a₁ a₂ a₃ a₄ a₆)

namespace EllipticCurve

instance : inhabited (EllipticCurve ℚ) :=
⟨⟨0, 0, 1, -1, 0, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩, by change (37 : ℚ) = _ + _; norm_num1⟩⟩

variables {R : Type*} [comm_ring R] (E : EllipticCurve R)

/-- The discriminant of an elliptic curve given by the long Weierstrass equation.
  Sometimes only defined up to sign in the literature; we choose the sign used by the LMFDB. See
  [the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant)
  for more discussion. -/
def disc : R := disc_aux E.a₁ E.a₂ E.a₃ E.a₄ E.a₆

lemma disc_is_unit : is_unit E.disc :=
by { convert units.is_unit E.disc_unit, exact E.disc_unit_eq.symm }

/-- The j-invariant of an elliptic curve. -/
def j := E.disc_unit.inv
  * (-48 * E.a₄ - 24 * E.a₁ * E.a₃ + 16 * E.a₂ ^ 2 + 8 * E.a₁ ^ 2 * E.a₂ + E.a₁ ^ 4) ^ 3

end EllipticCurve
