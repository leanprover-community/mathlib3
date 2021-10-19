/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import algebra.group_power
import data.rat.basic
import tactic.norm_num

/-!
# The category of elliptic curves (over a field or a PID)

We give a working definition of elliptic curves which is mathematically accurate
in many cases, and also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category,
whose objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some
axioms (the map is smooth and proper and the fibres are geometrically connected group varieties
of dimension 1). In the special case where `S` is `Spec R` for some commutative ring `R`
whose Picard group is trivial (this includes all fields, all principal ideal domains, and many
other commutative rings) then it can be shown (using rather a lot of algebro-geometric machinery)
that every elliptic curve is, up to isomorphism, a projective plane cubic defined by
the equation `y^2+a₁xy+a₃y=x^3+a₂x^2+a₄x+a₆`, with `aᵢ : R`, and such that the discriminant
of the aᵢ is a unit in `R`.

Some more details of the construction can be found on pages 66-69 of
[N. Katz and B. Mazur, *Arithmetic moduli of elliptic curves*][katz_mazur] or pages
53-56 of [P. Deligne, *Courbes elliptiques: formulaire d'après J. Tate*][deligne_formulaire].

## Warning

The definition in this file makes sense for all commutative rings `R`, but it only gives
a type which can be beefed up to a category which is equivalent to the category of elliptic
curves over `Spec R` in the case that `R` has trivial Picard group or, slightly more generally,
when the 12-torsion of Pic(R) is trivial. The issue is that for a general ring R, there
might be elliptic curves over Spec(R) in the sense of algebraic geometry which are not
globally defined by a cubic equation valid over the entire base.

## TODO

Define the R-points (or even A-points if A is an R-algebra). Care will be needed
at infinity if R is not a field. Define the group law on the R-points. (hard) prove associativity.

-/

/-- The discriminant of the plane cubic `Y^2+a1*X*Y+a3*Y=X^3+a2*X^2+a4*X+a6`. If `R` is a field
then this polynomial vanishes iff the cubic curve cut out by this equation is singular. -/
def EllipticCurve.disc_aux {R : Type*} [comm_ring R] (a1 a2 a3 a4 a6 : R) : R :=
-432*a6^2 + ((288*a2 + 72*a1^2)*a4 + (-216*a3^2 + (144*a1*a2 + 36*a1^3)*a3 + (-64*a2^3 -
48*a1^2*a2^2 - 12*a1^4*a2 - a1^6)))*a6 + (-64*a4^3 + (-96*a1*a3 + (16*a2^2 + 8*a1^2*a2 + a1^4))*a4^2
+ ((72*a2 - 30*a1^2)*a3^2 + (16*a1*a2^2 + 8*a1^3*a2 + a1^5)*a3)*a4 + (-27*a3^4 + (36*a1*a2 +
a1^3)*a3^3 + (-16*a2^3 - 8*a1^2*a2^2 - a1^4*a2)*a3^2))

-- If Pic(R)[12]=0 then this definition is mathematically correct
/-- The category of elliptic curves over `R` (note that this definition is only mathematically
correct for certain rings, for example if `R` is a field or a PID). -/
structure EllipticCurve (R : Type*) [comm_ring R] :=
(a1 a2 a3 a4 a6 : R)
(disc_unit : units R)
(disc_unit_eq : (disc_unit : R) = EllipticCurve.disc_aux a1 a2 a3 a4 a6)

namespace EllipticCurve

instance : inhabited (EllipticCurve ℚ) := ⟨⟨0,0,1,-1,0, ⟨37, 37⁻¹, by norm_num, by norm_num⟩,
  show (37 : ℚ) = _ + _, by norm_num⟩⟩

variables {R : Type*} [comm_ring R] (E : EllipticCurve R)

/-- The discriminant of an elliptic curve. Sometimes only defined up to sign in the literature;
  we choose the sign used by the LMFDB. See
  [the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant)
  for more discussion. -/
def disc : R := disc_aux E.a1 E.a2 E.a3 E.a4 E.a6

lemma disc_is_unit : is_unit E.disc :=
begin
  convert units.is_unit E.disc_unit,
  exact E.disc_unit_eq.symm
end

/-- The j-invariant of an elliptic curve. -/
def j := (-48*E.a4 + (-24*E.a1*E.a3 + (16*E.a2^2 + 8*E.a1^2*E.a2 + E.a1^4)))^3 *
  (E.disc_unit⁻¹ : units R)

end EllipticCurve
