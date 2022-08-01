/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import data.rat.defs
import tactic.ring

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
let b2 := a1^2 + 4*a2,
    b4 := 2*a4 + a1*a3,
    b6 := a3^2 + 4*a6,
    b8 := b2*a6 - a1*a3*a4 + a2*a3^2 - a4^2 in
-b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6

theorem EllipticCurve.disc_aux_def {R : Type*} [comm_ring R] (a1 a2 a3 a4 a6 : R) :
  EllipticCurve.disc_aux a1 a2 a3 a4 a6 =
  -27*a3^4 + a1^5*a3*a4 + 16*a2^2*a4^2 - 64*a4^3 - a1^6*a6 - 216*a3^2*a6 - 432*a6^2 -
  16*a2^3*(a3^2 + 4*a6) + 72*a2*a4*(a3^2 + 4*a6) + a1^3*a3*(a3^2 + 8*a2*a4 + 36*a6) +
  4*a1*a3*(4*a2^2*a4 - 24*a4^2 + 9*a2*(a3^2 + 4*a6)) +
  a1^2*(-30*a3^2*a4 + 8*a2*a4^2 + 72*a4*a6 - 8*a2^2*(a3^2 + 6*a6)) +
  a1^4*(a4^2 - a2*(a3^2 + 12*a6)) :=
by dsimp only [EllipticCurve.disc_aux]; ring

-- If Pic(R)[12]=0 then this definition is mathematically correct
/-- The category of elliptic curves over `R` (note that this definition is only mathematically
correct for certain rings, for example if `R` is a field or a PID). -/
structure EllipticCurve (R : Type*) [comm_ring R] :=
(a1 a2 a3 a4 a6 : R)
(disc_unit : Rˣ)
(disc_unit_eq : (disc_unit : R) = EllipticCurve.disc_aux a1 a2 a3 a4 a6)

namespace EllipticCurve

instance : inhabited (EllipticCurve ℚ) := ⟨⟨0,0,1,-1,0, units.mk0 37 (by norm_num),
  by simv only [units.coe_mk, disc_aux_def]; norm_num⟩⟩

variables {R : Type*} [comm_ring R] (E : EllipticCurve R)

/-- The `b_2` coefficient of an elliptic curve. -/
def b2 : R := E.a1^2 + 4*E.a2
/-- The `b_4` coefficient of an elliptic curve. -/
def b4 : R := 2*E.a4 + E.a1*E.a3
/-- The `b_6` coefficient of an elliptic curve. -/
def b6 : R := E.a3^2 + 4*E.a6
/-- The `b_8` coefficient of an elliptic curve. -/
def b8 : R := E.b2*E.a6 - E.a1*E.a3*E.a4 + E.a2*E.a3^2 - E.a4^2
/-- The `c_4` coefficient of an elliptic curve. -/
def c4 : R := E.b2^2 - 24*E.b4

theorem c4_def : E.c4 = E.a1^4 + 8*E.a1^2*E.a2 + 16*E.a2^2 - 24*E.a1*E.a3 - 48*E.a4 :=
by { unfold c4 b2 b4, ring }

/-- The discriminant of an elliptic curve. Sometimes only defined up to sign in the literature;
  we choose the sign used by the LMFDB. See
  [the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant)
  for more discussion. -/
def disc : R := disc_aux E.a1 E.a2 E.a3 E.a4 E.a6

lemma disc_def : E.disc = -E.b2^2*E.b8 - 8*E.b4^3 - 27*E.b6^2 + 9*E.b2*E.b4*E.b6 := rfl

lemma disc_is_unit : is_unit E.disc :=
begin
  convert units.is_unit E.disc_unit,
  exact E.disc_unit_eq.symm
end

/-- The j-invariant of an elliptic curve. -/
def j := E.c4^3 /ₚ E.disc_unit

end EllipticCurve
