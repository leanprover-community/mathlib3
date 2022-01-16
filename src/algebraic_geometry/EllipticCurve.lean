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

----------------------------------------------------------------------------------------------------
/-! ## Change of variables -/

section change_of_variables

variables (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by a linear change of variables
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` for some `u ∈ Rˣ` and some `r, s, t ∈ R`. -/
def cov : EllipticCurve R :=
{ a₁           := u.inv * (E.a₁ + 2 * s),
  a₂           := u.inv ^ 2 * (E.a₂ - s * E.a₁ + 3 * r - s ^ 2),
  a₃           := u.inv ^ 3 * (E.a₃ + r * E.a₁ + 2 * t),
  a₄           := u.inv ^ 4 * (E.a₄ - s * E.a₃
                               + 2 * r * E.a₂ - (t + r * s) * E.a₁
                               + 3 * r ^ 2 - 2 * s * t),
  a₆           := u.inv ^ 6 * (E.a₆ + r * E.a₄
                               + r ^ 2 * E.a₂ + r ^ 3 - t * E.a₃
                               - t ^ 2 - r * t * E.a₁),
  disc_unit    :=
  { val     := u.inv ^ 12 * E.disc_unit.val,
    inv     := u.val ^ 12 * E.disc_unit.inv,
    val_inv := by rw [← mul_assoc, ← mul_comm $ _ ^ 12, ← mul_assoc, ← mul_pow, u.val_inv, one_pow,
                      one_mul, E.disc_unit.val_inv],
    inv_val := by rw [← mul_assoc, ← mul_comm $ _ ^ 12, ← mul_assoc, ← mul_pow, u.inv_val, one_pow,
                      one_mul, E.disc_unit.inv_val] },
  disc_unit_eq := by { simp only, rw [disc_unit_eq, disc_aux, disc_aux], ring1 } }

lemma cov.j_eq : (E.cov u r s t).j = E.j :=
begin
  have lhs_rw : ∀ a₁ a₂ a₃ a₄ v : R,
    v ^ 12 * (-48 * a₄ - 24 * a₁ * a₃ + 16 * a₂ ^ 2 + 8 * a₁ ^ 2 * a₂ + a₁ ^ 4) ^ 3
    = (-48 * (v ^ 4 * a₄) - 24 * (v * a₁) * (v ^ 3 * a₃) + 16 * (v ^ 2 * a₂) ^ 2
       + 8 * (v * a₁) ^ 2 * (v ^ 2 * a₂) + (v * a₁) ^ 4) ^ 3 :=
  by { intros, ring1 },
  simp only [cov, j],
  rw [mul_comm $ u.val ^ 12, mul_assoc, lhs_rw],
  simp only [← mul_assoc u.val, ← mul_assoc (u.val ^ _), ← mul_pow, u.val_inv],
  ring1
end

variables [invertible (2 : R)]

instance invertible_two_times_two : invertible (2 * 2 : R) := invertible_mul 2 2

instance invertible_four : invertible (4 : R) :=
by { convert_to invertible (2 * 2 : R), { norm_num1 }, apply invertible_mul }

private lemma half_mul_half : (⅟2 : R) * ⅟2 = ⅟4 :=
by { rw [← inv_of_mul], apply invertible_unique, norm_num1 }

/-- The medium Weierstrass equation `covₘ` obtained by completing a square. -/
def covₘ : EllipticCurve R := E.cov 1 0 (-⅟2 * E.a₁) (-⅟2 * E.a₃)

lemma covₘ.a₁_eq : E.covₘ.a₁ = 0 :=
begin
  change (1 : R) * _ = 0,
  rw [one_mul, neg_mul_comm, ← mul_assoc, mul_inv_of_self, one_mul, add_neg_eq_zero]
end

lemma covₘ.a₂_eq : E.covₘ.a₂ = ⅟4 * E.a₁ ^ 2 + E.a₂ :=
begin
  have lhs_rw : ∀ a₁ a₂ t : R,
    a₂ - -t * a₁ * a₁ + 3 * 0 - (-t * a₁) ^ 2 = (1 - t) * t * a₁ ^ 2 + a₂ :=
  by { intros, ring1 },
  change (1 : R) ^ 2 * _ = _,
  rw [one_pow, one_mul, lhs_rw, one_sub_inv_of_two, half_mul_half]
end

lemma covₘ.a₃_eq : E.covₘ.a₃ = 0 :=
begin
  change (1 : R) ^ 3 * _ = 0,
  rw [one_pow, one_mul, zero_mul, add_monoid.add_zero, neg_mul_comm, ← mul_assoc,
      mul_inv_of_self, one_mul, add_neg_eq_zero]
end

lemma covₘ.a₄_eq :
  E.covₘ.a₄ = E.a₄ + ⅟2 * (E.a₁ * E.a₃) :=
begin
  have lhs_rw : ∀ a₁ a₂ a₃ a₄ t : R,
    a₄ - -t * a₁ * a₃ + 2 * 0 * a₂ - (-t * a₃ + 0 * (-t * a₁)) * a₁ + 3 * 0 ^ 2
      - 2 * (-t * a₁) * (-t * a₃) = a₄ + 2 * t * (1 - t) * (a₁ * a₃) :=
  by { intros, ring1 },
  change (1 : R) ^ 4 * _ = _,
  rw [one_pow, one_mul, lhs_rw, mul_inv_of_self, one_mul, one_sub_inv_of_two]
end

lemma covₘ.a₆_eq : E.covₘ.a₆ = ⅟4 * E.a₃ ^ 2 + E.a₆ :=
begin
  have lhs_rw : ∀ a₁ a₂ a₃ a₄ a₆ t : R,
    a₆ + 0 * a₄ + 0 ^ 2 * a₂ + 0 ^ 3 - -t * a₃ * a₃ - (-t * a₃) ^ 2 - 0 * (-t * a₃) * a₁
      = (1 - t) * t * a₃ ^ 2 + a₆ :=
  by { intros, ring1 },
  change (1 : R) ^ 6 * _ = _,
  rw [one_pow, one_mul, lhs_rw, one_sub_inv_of_two, half_mul_half]
end

end change_of_variables

----------------------------------------------------------------------------------------------------

end EllipticCurve
