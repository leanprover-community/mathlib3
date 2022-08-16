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

universes u v

/-- The discriminant of an elliptic curve given by the long Weierstrass equation
  `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. If `R` is a field, then this polynomial vanishes iff the
  cubic curve cut out by this equation is singular. Sometimes only defined up to sign in the
  literature; we choose the sign used by the LMFDB. For more discussion, see
  [the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[simp] def EllipticCurve.Δ_aux {R : Type u} [comm_ring R] (a₁ a₂ a₃ a₄ a₆ : R) : R :=
let b₂ : R := a₁ ^ 2 + 4 * a₂,
    b₄ : R := 2 * a₄ + a₁ * a₃,
    b₆ : R := a₃ ^ 2 + 4 * a₆,
    b₈ : R := a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2
in  -b₂ ^ 2 * b₈ - 8 * b₄ ^ 3 - 27 * b₆ ^ 2 + 9 * b₂ * b₄ * b₆

/-- The category of elliptic curves over `R` (note that this definition is only mathematically
  correct for certain rings `R` with `Pic(R)[12] = 0`, for example if `R` is a field or a PID). -/
structure EllipticCurve (R : Type u) [comm_ring R] :=
(a₁ a₂ a₃ a₄ a₆ : R) (Δ : Rˣ) (Δ_eq : ↑Δ = EllipticCurve.Δ_aux a₁ a₂ a₃ a₄ a₆)

namespace EllipticCurve

instance : inhabited (EllipticCurve ℚ) :=
⟨⟨0, 0, 1, -1, 0, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩, show (37 : ℚ) = _ + _, by norm_num1 ⟩⟩

variables {R : Type u} [comm_ring R] (E : EllipticCurve R)

/-! ### Standard quantities -/

section quantity

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

/-! ### `2`-torsion polynomials -/

section torsion_polynomial

variables (A : Type v) [comm_ring A] [algebra R A]

/-- The polynomial whose roots over a splitting field of `R` are the `2`-torsion points of the
  elliptic curve when `R` is a field of characteristic different from `2`, and whose discriminant
  happens to be a multiple of the discriminant of the elliptic curve. -/
def two_torsion_polynomial : cubic A :=
⟨4, algebra_map R A E.b₂, 2 * algebra_map R A E.b₄, algebra_map R A E.b₆⟩

lemma two_torsion_polynomial.disc_eq :
  (two_torsion_polynomial E A).disc = 16 * algebra_map R A E.Δ :=
begin
  simp only [two_torsion_polynomial, cubic.disc, coe_Δ, b₂, b₄, b₆, b₈, map_neg, map_add, map_sub,
             map_mul, map_pow, map_one, map_bit0, map_bit1],
  ring1
end

lemma two_torsion_polynomial.disc_ne_zero {K : Type u} [field K] [invertible (2 : K)]
  (E : EllipticCurve K) (A : Type v) [comm_ring A] [nontrivial A] [algebra K A] :
  (two_torsion_polynomial E A).disc ≠ 0 :=
λ hdisc, E.Δ.ne_zero $ mul_left_cancel₀ (pow_ne_zero 4 $ nonzero_of_invertible (2 : K)) $
  (algebra_map K A).injective
begin
  simp only [map_mul, map_pow, map_bit0, map_one, map_zero],
  linear_combination hdisc - two_torsion_polynomial.disc_eq E A
end

end torsion_polynomial

/-! ### Changes of variables -/

variables (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` for some `u ∈ Rˣ` and some `r, s, t ∈ R`.
  When `R` is a field, any two isomorphic long Weierstrass equations are related by this. -/
def change_of_variable : EllipticCurve R :=
{ a₁   := ↑u⁻¹ * (E.a₁ + 2 * s),
  a₂   := ↑u⁻¹ ^ 2 * (E.a₂ - s * E.a₁ + 3 * r - s ^ 2),
  a₃   := ↑u⁻¹ ^ 3 * (E.a₃ + r * E.a₁ + 2 * t),
  a₄   := ↑u⁻¹ ^ 4 * (E.a₄ - s * E.a₃ + 2 * r * E.a₂ - (t + r * s) * E.a₁ + 3 * r ^ 2 - 2 * s * t),
  a₆   := ↑u⁻¹ ^ 6 * (E.a₆ + r * E.a₄ + r ^ 2 * E.a₂ + r ^ 3 - t * E.a₃ - t ^ 2 - r * t * E.a₁),
  Δ    := u⁻¹ ^ 12 * E.Δ,
  Δ_eq := by { simp [-inv_pow], ring1 } }

namespace change_of_variable

@[simp] lemma a₁_eq : (E.change_of_variable u r s t).a₁ = ↑u⁻¹ * (E.a₁ + 2 * s) := rfl

@[simp] lemma a₂_eq :
  (E.change_of_variable u r s t).a₂ = ↑u⁻¹ ^ 2 * (E.a₂ - s * E.a₁ + 3 * r - s ^ 2) :=
rfl

@[simp] lemma a₃_eq : (E.change_of_variable u r s t).a₃ = ↑u⁻¹ ^ 3 * (E.a₃ + r * E.a₁ + 2 * t) :=
rfl

@[simp] lemma a₄_eq :
  (E.change_of_variable u r s t).a₄
    = ↑u⁻¹ ^ 4 * (E.a₄ - s * E.a₃ + 2 * r * E.a₂ - (t + r * s) * E.a₁ + 3 * r ^ 2 - 2 * s * t) :=
rfl

@[simp] lemma a₆_eq :
  (E.change_of_variable u r s t).a₆
    = ↑u⁻¹ ^ 6 * (E.a₆ + r * E.a₄ + r ^ 2 * E.a₂ + r ^ 3 - t * E.a₃ - t ^ 2 - r * t * E.a₁) :=
rfl

@[simp] lemma b₂_eq : (E.change_of_variable u r s t).b₂ = ↑u⁻¹ ^ 2 * (E.b₂ + 12 * r) :=
by { simp [change_of_variable], ring1 }

@[simp] lemma b₄_eq :
  (E.change_of_variable u r s t).b₄ = ↑u⁻¹ ^ 4 * (E.b₄ + r * E.b₂ + 6 * r ^ 2) :=
by { simp [change_of_variable], ring1 }

@[simp] lemma b₆_eq :
  (E.change_of_variable u r s t).b₆ = ↑u⁻¹ ^ 6 * (E.b₆ + 2 * r * E.b₄ + r ^ 2 * E.b₂ + 4 * r ^ 3) :=
by { simp [change_of_variable], ring1 }

@[simp] lemma b₈_eq :
  (E.change_of_variable u r s t).b₈
    = ↑u⁻¹ ^ 8 * (E.b₈ + 3 * r * E.b₆ + 3 * r ^ 2 * E.b₄ + r ^ 3 * E.b₂ + 3 * r ^ 4) :=
by { simp [change_of_variable], ring1 }

@[simp] lemma c₄_eq : (E.change_of_variable u r s t).c₄ = ↑u⁻¹ ^ 4 * E.c₄ :=
by { simp [change_of_variable], ring1 }

@[simp] lemma c₆_eq : (E.change_of_variable u r s t).c₆ = ↑u⁻¹ ^ 6 * E.c₆ :=
by { simp [change_of_variable], ring1 }

@[simp] lemma Δ_eq : (E.change_of_variable u r s t).Δ = u⁻¹ ^ 12 * E.Δ := rfl

@[simp] lemma j_eq : (E.change_of_variable u r s t).j = E.j :=
begin
  simp only [j, c₄, Δ_eq, inv_pow, mul_inv_rev, inv_inv, units.coe_mul, units.coe_pow,
    c₄_eq, b₂, b₄],
  have hu : (u * ↑u⁻¹ : R) ^ 12 = 1 := by rw [u.mul_inv, one_pow],
  linear_combination ↑E.Δ⁻¹ * ((E.a₁ ^ 2 + 4 * E.a₂) ^ 2 - 24 * (2 * E.a₄ + E.a₁ * E.a₃)) ^ 3 * hu
end

end change_of_variable

end EllipticCurve
