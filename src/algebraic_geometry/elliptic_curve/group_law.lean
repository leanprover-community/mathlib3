/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.elliptic_curve.EllipticCurve

import algebra.algebra.basic

/-!
# The group of rational points on an elliptic curve over a field
-/

open_locale classical
noncomputable theory

variables {F : Type*} [field F]
variables (E : EllipticCurve F)
variables (K : Type*) [field K] [algebra F K]

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

notation F↑K := algebra_map F K

/-- The group of `K`-rational points `E(K)` on an elliptic curve `E` over `F`,
    consisting of the point at infinity and the affine points satisfying a Weierstrass equation. -/
inductive point
| zero
| some (x y : K) (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
                    = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6)

notation E`⟮`K`⟯` := point E K

open point

----------------------------------------------------------------------------------------------------
/-! ## Zero in `E(K)` -/

section zero

/-- Zero in `E(K)`. -/
def zero' : E⟮K⟯ := zero

/-- `E(K)` has zero. -/
instance point.has_zero : has_zero (E⟮K⟯) := ⟨zero' E K⟩

/-- Zero in `E(K)` is zero. -/
@[simp]
lemma zero.def : (zero : E⟮K⟯) = 0 := rfl

/-- `E(K)` is inhabited. -/
instance point.inhabited : inhabited (E⟮K⟯) := ⟨zero' E K⟩

end zero

----------------------------------------------------------------------------------------------------
/-! ## Negation in `E(K)` -/

section negation

variables {x y : K}

/-- Negation of an affine point in `E(K)` is in `E(K)`. -/
lemma neg_some.weierstrass
  (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
     = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6) :
  (-y - (F↑K)E.a1 * x - (F↑K)E.a3) ^ 2 + (F↑K)E.a1 * x * (-y - (F↑K)E.a1 * x - (F↑K)E.a3)
    + (F↑K)E.a3 * (-y - (F↑K)E.a1 * x - (F↑K)E.a3)
    = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6 :=
by { rw [← w], ring }

/-- Negate an affine point in `E(K)`. -/
def neg_some.def
  (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
     = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6) : E⟮K⟯ :=
some x (-y - (F↑K)E.a1 * x - (F↑K)E.a3) $ neg_some.weierstrass E K w

/-- Negation in `E(K)`. -/
def neg : E⟮K⟯ → (E⟮K⟯)
| 0            := 0
| (some _ _ w) := neg_some.def E K w

/-- `E(K)` has negation. -/
instance point.has_neg : has_neg (E⟮K⟯) := ⟨neg E K⟩

/-- Negation of zero in `E(K)` is zero. -/
@[simp]
lemma neg_zero : -(0 : E⟮K⟯) = 0 := rfl

/-- Negation of an affine point in `E(K)` is an affine point. -/
@[simp]
lemma neg_some
  (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
     = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6) :
  -some x y w = some x (-y - (F↑K)E.a1 * x - (F↑K)E.a3) (neg_some.weierstrass E K w) :=
rfl

end negation

----------------------------------------------------------------------------------------------------
/-! ## Doubling in `E(K)` -/

section doubling

variables {x y l x' y' : K}

/-- Doubling of an affine point in `E(K)` is in `E(K)`. -/
lemma dbl_some.weierstrass
  (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
     = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6)
  (y_ne : 2 * y + (F↑K)E.a1 * x + (F↑K)E.a3 ≠ 0)
  (l_def : l  = (3 * x ^ 2 + 2 * (F↑K)E.a2 * x + (F↑K)E.a4 - (F↑K)E.a1 * y)
                * (2 * y + (F↑K)E.a1 * x + (F↑K)E.a3)⁻¹)
  (x_def : x' = l ^ 2 + (F↑K)E.a1 * l - (F↑K)E.a2 - 2 * x)
  (y_def : y' = -l * x' - (F↑K)E.a1 * x' - y + l * x - (F↑K)E.a3) :
  y' ^ 2 + (F↑K)E.a1 * x' * y' + (F↑K)E.a3 * y'
    = x' ^ 3 + (F↑K)E.a2 * x' ^ 2 + (F↑K)E.a4 * x' + (F↑K)E.a6 :=
begin
  -- rewrite Weierstrass equation as w(x, y) = 0
  rw [← sub_eq_zero] at w,
  -- rewrite y
  have y_rw :
    y' ^ 2 + (F↑K)E.a1 * x' * y' + (F↑K)E.a3 * y'
      = x' ^ 2 * (l ^ 2 + (F↑K)E.a1 * l)
      + x' * (-2 * x * l ^ 2 - (F↑K)E.a1 * x * l + 2 * y * l + (F↑K)E.a3 * l + (F↑K)E.a1 * y)
      + (x ^ 2 * l ^ 2 - 2 * x * y * l - (F↑K)E.a3 * x * l + y ^ 2 + (F↑K)E.a3 * y) :=
  by { rw [y_def], ring },
  -- rewrite x
  have x_rw :
    x' ^ 2 * (l ^ 2 + (F↑K)E.a1 * l)
      + x' * (-2 * x * l ^ 2 - (F↑K)E.a1 * x * l + 2 * y * l + (F↑K)E.a3 * l + (F↑K)E.a1 * y)
      + (x ^ 2 * l ^ 2 - 2 * x * y * l - (F↑K)E.a3 * x * l + y ^ 2 + (F↑K)E.a3 * y)
      - (x' ^ 3 + (F↑K)E.a2 * x' ^ 2 + (F↑K)E.a4 * x' + (F↑K)E.a6)
      = l * (l * (l * (2 * y + (F↑K)E.a1 * x + (F↑K)E.a3)
                  + (-3 * x ^ 2 + (F↑K)E.a1 ^ 2 * x - 2 * (F↑K)E.a2 * x + 3 * (F↑K)E.a1 * y
                     + (F↑K)E.a1 * (F↑K)E.a3 - (F↑K)E.a4))
             + (-6 * (F↑K)E.a1 * x ^ 2 - 6 * x * y - 3 * (F↑K)E.a1 * (F↑K)E.a2 * x
                - 3 * (F↑K)E.a3 * x + (F↑K)E.a1 ^ 2 * y - 2 * (F↑K)E.a2 * y - (F↑K)E.a1 * (F↑K)E.a4
                - (F↑K)E.a2 * (F↑K)E.a3))
        + (8 * x ^ 3 + 8 * (F↑K)E.a2 * x ^ 2 - 2 * (F↑K)E.a1 * x * y + y ^ 2 + 2 * (F↑K)E.a2 ^ 2 * x
           + 2 * (F↑K)E.a4 * x - (F↑K)E.a1 * (F↑K)E.a2 * y + (F↑K)E.a3 * y + (F↑K)E.a2 * (F↑K)E.a4
           - (F↑K)E.a6) :=
  by { rw [x_def], ring },
  -- rewrite l step 1
  have l_rw_1 :
    l * (2 * y + (F↑K)E.a1 * x + (F↑K)E.a3)
      + (-3 * x ^ 2 + (F↑K)E.a1 ^ 2 * x - 2 * (F↑K)E.a2 * x + 3 * (F↑K)E.a1 * y
         + (F↑K)E.a1 * (F↑K)E.a3 - (F↑K)E.a4)
      = (2 * y + (F↑K)E.a1 * x + (F↑K)E.a3) * (F↑K)E.a1 :=
  by { rw [l_def, inv_mul_cancel_right₀ y_ne], ring },
  -- rewrite l step 2
  have l_rw_2 :
    l * ((2 * y + (F↑K)E.a1 * x + (F↑K)E.a3) * (F↑K)E.a1)
      + (-6 * (F↑K)E.a1 * x ^ 2 - 6 * x * y - 3 * (F↑K)E.a1 * (F↑K)E.a2 * x - 3 * (F↑K)E.a3 * x
         + (F↑K)E.a1 ^ 2 * y - 2 * (F↑K)E.a2 * y - (F↑K)E.a1 * (F↑K)E.a4 - (F↑K)E.a2 * (F↑K)E.a3)
      = (2 * y + (F↑K)E.a1 * x + (F↑K)E.a3) * (-3 * x - (F↑K)E.a2) :=
  by { rw [← mul_assoc l, l_def, inv_mul_cancel_right₀ y_ne], ring },
  -- rewrite l step 3
  have l_rw_3 :
    l * ((2 * y + (F↑K)E.a1 * x + (F↑K)E.a3) * (-3 * x - (F↑K)E.a2))
      + (8 * x ^ 3 + 8 * (F↑K)E.a2 * x ^ 2 - 2 * (F↑K)E.a1 * x * y + y ^ 2 + 2 * (F↑K)E.a2 ^ 2 * x
         + 2 * (F↑K)E.a4 * x - (F↑K)E.a1 * (F↑K)E.a2 * y + (F↑K)E.a3 * y + (F↑K)E.a2 * (F↑K)E.a4
         - (F↑K)E.a6)
      = 0 :=
  by { rw [← mul_assoc l, l_def, inv_mul_cancel_right₀ y_ne, ← w], ring },
  -- rewrite Weierstrass equation as w'(x', y') = 0 and sequence steps
  rw [← sub_eq_zero, y_rw, x_rw, l_rw_1, l_rw_2, l_rw_3]
end

/-- Double an affine point `(x, y) ∈ E(K)` with `2y + a₁x + a₃ ≠ 0`. -/
def dbl_some.def
  (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
     = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6)
  (y_ne : 2 * y + (F↑K)E.a1 * x + (F↑K)E.a3 ≠ 0) : E⟮K⟯ :=
let l  := (3 * x ^ 2 + 2 * (F↑K)E.a2 * x + (F↑K)E.a4 - (F↑K)E.a1 * y)
          * (2 * y + (F↑K)E.a1 * x + (F↑K)E.a3)⁻¹,
    x' := l ^ 2 + (F↑K)E.a1 * l - (F↑K)E.a2 - 2 * x,
    y' := -l * x' - (F↑K)E.a1 * x' - y + l * x - (F↑K)E.a3
in  some x' y' $ dbl_some.weierstrass E K w y_ne rfl rfl rfl

/-- Doubling in `E(K)`. -/
def dbl : E⟮K⟯ → (E⟮K⟯)
| 0            := 0
| (some x y w) :=
if y_ne : 2 * y + (F↑K)E.a1 * x + (F↑K)E.a3 ≠ 0 then dbl_some.def E K w y_ne else 0

/-- Doubling of zero in `E(K)` is zero. -/
@[simp]
lemma dbl_zero : dbl E K 0 = 0 := rfl

/-- Doubling of an affine point `(x, y) ∈ E(K)` with `2y + a₁x + a₃ ≠ 0` is an affine point. -/
lemma dbl_some
  (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
     = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6)
  (y_ne : 2 * y + (F↑K)E.a1 * x + (F↑K)E.a3 ≠ 0) :
  dbl E K (some x y w) = dbl_some.def E K w y_ne :=
by rw [dbl, dif_pos y_ne]

/-- Doubling of an affine point `(x, y) ∈ E(K)` with `2y + a₁x + a₃ = 0` is zero. -/
@[simp]
lemma dbl_some'
  (w : y ^ 2 + (F↑K)E.a1 * x * y + (F↑K)E.a3 * y
     = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6)
  (y_eq : 2 * y + (F↑K)E.a1 * x + (F↑K)E.a3 = 0) :
  dbl E K (some x y w) = 0 :=
by rw [dbl, dif_neg (by { rw [not_not], exact y_eq })]

end doubling

----------------------------------------------------------------------------------------------------
/-! ## Addition in `E(K)` -/

section addition

variables {x₁ y₁ x₂ y₂ l x₃ y₃ : K}

/-- Addition of affine points in `E(K)` is in `E(K)`. -/
lemma add_some_some.weierstrass
  (w₁ : y₁ ^ 2 + (F↑K)E.a1 * x₁ * y₁ + (F↑K)E.a3 * y₁
      = x₁ ^ 3 + (F↑K)E.a2 * x₁ ^ 2 + (F↑K)E.a4 * x₁ + (F↑K)E.a6)
  (w₂ : y₂ ^ 2 + (F↑K)E.a1 * x₂ * y₂ + (F↑K)E.a3 * y₂
      = x₂ ^ 3 + (F↑K)E.a2 * x₂ ^ 2 + (F↑K)E.a4 * x₂ + (F↑K)E.a6)
  (x_ne : x₁ - x₂ ≠ 0)
  (l_def : l  = (y₁ - y₂) * (x₁ - x₂)⁻¹)
  (x_def : x₃ = l ^ 2 + (F↑K)E.a1 * l - (F↑K)E.a2 - x₁ - x₂)
  (y_def : y₃ = -l * x₃ - (F↑K)E.a1 * x₃ - y₁ + l * x₁ - (F↑K)E.a3) :
  y₃ ^ 2 + (F↑K)E.a1 * x₃ * y₃ + (F↑K)E.a3 * y₃
    = x₃ ^ 3 + (F↑K)E.a2 * x₃ ^ 2 + (F↑K)E.a4 * x₃ + (F↑K)E.a6 :=
begin
  -- rewrite Weierstrass equations as w₁(x₁, y₁) = 0 and w₂(x₂, y₂) = 0
  rw [← sub_eq_zero] at w₁ w₂,
  -- rewrite y
  have y_rw :
    y₃ ^ 2 + (F↑K)E.a1 * x₃ * y₃ + (F↑K)E.a3 * y₃
      = x₃ ^ 2 * (l ^ 2 + (F↑K)E.a1 * l)
      + x₃ * (-2 * x₁ * l ^ 2 - (F↑K)E.a1 * x₁ * l + 2 * y₁ * l + (F↑K)E.a3 * l + (F↑K)E.a1 * y₁)
      + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (F↑K)E.a3 * x₁ * l + y₁ ^ 2 + (F↑K)E.a3 * y₁) :=
  by { rw [y_def], ring },
  -- rewrite x
  have x_rw :
    x₃ ^ 2 * (l ^ 2 + (F↑K)E.a1 * l)
      + x₃ * (-2 * x₁ * l ^ 2 - (F↑K)E.a1 * x₁ * l + 2 * y₁ * l + (F↑K)E.a3 * l + (F↑K)E.a1 * y₁)
      + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (F↑K)E.a3 * x₁ * l + y₁ ^ 2 + (F↑K)E.a3 * y₁)
      - (x₃ ^ 3 + (F↑K)E.a2 * x₃ ^ 2 + (F↑K)E.a4 * x₃ + (F↑K)E.a6)
      = l * (l * (l * (l * (x₁ - x₂) * (-1)
                       + (-(F↑K)E.a1 * x₁ + 2 * (F↑K)E.a1 * x₂ + 2 * y₁ + (F↑K)E.a3))
                  + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (F↑K)E.a1 ^ 2 * x₂ - 2 * (F↑K)E.a2 * x₂
                     + 3 * (F↑K)E.a1 * y₁ + (F↑K)E.a1 * (F↑K)E.a3 - (F↑K)E.a4))
             + (-(F↑K)E.a1 * x₁ ^ 2 - 3 * (F↑K)E.a1 * x₁ * x₂ - 4 * x₁ * y₁ - 2 * (F↑K)E.a1 * x₂ ^ 2
                - 2 * x₂ * y₁ - (F↑K)E.a1 * (F↑K)E.a2 * x₁ - 2 * (F↑K)E.a3 * x₁
                - 2 * (F↑K)E.a1 * (F↑K)E.a2 * x₂ - (F↑K)E.a3 * x₂ + (F↑K)E.a1 ^ 2 * y₁
                - 2 * (F↑K)E.a2 * y₁ - (F↑K)E.a1 * (F↑K)E.a4 - (F↑K)E.a2 * (F↑K)E.a3))
        + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (F↑K)E.a2 * x₁ ^ 2
           + 4 * (F↑K)E.a2 * x₁ * x₂ - (F↑K)E.a1 * x₁ * y₁ + 2 * (F↑K)E.a2 * x₂ ^ 2
           - (F↑K)E.a1 * x₂ * y₁ + y₁ ^ 2 + (F↑K)E.a2 ^ 2 * x₁ + (F↑K)E.a4 * x₁ + (F↑K)E.a2 ^ 2 * x₂
           + (F↑K)E.a4 * x₂ - (F↑K)E.a1 * (F↑K)E.a2 * y₁ + (F↑K)E.a3 * y₁ + (F↑K)E.a2 * (F↑K)E.a4
           - (F↑K)E.a6) :=
  by { rw [x_def], ring },
  -- rewrite l auxiliary tactic
  have l_rw : ∀ a b c : K, l * a + b = c ↔ (y₁ - y₂) * a + (x₁ - x₂) * b + 0 = (x₁ - x₂) * c + 0 :=
  by { intros a b c, rw [← mul_right_inj' x_ne, mul_add (x₁ - x₂), ← mul_assoc (x₁ - x₂) l],
       rw [mul_comm (x₁ - x₂) l, l_def, inv_mul_cancel_right₀ x_ne, ← add_left_inj (0 : K)] },
  -- rewrite l step 1
  have l_rw_1 :
    l * (x₁ - x₂) * (-1) + (-(F↑K)E.a1 * x₁ + 2 * (F↑K)E.a1 * x₂ + 2 * y₁ + (F↑K)E.a3)
      = -(F↑K)E.a1 * x₁ + 2 * (F↑K)E.a1 * x₂ + 2 * y₁ + (F↑K)E.a3 - y₁ + y₂ :=
  by { rw [l_def, inv_mul_cancel_right₀ x_ne], ring },
  -- rewrite l step 2
  have l_rw_2 :
    l * (-(F↑K)E.a1 * x₁ + 2 * (F↑K)E.a1 * x₂ + 2 * y₁ + (F↑K)E.a3 - y₁ + y₂)
      + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (F↑K)E.a1 ^ 2 * x₂ - 2 * (F↑K)E.a2 * x₂
         + 3 * (F↑K)E.a1 * y₁ + (F↑K)E.a1 * (F↑K)E.a3 - (F↑K)E.a4)
      = 2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (F↑K)E.a2 * x₁ + (F↑K)E.a1 ^ 2 * x₂ + (F↑K)E.a2 * x₂
      - 2 * (F↑K)E.a2 * x₂ + (F↑K)E.a1 * y₁ + (F↑K)E.a1 * y₂ + (F↑K)E.a1 * (F↑K)E.a3 :=
  by { rw [l_rw], nth_rewrite_rhs 0 [← w₁], nth_rewrite_lhs 0 [← w₂], ring },
  -- rewrite l step 3
  have l_rw_3 :
    l * (2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (F↑K)E.a2 * x₁ + (F↑K)E.a1 ^ 2 * x₂ + (F↑K)E.a2 * x₂
         - 2 * (F↑K)E.a2 * x₂ + (F↑K)E.a1 * y₁ + (F↑K)E.a1 * y₂ + (F↑K)E.a1 * (F↑K)E.a3)
      + (-(F↑K)E.a1 * x₁ ^ 2 - 3 * (F↑K)E.a1 * x₁ * x₂ - 4 * x₁ * y₁ - 2 * (F↑K)E.a1 * x₂ ^ 2
         - 2 * x₂ * y₁ - (F↑K)E.a1 * (F↑K)E.a2 * x₁ - 2 * (F↑K)E.a3 * x₁
         - 2 * (F↑K)E.a1 * (F↑K)E.a2 * x₂ - (F↑K)E.a3 * x₂ + (F↑K)E.a1 ^ 2 * y₁ - 2 * (F↑K)E.a2 * y₁
         - (F↑K)E.a1 * (F↑K)E.a4 - (F↑K)E.a2 * (F↑K)E.a3)
      = -2 * (F↑K)E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (F↑K)E.a1 * x₂ ^ 2 - x₂ * y₁
        - x₂ * y₂ - 2 * (F↑K)E.a3 * x₁ - (F↑K)E.a1 * (F↑K)E.a2 * x₂ - (F↑K)E.a3 * x₂
        - (F↑K)E.a2 * y₁ - (F↑K)E.a2 * y₂ - (F↑K)E.a2 * (F↑K)E.a3 :=
  by { apply_fun ((*) ((F↑K)E.a1)) at w₁ w₂, rw [mul_zero] at w₁ w₂, rw [l_rw],
       nth_rewrite_rhs 0 [← w₁], nth_rewrite_lhs 0 [← w₂], ring },
  -- rewrite l step 4
  have l_rw_4 :
    l * (-2 * (F↑K)E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (F↑K)E.a1 * x₂ ^ 2 - x₂ * y₁
         - x₂ * y₂ - 2 * (F↑K)E.a3 * x₁ - (F↑K)E.a1 * (F↑K)E.a2 * x₂ - (F↑K)E.a3 * x₂
         - (F↑K)E.a2 * y₁ - (F↑K)E.a2 * y₂ - (F↑K)E.a2 * (F↑K)E.a3)
      + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (F↑K)E.a2 * x₁ ^ 2
         + 4 * (F↑K)E.a2 * x₁ * x₂ - (F↑K)E.a1 * x₁ * y₁ + 2 * (F↑K)E.a2 * x₂ ^ 2
         - (F↑K)E.a1 * x₂ * y₁ + y₁ ^ 2 + (F↑K)E.a2 ^ 2 * x₁ + (F↑K)E.a4 * x₁ + (F↑K)E.a2 ^ 2 * x₂
         + (F↑K)E.a4 * x₂ - (F↑K)E.a1 * (F↑K)E.a2 * y₁ + (F↑K)E.a3 * y₁ + (F↑K)E.a2 * (F↑K)E.a4
         - (F↑K)E.a6)
      = 0 :=
  by { apply_fun ((*) (x₁ + 2 * x₂ + (F↑K)E.a2)) at w₁,
       apply_fun ((*) (2 * x₁ + x₂ + (F↑K)E.a2)) at w₂, rw [mul_zero] at w₁ w₂, rw [l_rw],
       nth_rewrite_lhs 0 [← w₁], nth_rewrite_rhs 1 [← w₂], ring },
  -- rewrite Weierstrass equation as w₃(x₃, y₃) = 0 and sequence steps
  rw [← sub_eq_zero, y_rw, x_rw, l_rw_1, l_rw_2, l_rw_3, l_rw_4]
end

/-- Add affine points in `E(K)`. -/
def add_some_some.def
  (w₁ : y₁ ^ 2 + (F↑K)E.a1 * x₁ * y₁ + (F↑K)E.a3 * y₁
      = x₁ ^ 3 + (F↑K)E.a2 * x₁ ^ 2 + (F↑K)E.a4 * x₁ + (F↑K)E.a6)
  (w₂ : y₂ ^ 2 + (F↑K)E.a1 * x₂ * y₂ + (F↑K)E.a3 * y₂
      = x₂ ^ 3 + (F↑K)E.a2 * x₂ ^ 2 + (F↑K)E.a4 * x₂ + (F↑K)E.a6)
  (x_ne : x₁ - x₂ ≠ 0) : E⟮K⟯ :=
let l  := (y₁ - y₂) * (x₁ - x₂)⁻¹,
    x₃ := l ^ 2 + (F↑K)E.a1 * l - (F↑K)E.a2 - x₁ - x₂,
    y₃ := -l * x₃ - (F↑K)E.a1 * x₃ - y₁ + l * x₁ - (F↑K)E.a3
in  some x₃ y₃ $ add_some_some.weierstrass E K w₁ w₂ x_ne rfl rfl rfl

/-- For all affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)`,
    if `x₁ = x₂` and `y₁ + y₂ + a₁x₂ + a₃ ≠ 0` then `y₁ = y₂`. -/
private lemma add_some_some_rw
  (w₁ : y₁ ^ 2 + (F↑K)E.a1 * x₁ * y₁ + (F↑K)E.a3 * y₁
      = x₁ ^ 3 + (F↑K)E.a2 * x₁ ^ 2 + (F↑K)E.a4 * x₁ + (F↑K)E.a6)
  (w₂ : y₂ ^ 2 + (F↑K)E.a1 * x₂ * y₂ + (F↑K)E.a3 * y₂
      = x₂ ^ 3 + (F↑K)E.a2 * x₂ ^ 2 + (F↑K)E.a4 * x₂ + (F↑K)E.a6)
  (x_eq : x₁ - x₂ = 0) (y_ne : y₁ + y₂ + (F↑K)E.a1 * x₂ + (F↑K)E.a3 ≠ 0) :
  2 * y₁ + (F↑K)E.a1 * x₁ + (F↑K)E.a3 ≠ 0 :=
begin
  rw [sub_eq_zero] at x_eq,
  subst x_eq,
  have y_rw :
    y₁ ^ 2 + (F↑K)E.a1 * x₁ * y₁ + (F↑K)E.a3 * y₁ - (y₂ ^ 2 + (F↑K)E.a1 * x₁ * y₂ + (F↑K)E.a3 * y₂)
      = (y₁ - y₂) * (y₁ + y₂ + (F↑K)E.a1 * x₁ + (F↑K)E.a3) :=
  by ring,
  rw [← w₂, ← sub_eq_zero, y_rw, mul_eq_zero, sub_eq_zero] at w₁,
  cases w₁,
  { subst w₁,
    rw [two_mul],
    exact y_ne },
  { contradiction },
end

/-- Addition in `E(K)`. -/
def add : E⟮K⟯ → (E⟮K⟯) → (E⟮K⟯)
| 0               P               := P
| P               0               := P
| (some x₁ y₁ w₁) (some x₂ y₂ w₂) :=
if x_ne : x₁ - x₂ ≠ 0 then
  add_some_some.def E K w₁ w₂ x_ne
else if y_ne : y₁ + y₂ + (F↑K)E.a1 * x₂ + (F↑K)E.a3 ≠ 0 then
  dbl_some.def E K w₁ $ add_some_some_rw E K w₁ w₂ (by { rw [not_not] at x_ne, exact x_ne }) y_ne
else
  0

/-- `E(K)` has addition. -/
instance point.has_add : has_add (E⟮K⟯) := ⟨add E K⟩

/-- Addition of zero and `P ∈ E(K)` is `P`. -/
@[simp]
lemma zero_add (P : E⟮K⟯) : 0 + P = P := by cases P; refl

/-- Addition of `P ∈ E(K)` and zero is `P`. -/
@[simp]
lemma add_zero (P : E⟮K⟯) : P + 0 = P := by cases P; refl

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)` with `x₁ - x₂ ≠ 0` is an affine point. -/
lemma add_some_some
  (w₁ : y₁ ^ 2 + (F↑K)E.a1 * x₁ * y₁ + (F↑K)E.a3 * y₁
      = x₁ ^ 3 + (F↑K)E.a2 * x₁ ^ 2 + (F↑K)E.a4 * x₁ + (F↑K)E.a6)
  (w₂ : y₂ ^ 2 + (F↑K)E.a1 * x₂ * y₂ + (F↑K)E.a3 * y₂
      = x₂ ^ 3 + (F↑K)E.a2 * x₂ ^ 2 + (F↑K)E.a4 * x₂ + (F↑K)E.a6)
  (x_ne : x₁ - x₂ ≠ 0) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂ = add_some_some.def E K w₁ w₂ x_ne :=
by { simp only [has_add.add, add, dif_pos x_ne] }

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)` with `x₁ - x₂ = 0`
    and `y₁ + y₂ + a₁x₂ + a₃ ≠ 0` is doubling of `(x₁, y₁)`. -/
lemma add_some_some'
  (w₁ : y₁ ^ 2 + (F↑K)E.a1 * x₁ * y₁ + (F↑K)E.a3 * y₁
      = x₁ ^ 3 + (F↑K)E.a2 * x₁ ^ 2 + (F↑K)E.a4 * x₁ + (F↑K)E.a6)
  (w₂ : y₂ ^ 2 + (F↑K)E.a1 * x₂ * y₂ + (F↑K)E.a3 * y₂
      = x₂ ^ 3 + (F↑K)E.a2 * x₂ ^ 2 + (F↑K)E.a4 * x₂ + (F↑K)E.a6)
  (x_eq : x₁ - x₂ = 0) (y_ne : y₁ + y₂ + (F↑K)E.a1 * x₂ + (F↑K)E.a3 ≠ 0) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂ = dbl_some.def E K w₁ (add_some_some_rw E K w₁ w₂ x_eq y_ne) :=
by { simp only [has_add.add, add, dif_neg (by { rw [not_not], exact x_eq }), dif_pos y_ne] }

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)` with `x₁ - x₂ = 0`
    and `y₁ + y₂ + a₁x₂ + a₃ = 0` is zero. -/
@[simp]
lemma add_some_some''
  (w₁ : y₁ ^ 2 + (F↑K)E.a1 * x₁ * y₁ + (F↑K)E.a3 * y₁
      = x₁ ^ 3 + (F↑K)E.a2 * x₁ ^ 2 + (F↑K)E.a4 * x₁ + (F↑K)E.a6)
  (w₂ : y₂ ^ 2 + (F↑K)E.a1 * x₂ * y₂ + (F↑K)E.a3 * y₂
      = x₂ ^ 3 + (F↑K)E.a2 * x₂ ^ 2 + (F↑K)E.a4 * x₂ + (F↑K)E.a6)
  (x_eq : x₁ - x₂ = 0) (y_eq : y₁ + y₂ + (F↑K)E.a1 * x₂ + (F↑K)E.a3 = 0) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂ = 0 :=
by { simp only [has_add.add, add, dif_neg (by { rw [not_not], exact x_eq }),
                dif_neg (by { rw [not_not], exact y_eq })] }

end addition

----------------------------------------------------------------------------------------------------
/-! ## Axioms in `E(K)` -/

section add_comm_group

/-- Left negation in `E(K)`. -/
@[simp]
lemma add_left_neg (P : E⟮K⟯) : -P + P = 0 :=
begin
  cases P,
  { refl },
  { rw [neg_some, add_some_some'']; ring }
end

/-- Commutativity in `E(K)`. -/
lemma add_comm (P Q : E⟮K⟯) : P + Q = Q + P :=
begin
  cases P,
  { cases Q; refl },
  { cases Q,
    { refl },
    { sorry } }
end

/-- Associativity in `E(K)`. -/
lemma add_assoc (P Q R : E⟮K⟯) : (P + Q) + R = P + (Q + R) :=
begin
  cases P,
  { cases Q,
    { cases R; refl },
    { cases R,
      { refl },
      { rw [zero.def, zero_add, zero_add] } } },
  { cases Q,
    { cases R; refl },
    { cases R,
      { rw [zero.def, add_zero, add_zero] },
      { sorry } } }
end

/-- `E(K)` is an additive commutative group. -/
instance point.add_comm_group : add_comm_group (E⟮K⟯) :=
{ zero         := 0,
  neg          := neg E K,
  add          := add E K,
  zero_add     := zero_add E K,
  add_zero     := add_zero E K,
  add_left_neg := add_left_neg E K,
  add_comm     := add_comm E K,
  add_assoc    := add_assoc E K }

end add_comm_group

----------------------------------------------------------------------------------------------------

end EllipticCurve
