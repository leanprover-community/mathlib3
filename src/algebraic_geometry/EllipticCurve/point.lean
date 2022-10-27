/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.EllipticCurve
import field_theory.galois -- temporary import to enable point notation
import tactic.field_simp

/-!
# The group of rational points on an elliptic curve over a field

Let $E$ be an elliptic curve over a field $F$. For a field extension $K$ of $F$, a $K$-rational
point on $E$ is simply a point $[X:Y:Z] \in \mathbb{P}^2$ over $K$ in the projective plane cubic
defined by $Y^2Z + a_1XYZ + a_3YZ^2 = X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3$. This file defines the type
of $K$-rational points on $E$ as an inductive, since any such point either lies in the affine chart
$Z \ne 0$ and satisfies the Weierstrass equation obtained by setting $x = X/Z$ and $y = Y/Z$, or is
the unique point at infinity $\mathcal{O} = [0:1:0] \in \mathbb{P}^2$ obtained by setting $Z = 0$.

The set of $K$-rational points on $E$ forms an abelian group under a chord-and-tangent process.
 * The identity point is $\mathcal{O}$.
 * Given a point $P$, its negation $-P$ is defined to be the unique third point of intersection
    between $E$ and the line joining $\mathcal{O}$ and $P$, which exists by Bézout's theorem.
    Explicitly, if $P = (x, y)$, then $-P = (x, -y - a_1x - a_3)$.
 * Given two points $P$ and $Q$, their addition $P + Q$ is defined to be the negation of the unique
    third point of intersection between $E$ and the line joining $P$ and $Q$, which again exists by
    Bézout's theorem. Explicitly, let $P = (x_1, y_1)$ and $Q = (x_2, y_2)$. If $x_1 = x_2$ and
    $P \ne -Q$, then this line is the tangent of $E$ at $P = Q$ and has a well-defined gradient
    $\ell = (3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$. Otherwise $P \ne Q$ and this
    line has a well-defined gradient $\ell = (y_1 - y_2) / (x_1 - x_2)$. The $x$-coordinate of
    $P + Q$ is then the unique third solution of the equation obtained by substituting the line
    $y = \ell(x - x_1) + y_1$ into the Weierstrass equation, and can be written down explicitly by
    inspecting the $x^2$ terms of this equation as $x = \ell^2 + a_1\ell - a_2 - x_1 - x_2$. The
    $y$-coordinate of $P + Q$, after applying the final negation that maps $y$ to $-y - a_1x - a_3$,
    is precisely $y = -(\ell(x - x_1) + y_1) - x - a_3$.
The group law on this set is then uniquely determined by these constructions. This file defines the
group operations by explicit equations and proves that the set is an abelian group (TODO).

## Main definitions

 * `EllipticCurve.point`: a `K`-rational point on `E`.
 * `EllipticCurve.point.add`: addition of two `K`-rational points on `E`.

## Main statements

 * `EllipticCurve.point.add_comm`: addition of two `K`-rational points on `E` is commutative.
 * TODO: addition of two `K`-rational points on `E` is associative (HARD), and hence forms a group.

## Notations

 * `E⟮K⟯`: the group of `K`-rational points on an elliptic curve `E`.

## Implementation notes

The proofs of `EllipticCurve.point.weierstrass_dbl'`, `EllipticCurve.point.weierstrass_add'`, and
`EllipticCurve.point.add_assoc` (TODO) are slow due to the sheer size of the polynomials involved,
but they can be hastened considerably by breaking the computations into multiple steps if necessary.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, group law
-/

universes u v

variables {F : Type u} [field F] (E : EllipticCurve F) {K : Type v} [field K] [algebra F K]

namespace EllipticCurve

/-- The proposition that an affine point $(x, y)$ lies in `E`. In other words, it satisfies the
Weierstrass equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$. -/
@[simp] def weierstrass (x y : K) : Prop :=
y ^ 2 + ↑E.a₁ * x * y + ↑E.a₃ * y = x ^ 3 + ↑E.a₂ * x ^ 2 + ↑E.a₄ * x + ↑E.a₆

variables (K)

/-- The group of `K`-rational points `E⟮K⟯` on an elliptic curve `E` over `F`. This consists of the
unique point at infinity `EllipticCurve.point.zero`and the affine points `EllipticCurve.point.some`
satisfying the Weierstrass equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$. -/
inductive point
| zero
| some (x y : K) (h : E.weierstrass x y)

localized "notation E⟮K⟯ := point E K" in EllipticCurve

variables {E K}

namespace point

instance : inhabited E⟮K⟯ := ⟨zero⟩

section zero

/-!
### Zero in `E⟮K⟯`

Use `0` instead of `EllipticCurve.point.zero`.
-/

instance : has_zero E⟮K⟯ := ⟨zero⟩

@[simp] lemma zero_def : zero = (0 : E⟮K⟯) := rfl

end zero

section negation

/-!
### Negation in `E⟮K⟯`

Given `P : E⟮K⟯`, use `-P` instead of `neg P`.
-/

variables {x y : K} (h : E.weierstrass x y)

include h

/-- The $y$-coordinate of the negation of an affine point. -/
@[simp, nolint unused_arguments] def neg_y : K := -y - ↑E.a₁ * x - ↑E.a₃

/-- The negation of an affine point in `E` lies in `E`. -/
lemma weierstrass_neg : E.weierstrass x $ neg_y h :=
by { rw [weierstrass] at h, rw [weierstrass, neg_y, ← h], ring1 }

omit h

/-- Negation in `E⟮K⟯`. Given `P : E⟮K⟯`, use `-P` instead of `neg P`. -/
@[simp] def neg : E⟮K⟯ → E⟮K⟯
| 0            := 0
| (some x y h) := some x (neg_y h) $ weierstrass_neg h

instance : has_neg E⟮K⟯ := ⟨neg⟩

lemma neg_def (P : E⟮K⟯) : -P = neg P := rfl

@[simp] lemma neg_zero : -0 = (0 : E⟮K⟯) := rfl

@[simp] lemma neg_some : -some x y h = some x (neg_y h) (weierstrass_neg h) := rfl

@[simp] lemma neg_neg (P : E⟮K⟯) : -(-P) = P := by { cases P, { refl }, { simp, ring1 } }

instance : has_involutive_neg E⟮K⟯ := ⟨neg, neg_neg⟩

end negation

section doubling

/-!
### Doubling in `E⟮K⟯`

Given `P : E⟮K⟯`, use `2 • P` instead of `P + P` (TODO: immediate once `add_comm_group` is defined).
-/

variables {x y : K} (h : E.weierstrass x y)

include h

/-- The gradient of the tangent line of `E` at an affine point $(x, y)$. This is not well-defined
only in the case of $y = -y - a_1x - a_3$, which is precisely when the tangent is vertical. -/
@[simp] def dbl_L : K := (3 * x ^ 2 + 2 * ↑E.a₂ * x + ↑E.a₄ - ↑E.a₁ * y) / (y - neg_y h)

/-- The $x$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
@[simp] def dbl_x : K := dbl_L h ^ 2 + ↑E.a₁ * dbl_L h - ↑E.a₂ - 2 * x

/-- The $y$-coordinate of the doubling of an affine point whose tangent is not vertical,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$. -/
@[simp] def dbl_y' : K := dbl_L h * (dbl_x h - x) + y

/-- The $y$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
@[simp] def dbl_y : K := -dbl_y' h - ↑E.a₁ * dbl_x h - ↑E.a₃

/-- The doubling of an affine point in `E` whose tangent is not vertical,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$, lies in `E`. -/
lemma weierstrass_dbl' (hy : y ≠ neg_y h) : E.weierstrass (dbl_x h) (dbl_y' h) :=
begin
  rw [weierstrass, ← sub_eq_zero],
  convert_to
    dbl_L h * (dbl_L h * (dbl_L h * (y - neg_y h)
                          + (-3 * x ^ 2 + ↑E.a₁ ^ 2 * x - 2 * ↑E.a₂ * x + 3 * ↑E.a₁ * y
                              + ↑E.a₁ * ↑E.a₃ - ↑E.a₄))
                + (-6 * ↑E.a₁ * x ^ 2 - 6 * x * y - 3 * ↑E.a₁ * ↑E.a₂ * x - 3 * ↑E.a₃ * x
                    + ↑E.a₁ ^ 2 * y - 2 * ↑E.a₂ * y - ↑E.a₁ * ↑E.a₄ - ↑E.a₂ * ↑E.a₃))
    + (8 * x ^ 3 + 8 * ↑E.a₂ * x ^ 2 - 2 * ↑E.a₁ * x * y + y ^ 2 + 2 * ↑E.a₂ ^ 2 * x + 2 * ↑E.a₄ * x
        - ↑E.a₁ * ↑E.a₂ * y + ↑E.a₃ * y + ↑E.a₂ * ↑E.a₄ - ↑E.a₆) = 0,
  { simp only [dbl_x, dbl_y', neg_y], ring1 },
  field_simp [-neg_y, sub_ne_zero_of_ne hy],
  rw [weierstrass] at h,
  linear_combination (2 * y + ↑E.a₁ * x + ↑E.a₃) ^ 2 * h
    with { normalization_tactic := `[rw [neg_y], ring1] }
end

/-- The doubling of an affine point in `E` whose tangent is not vertical lies in `E`. -/
lemma weierstrass_dbl (hy : y ≠ neg_y h) : E.weierstrass (dbl_x h) (dbl_y h) :=
weierstrass_neg $ weierstrass_dbl' h hy

end doubling

section addition

/-!
### Addition in `E⟮K⟯`

Given `P Q : E⟮K⟯`, use `P + Q` instead of `add P Q`.
-/

variables {x₁ y₁ x₂ y₂ : K} (h₁ : E.weierstrass x₁ y₁) (h₂ : E.weierstrass x₂ y₂)

include h₁ h₂

/-- The gradient of the line joining two affine points $(x_1, y_1)$ and $(x_2, y_2)$. This is not
well-defined only in the case of $x_1 = x_2$, where the line becomes a tangent of `E`. -/
@[simp, nolint unused_arguments] def add_L : K := (y₁ - y₂) / (x₁ - x₂)

/-- The $x$-coordinate of the addition of two affine points with distinct $x$-coordinates. -/
@[simp] def add_x : K := add_L h₁ h₂ ^ 2 + ↑E.a₁ * add_L h₁ h₂ - ↑E.a₂ - x₁ - x₂

/-- The $y$-coordinate of the addition of two affine points with distinct $x$-coordinates,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$. -/
@[simp] def add_y' : K := add_L h₁ h₂ * (add_x h₁ h₂ - x₁) + y₁

/-- The $y$-coordinate of the addition of two affine points with distinct $x$-coordinates. -/
@[simp] def add_y : K := -add_y' h₁ h₂ - ↑E.a₁ * add_x h₁ h₂ - ↑E.a₃

/-- The addition of two affine points in `E` with distinct $x$-coordinates,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$, lies in `E`. -/
lemma weierstrass_add' (hx : x₁ ≠ x₂) : E.weierstrass (add_x h₁ h₂) (add_y' h₁ h₂) :=
begin
  rw [weierstrass, ← sub_eq_zero],
  convert_to
    add_L h₁ h₂ * (add_L h₁ h₂ * (add_L h₁ h₂ * (add_L h₁ h₂ * (x₁ - x₂) * -1
                                                  + (-↑E.a₁ * x₁ + 2 * ↑E.a₁ * x₂ + 2 * y₁ + ↑E.a₃))
                                  + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + ↑E.a₁ ^ 2 * x₂
                                      - 2 * ↑E.a₂ * x₂ + 3 * ↑E.a₁ * y₁ + ↑E.a₁ * ↑E.a₃ - ↑E.a₄))
                    + (-↑E.a₁ * x₁ ^ 2 - 3 * ↑E.a₁ * x₁ * x₂ - 4 * x₁ * y₁ - 2 * ↑E.a₁ * x₂ ^ 2
                        - 2 * x₂ * y₁ - ↑E.a₁ * ↑E.a₂ * x₁ - 2 * ↑E.a₃ * x₁ - 2 * ↑E.a₁ * ↑E.a₂ * x₂
                        - ↑E.a₃ * x₂ + ↑E.a₁ ^ 2 * y₁ - 2 * ↑E.a₂ * y₁ - ↑E.a₁ * ↑E.a₄
                        - ↑E.a₂ * ↑E.a₃))
    + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * ↑E.a₂ * x₁ ^ 2
        + 4 * ↑E.a₂ * x₁ * x₂ - ↑E.a₁ * x₁ * y₁ + 2 * ↑E.a₂ * x₂ ^ 2 - ↑E.a₁ * x₂ * y₁ + y₁ ^ 2
        + ↑E.a₂ ^ 2 * x₁ + ↑E.a₄ * x₁ + ↑E.a₂ ^ 2 * x₂ + ↑E.a₄ * x₂ - ↑E.a₁ * ↑E.a₂ * y₁
        + ↑E.a₃ * y₁ + ↑E.a₂ * ↑E.a₄ - ↑E.a₆) = 0,
  { simp only [add_x, add_y'], ring1 },
  field_simp [sub_ne_zero_of_ne hx],
  rw [weierstrass] at h₁ h₂,
  linear_combination
    -((x₁ - x₂) ^ 2 * (x₁ + 2 * x₂ + ↑E.a₂) - (x₁ - x₂) * (y₁ - y₂) * ↑E.a₁ - (y₁ - y₂) ^ 2) * h₁
    + ((x₁ - x₂) ^ 2 * (2 * x₁ + x₂ + ↑E.a₂) - (x₁ - x₂) * (y₁ - y₂) * ↑E.a₁ - (y₁ - y₂) ^ 2) * h₂
    with { normalization_tactic := `[ring1] }
end

/-- The addition of two affine points in `E` with distinct $x$-coordinates lies in `E`. -/
lemma weierstrass_add (hx : x₁ ≠ x₂) : E.weierstrass (add_x h₁ h₂) (add_y h₁ h₂) :=
weierstrass_neg $ weierstrass_add' h₁ h₂ hx

private lemma y_eq_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) : y₁ = y₂ :=
begin
  rw [weierstrass] at h₂,
  rw [weierstrass, hx, ← h₂, ← sub_eq_zero] at h₁,
  apply eq_of_sub_eq_zero ∘ eq_zero_of_ne_zero_of_mul_right_eq_zero (sub_ne_zero.mpr hy),
  convert h₁,
  rw [neg_y],
  ring1
end

private lemma y_ne_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) : y₁ ≠ neg_y h₁ :=
by { convert hy, exact y_eq_of_y_ne h₁ h₂ hx hy }

omit h₁ h₂

open_locale classical

/-- Addition in `E⟮K⟯`. Given `P Q : E⟮K⟯`, use `P + Q` instead of `add P Q`. -/
@[simp] noncomputable def add : E⟮K⟯ → E⟮K⟯ → E⟮K⟯
| 0               P               := P
| P               0               := P
| (some x₁ y₁ h₁) (some x₂ y₂ h₂) :=
if hx : x₁ = x₂ then if hy : y₁ = neg_y h₂ then 0
else some _ _ $ weierstrass_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy
else some _ _ $ weierstrass_add h₁ h₂ hx

noncomputable instance : has_add E⟮K⟯ := ⟨add⟩

lemma add_def (P Q : E⟮K⟯) : P + Q = add P Q := rfl

@[simp] lemma zero_add (P : E⟮K⟯) : 0 + P = P := by cases P; refl

@[simp] lemma add_zero (P : E⟮K⟯) : P + 0 = P := by cases P; refl

@[simp] lemma some_add_some_of_y_eq (hx : x₁ = x₂) (hy : y₁ = neg_y h₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = 0 :=
by rw [add_def, add, dif_pos hx, dif_pos hy]

@[simp] lemma some_add_self_of_y_eq (hy : y₁ = neg_y h₁) : some x₁ y₁ h₁ + some x₁ y₁ h₁ = 0 :=
some_add_some_of_y_eq h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = some _ _ (weierstrass_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
by rw [add_def, add, dif_pos hx, dif_neg hy]

lemma some_add_some_of_y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = -some _ _ (weierstrass_dbl' h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
some_add_some_of_y_ne h₁ h₂ hx hy

@[simp] lemma some_add_self_of_y_ne (hy : y₁ ≠ neg_y h₁) :
  some x₁ y₁ h₁ + some x₁ y₁ h₁ = some _ _ (weierstrass_dbl h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

lemma some_add_self_of_y_ne' (hy : y₁ ≠ neg_y h₁) :
  some x₁ y₁ h₁ + some x₁ y₁ h₁ = -some _ _ (weierstrass_dbl' h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_x_ne (hx : x₁ ≠ x₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = some _ _ (weierstrass_add h₁ h₂ hx) :=
by rw [add_def, add, dif_neg hx]

lemma some_add_some_of_x_ne' (hx : x₁ ≠ x₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = -some _ _ (weierstrass_add' h₁ h₂ hx) :=
some_add_some_of_x_ne h₁ h₂ hx

end addition

section add_comm_group

/-!
### Axioms in `E⟮K⟯`

TODO: Associativity of addition.
-/

@[simp] lemma add_left_neg (P : E⟮K⟯) : -P + P = 0 :=
by { cases P, { refl }, { simp only [neg_some, some_add_some_of_y_eq] } }

lemma add_comm (P Q : E⟮K⟯) : P + Q = Q + P :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | ⟨x₁, y₁, h₁⟩, _ | ⟨x₂, y₂, h₂⟩⟩,
  any_goals { refl },
  by_cases hx : x₁ = x₂,
  { by_cases hy : y₁ = neg_y h₂,
    { rw [some_add_some_of_y_eq h₁ h₂ hx hy,
          some_add_some_of_y_eq h₂ h₁ hx.symm $ by { simp only [neg_y, hx, hy], ring1 }] },
    { simp only [hx, y_eq_of_y_ne h₁ h₂ hx hy] } },
  { rw [some_add_some_of_x_ne' h₁ h₂ hx, some_add_some_of_x_ne' h₂ h₁ $ ne.symm hx, neg_inj],
    field_simp [sub_ne_zero_of_ne hx, sub_ne_zero_of_ne (ne.symm hx)],
    exact ⟨by ring1, by ring1⟩ }
end

end add_comm_group

end point

end EllipticCurve
