/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.EllipticCurve
import field_theory.galois -- temporary import to enable point notation
import ring_theory.class_group

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
    Bézout's theorem. Explicitly, let $P = (x_1, y_1)$ and $Q = (x_2, y_2)$.
      * If $x_1 = x_2$ and $P = -Q$ then this line is vertical and $P + Q = \mathcal{O}$.
      * If $x_1 = x_2$ and $P \ne -Q$ then this line is the tangent of $E$ at $P = Q$ and has
        gradient $\ell = (3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$.
      * Otherwise $x_1 \ne x_2$ then this line has gradient $\ell = (y_1 - y_2) / (x_1 - x_2)$.
    In the latter two cases, the $x$-coordinate of $P + Q$ is then the unique third solution of the
    equation obtained by substituting the line $y = \ell(x - x_1) + y_1$ into the Weierstrass
    equation, and can be written down explicitly as $x = \ell^2 + a_1\ell - a_2 - x_1 - x_2$ by
    inspecting $x^2$ terms. The $y$-coordinate of $P + Q$, after applying the final negation that
    maps $y$ to $-y - a_1x - a_3$, is precisely $y = -(\ell(x - x_1) + y_1) - x - a_3$.
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

namespace EllipticCurve

open polynomial

open_locale non_zero_divisors polynomial

universes u v

section basic

/-!
### The `K`-rational points `E⟮K⟯`

Use `0` instead of `EllipticCurve.point.zero`.
-/

variables {F : Type u} [comm_ring F] (E : EllipticCurve F) (K : Type v) [comm_ring K] [algebra F K]

section weierstrass

/-- The Weierstrass polynomial $w_E(X, Y) = Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$. -/
noncomputable def weierstrass_polynomial : K[X][X] :=
X ^ 2 + C (C ↑E.a₁ * X) * X + C (C ↑E.a₃) * X - C (X ^ 3 + C ↑E.a₂ * X ^ 2 + C ↑E.a₄ * X + C ↑E.a₆)

lemma weierstrass_polynomial_eq :
  E.weierstrass_polynomial K
    = cubic.to_poly
      ⟨0, 1, cubic.to_poly ⟨0, 0, ↑E.a₁, ↑E.a₃⟩, cubic.to_poly ⟨-1, -↑E.a₂, -↑E.a₄, -↑E.a₆⟩⟩ :=
by { simp only [weierstrass_polynomial, cubic.to_poly, C_0, C_1, C_neg, C_add, C_mul], ring1 }

lemma weierstrass_polynomial_ne_zero [nontrivial K] : E.weierstrass_polynomial K ≠ 0 :=
by { rw [weierstrass_polynomial_eq], exact cubic.ne_zero_of_b_ne_zero one_ne_zero }

lemma weierstrass_polynomial_degree [nontrivial K] : (E.weierstrass_polynomial K).degree = 2 :=
by simpa only [weierstrass_polynomial_eq] using cubic.degree_of_b_ne_zero' one_ne_zero

lemma weierstrass_polynomial_not_is_unit [nontrivial K] [no_zero_divisors K] :
  ¬is_unit (E.weierstrass_polynomial K) :=
begin
  rintro ⟨⟨p, _, h, _⟩, rfl : p = _⟩,
  apply_fun degree at h,
  rw [degree_mul, weierstrass_polynomial_degree, degree_one, nat.with_bot.add_eq_zero_iff] at h,
  exact two_ne_zero (with_bot.coe_eq_zero.mp h.left)
end

lemma weierstrass_polynomial_irreducible [nontrivial K] [no_zero_divisors K] :
  irreducible $ E.weierstrass_polynomial K :=
⟨E.weierstrass_polynomial_not_is_unit K, λ f g h,
begin
  set f1 : K[X] := f.leading_coeff,
  set f0 : K[X] := f.coeff 0,
  set g1 : K[X] := g.leading_coeff,
  set g0 : K[X] := g.coeff 0,
  symmetry' at h,
  have hdegree := congr_arg degree h,
  rw [degree_mul, weierstrass_polynomial_degree, nat.with_bot.add_eq_two_iff] at hdegree,
  rcases hdegree with (⟨hf, hg⟩ | ⟨hf, hg⟩ | ⟨hf, hg⟩),
  { apply_fun C ∘ leading_coeff at h,
    rw [function.comp_apply, leading_coeff_mul, C_mul, eq_C_of_degree_eq_zero hf, leading_coeff_C,
        ← eq_C_of_degree_eq_zero hf, function.comp_apply, weierstrass_polynomial_eq,
        cubic.leading_coeff_of_b_ne_zero' $ one_ne_zero' K[X]] at h,
    exact or.inl ⟨⟨f, C g1, h, by rwa [mul_comm]⟩, rfl⟩ },
  { have to_poly : f * g = cubic.to_poly ⟨0, f1 * g1, f1 * g0 + f0 * g1, f0 * g0⟩ :=
    begin
      conv_lhs { rw [eq_X_add_C_of_degree_eq_one hf, eq_X_add_C_of_degree_eq_one hg] },
      simp only [cubic.to_poly, C_0, C_add, C_mul],
      ring1
    end,
    simp only [weierstrass_polynomial_eq, to_poly, cubic.to_poly_injective] at h,
    rcases h with ⟨_, h11, h10, h00⟩,
    apply_fun degree at h11 h10 h00,
    rw [degree_mul, degree_one, nat.with_bot.add_eq_zero_iff] at h11,
    replace h10 := le_of_eq_of_le h10 cubic.degree_of_b_eq_zero',
    contrapose h10,
    rw [degree_mul, cubic.degree_of_a_ne_zero' $ neg_ne_zero.mpr $ one_ne_zero' K] at h00,
    rcases nat.with_bot.add_eq_three_iff.mp h00 with (h00 | h00 | h00 | h00),
    any_goals
      { rw [degree_add_eq_left_of_degree_lt]; simp only [degree_mul, h11, h00]; dec_trivial },
    any_goals
      { rw [degree_add_eq_right_of_degree_lt]; simp only [degree_mul, h11, h00]; dec_trivial } },
  { apply_fun C ∘ leading_coeff at h,
    rw [function.comp_apply, leading_coeff_mul, C_mul, eq_C_of_degree_eq_zero hg, leading_coeff_C,
        ← eq_C_of_degree_eq_zero hg, function.comp_apply, weierstrass_polynomial_eq,
        cubic.leading_coeff_of_b_ne_zero' $ one_ne_zero' K[X]] at h,
    exact or.inr ⟨⟨g, C f1, by rwa [mul_comm], h⟩, rfl⟩ }
end⟩

/-- The Weierstrass ring $R_E = K[X, Y] / \langle w_E(X, Y) \rangle$. -/
@[reducible] def weierstrass_ring : Type v := adjoin_root $ E.weierstrass_polynomial K

variables {K}

/-- The proposition that an affine point $(x, y)$ lies in `E`, that is $w_E(x, y) = 0$. -/
def weierstrass_equation (x y : K) : Prop := eval x (eval (C y) $ E.weierstrass_polynomial K) = 0

@[simp] lemma eval_weierstrass_polynomial (x y : K) :
  eval x (eval (C y) $ E.weierstrass_polynomial K)
    = y ^ 2 + ↑E.a₁ * x * y + ↑E.a₃ * y - (x ^ 3 + ↑E.a₂ * x ^ 2 + ↑E.a₄ * x + ↑E.a₆) :=
by simp only [weierstrass_polynomial, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]

lemma weierstrass_equation_iff' (x y : K) :
  E.weierstrass_equation x y
    ↔ y ^ 2 + ↑E.a₁ * x * y + ↑E.a₃ * y - (x ^ 3 + ↑E.a₂ * x ^ 2 + ↑E.a₄ * x + ↑E.a₆) = 0 :=
by rw [weierstrass_equation, eval_weierstrass_polynomial]

@[simp] lemma weierstrass_equation_iff (x y : K) :
  E.weierstrass_equation x y
    ↔ y ^ 2 + ↑E.a₁ * x * y + ↑E.a₃ * y = x ^ 3 + ↑E.a₂ * x ^ 2 + ↑E.a₄ * x + ↑E.a₆ :=
by rw [weierstrass_equation_iff', sub_eq_zero]

end weierstrass

variables (K)

/-- The group of `K`-rational points `E⟮K⟯` on an elliptic curve `E` over `F`. This consists of the
unique point at infinity `EllipticCurve.point.zero`and the affine points `EllipticCurve.point.some`
satisfying the Weierstrass equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ of `E`. -/
inductive point
| zero
| some (x y : K) (h : E.weierstrass_equation x y)

localized "notation E⟮K⟯ := point E K" in EllipticCurve

variables {E K}

namespace point

instance : inhabited E⟮K⟯ := ⟨zero⟩

section zero

instance : has_zero E⟮K⟯ := ⟨zero⟩

@[simp] lemma zero_def : zero = (0 : E⟮K⟯) := rfl

end zero

section negation

variables {x y : K} (h : E.weierstrass_equation x y)

include h

/-- The $y$-coordinate of the negation of an affine point. -/
@[nolint unused_arguments] def neg_y : K := -y - ↑E.a₁ * x - ↑E.a₃

@[simp] lemma neg_y_def : neg_y h = -y - ↑E.a₁ * x - ↑E.a₃ := rfl

/-- The negation of an affine point in `E` lies in `E`. -/
lemma weierstrass_equation_neg : E.weierstrass_equation x $ neg_y h :=
by { rw [weierstrass_equation_iff] at h, rw [weierstrass_equation_iff, neg_y_def, ← h], ring1 }

omit h

/-- Negation in `E⟮K⟯`. Given `P : E⟮K⟯`, use `-P` instead of `neg P`. -/
def neg : E⟮K⟯ → E⟮K⟯
| 0            := 0
| (some x y h) := some x (neg_y h) $ weierstrass_equation_neg h

instance : has_neg E⟮K⟯ := ⟨neg⟩

@[simp] lemma neg_def (P : E⟮K⟯) : neg P = -P := rfl

@[simp] lemma neg_zero : -0 = (0 : E⟮K⟯) := rfl

@[simp] lemma neg_some : -some x y h = some x (neg_y h) (weierstrass_equation_neg h) := rfl

@[simp] lemma neg_neg (P : E⟮K⟯) : -(-P) = P := by { cases P, { refl }, { simp, ring1 } }

instance : has_involutive_neg E⟮K⟯ := ⟨neg, neg_neg⟩

end negation

end point

end basic

open_locale EllipticCurve

variables {F : Type u} [field F] {E : EllipticCurve F} {K : Type v} [field K] [algebra F K]

section dbl_add

/-!
### The addition law of `E⟮K⟯`

Given `P Q : E⟮K⟯`, use `P + Q` instead of `add P Q`.
-/

namespace point

section doubling

variables {x y : K} (h : E.weierstrass_equation x y)

include h

/-- The gradient of the tangent line of `E` at an affine point $(x, y)$. This is not well-defined
only in the case of $y = -y - a_1x - a_3$, which is precisely when the tangent is vertical. -/
def dbl_L : K := (3 * x ^ 2 + 2 * ↑E.a₂ * x + ↑E.a₄ - ↑E.a₁ * y) / (y - neg_y h)

@[simp] lemma dbl_L_def :
  dbl_L h = (3 * x ^ 2 + 2 * ↑E.a₂ * x + ↑E.a₄ - ↑E.a₁ * y) / (y - neg_y h) :=
rfl

/-- The $x$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
def dbl_x : K := dbl_L h ^ 2 + ↑E.a₁ * dbl_L h - ↑E.a₂ - 2 * x

@[simp] lemma dbl_x_def : dbl_x h = dbl_L h ^ 2 + ↑E.a₁ * dbl_L h - ↑E.a₂ - 2 * x := rfl

/-- The $y$-coordinate of the doubling of an affine point whose tangent is not vertical,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$. -/
def dbl_y' : K := dbl_L h * (dbl_x h - x) + y

@[simp] lemma dbl_y'_def : dbl_y' h = dbl_L h * (dbl_x h - x) + y := rfl

/-- The $y$-coordinate of the doubling of an affine point whose tangent is not vertical. -/
def dbl_y : K := -dbl_y' h - ↑E.a₁ * dbl_x h - ↑E.a₃

@[simp] lemma dbl_y_def : dbl_y h = -dbl_y' h - ↑E.a₁ * dbl_x h - ↑E.a₃ := rfl

/-- The doubling of an affine point in `E` whose tangent is not vertical,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$, lies in `E`. -/
lemma weierstrass_equation_dbl' (hy : y ≠ neg_y h) : E.weierstrass_equation (dbl_x h) (dbl_y' h) :=
begin
  rw [weierstrass_equation_iff'],
  convert_to
    dbl_L h * (dbl_L h * (dbl_L h * (y - neg_y h)
                          + (-3 * x ^ 2 + ↑E.a₁ ^ 2 * x - 2 * ↑E.a₂ * x + 3 * ↑E.a₁ * y
                              + ↑E.a₁ * ↑E.a₃ - ↑E.a₄))
                + (-6 * ↑E.a₁ * x ^ 2 - 6 * x * y - 3 * ↑E.a₁ * ↑E.a₂ * x - 3 * ↑E.a₃ * x
                    + ↑E.a₁ ^ 2 * y - 2 * ↑E.a₂ * y - ↑E.a₁ * ↑E.a₄ - ↑E.a₂ * ↑E.a₃))
    + (8 * x ^ 3 + 8 * ↑E.a₂ * x ^ 2 - 2 * ↑E.a₁ * x * y + y ^ 2 + 2 * ↑E.a₂ ^ 2 * x + 2 * ↑E.a₄ * x
        - ↑E.a₁ * ↑E.a₂ * y + ↑E.a₃ * y + ↑E.a₂ * ↑E.a₄ - ↑E.a₆) = 0,
  { simp only [dbl_x_def, dbl_y'_def, neg_y_def], ring1 },
  field_simp [-neg_y_def, sub_ne_zero_of_ne hy],
  rw [weierstrass_equation_iff'] at h,
  linear_combination (2 * y + ↑E.a₁ * x + ↑E.a₃) ^ 2 * h
    with { normalization_tactic := `[rw [neg_y_def], ring1] }
end

/-- The doubling of an affine point in `E` whose tangent is not vertical lies in `E`. -/
lemma weierstrass_equation_dbl (hy : y ≠ neg_y h) : E.weierstrass_equation (dbl_x h) (dbl_y h) :=
weierstrass_equation_neg $ weierstrass_equation_dbl' h hy

end doubling

section addition

variables {x₁ x₂ y₁ y₂ : K} (h₁ : E.weierstrass_equation x₁ y₁) (h₂ : E.weierstrass_equation x₂ y₂)

include h₁ h₂

/-- The gradient of the line joining two affine points $(x_1, y_1)$ and $(x_2, y_2)$. This is not
well-defined only in the case of $x_1 = x_2$, where the line becomes a tangent of `E`. -/
@[nolint unused_arguments] def add_L : K := (y₁ - y₂) / (x₁ - x₂)

@[simp] lemma add_L_def : add_L h₁ h₂ = (y₁ - y₂) / (x₁ - x₂) := rfl

/-- The $x$-coordinate of the addition of two affine points with distinct $x$-coordinates. -/
def add_x : K := add_L h₁ h₂ ^ 2 + ↑E.a₁ * add_L h₁ h₂ - ↑E.a₂ - x₁ - x₂

@[simp] lemma add_x_def : add_x h₁ h₂ = add_L h₁ h₂ ^ 2 + ↑E.a₁ * add_L h₁ h₂ - ↑E.a₂ - x₁ - x₂ :=
rfl

/-- The $y$-coordinate of the addition of two affine points with distinct $x$-coordinates,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$. -/
def add_y' : K := add_L h₁ h₂ * (add_x h₁ h₂ - x₁) + y₁

@[simp] lemma add_y'_def : add_y' h₁ h₂ = add_L h₁ h₂ * (add_x h₁ h₂ - x₁) + y₁ := rfl

/-- The $y$-coordinate of the addition of two affine points with distinct $x$-coordinates. -/
def add_y : K := -add_y' h₁ h₂ - ↑E.a₁ * add_x h₁ h₂ - ↑E.a₃

@[simp] lemma add_y_def : add_y h₁ h₂ = -add_y' h₁ h₂ - ↑E.a₁ * add_x h₁ h₂ - ↑E.a₃ := rfl

/-- The addition of two affine points in `E` with distinct $x$-coordinates,
before applying the final negation that maps $y$ to $-y - a_1x - a_3$, lies in `E`. -/
lemma weierstrass_equation_add' (hx : x₁ ≠ x₂) :
  E.weierstrass_equation (add_x h₁ h₂) (add_y' h₁ h₂) :=
begin
  rw [weierstrass_equation_iff'],
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
  { simp only [add_x_def, add_y'_def], ring1 },
  field_simp [sub_ne_zero_of_ne hx],
  rw [weierstrass_equation_iff'] at h₁ h₂,
  linear_combination
    -((x₁ - x₂) ^ 2 * (x₁ + 2 * x₂ + ↑E.a₂) - (x₁ - x₂) * (y₁ - y₂) * ↑E.a₁ - (y₁ - y₂) ^ 2) * h₁
    + ((x₁ - x₂) ^ 2 * (2 * x₁ + x₂ + ↑E.a₂) - (x₁ - x₂) * (y₁ - y₂) * ↑E.a₁ - (y₁ - y₂) ^ 2) * h₂
    with { normalization_tactic := `[ring1] }
end

/-- The addition of two affine points in `E` with distinct $x$-coordinates lies in `E`. -/
lemma weierstrass_equation_add (hx : x₁ ≠ x₂) :
  E.weierstrass_equation (add_x h₁ h₂) (add_y h₁ h₂) :=
weierstrass_equation_neg $ weierstrass_equation_add' h₁ h₂ hx

lemma y_eq_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) : y₁ = y₂ :=
begin
  rw [neg_y] at hy,
  rw [weierstrass_equation_iff] at h₂,
  rw [weierstrass_equation_iff', hx, ← h₂] at h₁,
  apply eq_of_sub_eq_zero ∘ eq_zero_of_ne_zero_of_mul_right_eq_zero (sub_ne_zero.mpr hy),
  convert h₁,
  ring1
end

lemma y_ne_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) : y₁ ≠ neg_y h₁ :=
by { convert hy, exact y_eq_of_y_ne h₁ h₂ hx hy }

omit h₁ h₂

open_locale classical

/-- Addition in `E⟮K⟯`. Given `P Q : E⟮K⟯`, use `P + Q` instead of `add P Q`. -/
noncomputable def add : E⟮K⟯ → E⟮K⟯ → E⟮K⟯
| 0               P               := P
| P               0               := P
| (some x₁ y₁ h₁) (some x₂ y₂ h₂) :=
if hx : x₁ = x₂ then if hy : y₁ = neg_y h₂ then 0
else some _ _ $ weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy
else some _ _ $ weierstrass_equation_add h₁ h₂ hx

noncomputable instance : has_add E⟮K⟯ := ⟨add⟩

@[simp] lemma add_def (P Q : E⟮K⟯) : add P Q = P + Q := rfl

@[simp] lemma zero_add (P : E⟮K⟯) : 0 + P = P := by cases P; refl

@[simp] lemma add_zero (P : E⟮K⟯) : P + 0 = P := by cases P; refl

noncomputable instance : add_zero_class E⟮K⟯ := ⟨0, (+), zero_add, add_zero⟩

lemma some_add_some :
  some x₁ y₁ h₁ + some x₂ y₂ h₂
    = if hx : x₁ = x₂ then if hy : y₁ = neg_y h₂ then 0
      else some _ _ $ weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy
      else some _ _ $ weierstrass_equation_add h₁ h₂ hx :=
rfl

@[simp] lemma some_add_some_of_y_eq (hx : x₁ = x₂) (hy : y₁ = neg_y h₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = 0 :=
by rw [some_add_some, dif_pos hx, dif_pos hy]

@[simp] lemma some_add_self_of_y_eq (hy : y₁ = neg_y h₁) : some x₁ y₁ h₁ + some x₁ y₁ h₁ = 0 :=
some_add_some_of_y_eq h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂
    = some _ _ (weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
by rw [some_add_some, dif_pos hx, dif_neg hy]

lemma some_add_some_of_y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂
    = -some _ _ (weierstrass_equation_dbl' h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
some_add_some_of_y_ne h₁ h₂ hx hy

@[simp] lemma some_add_self_of_y_ne (hy : y₁ ≠ neg_y h₁) :
  some x₁ y₁ h₁ + some x₁ y₁ h₁
    = some _ _ (weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

lemma some_add_self_of_y_ne' (hy : y₁ ≠ neg_y h₁) :
  some x₁ y₁ h₁ + some x₁ y₁ h₁
    = -some _ _ (weierstrass_equation_dbl' h₁ $ y_ne_of_y_ne h₁ h₁ rfl hy) :=
some_add_some_of_y_ne h₁ h₁ rfl hy

@[simp] lemma some_add_some_of_x_ne (hx : x₁ ≠ x₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = some _ _ (weierstrass_equation_add h₁ h₂ hx) :=
by rw [some_add_some, dif_neg hx]

lemma some_add_some_of_x_ne' (hx : x₁ ≠ x₂) :
  some x₁ y₁ h₁ + some x₂ y₂ h₂ = -some _ _ (weierstrass_equation_add' h₁ h₂ hx) :=
some_add_some_of_x_ne h₁ h₂ hx

end addition

end point

end dbl_add

section group_law

/-!
### The group law on `E⟮K⟯`

This follows by constructing an injective `add_monoid_hom` from `E⟮K⟯` to the class group of $R_E$.
-/

instance : is_domain $ E.weierstrass_ring K := (ideal.quotient.is_domain_iff_prime _).mpr
begin
  classical,
  simpa only [ideal.span_singleton_prime (E.weierstrass_polynomial_ne_zero K),
              ← gcd_monoid.irreducible_iff_prime] using E.weierstrass_polynomial_irreducible K
end

variables (E) {K}

/-- TODO: docstring -/
def some_ideal_set (x y : K) : set $ E.weierstrass_ring K :=
{ideal.quotient.mk _ $ C (X - C x), ideal.quotient.mk _ $ X - C (C y)}

/-- TODO: docstring -/
noncomputable def some_ideal (x y : K) :
  fractional_ideal (E.weierstrass_ring K)⁰ $ fraction_ring $ E.weierstrass_ring K :=
ideal.span $ E.some_ideal_set x y

/-- TODO: docstring -/
def some_ideal_x_set (x : K) : set $ E.weierstrass_ring K := {ideal.quotient.mk _ $ C (X - C x)}

/-- TODO: docstring -/
noncomputable def some_ideal_x (x : K) :
  fractional_ideal (E.weierstrass_ring K)⁰ $ fraction_ring $ E.weierstrass_ring K :=
ideal.span $ E.some_ideal_x_set x

/-- TODO: might be false -/
@[simp] lemma some_ideal_mul_neg {x y : K} (h : E.weierstrass_equation x y) :
  E.some_ideal x y * (E.some_ideal x (point.neg_y h) / E.some_ideal_x x) = 1 :=
sorry

@[simp] lemma some_ideal_neg_mul {x y : K} (h : E.weierstrass_equation x y) :
  (E.some_ideal x (point.neg_y h) / E.some_ideal_x x) * E.some_ideal x y = 1 :=
by rw [mul_comm, E.some_ideal_mul_neg h]

/-- TODO: docstring -/
noncomputable def some_ideal_units {x y : K} (h : E.weierstrass_equation x y) :
  (fractional_ideal (E.weierstrass_ring K)⁰ $ fraction_ring $ E.weierstrass_ring K)ˣ :=
⟨_, _, E.some_ideal_mul_neg h, E.some_ideal_neg_mul h⟩

variables {E}

namespace point

@[simp] lemma add_eq_zero (P Q : E⟮K⟯) : P + Q = 0 ↔ P = -Q :=
begin
  rcases ⟨P, Q⟩ with ⟨_ | ⟨x₁, y₁, h₁⟩, _ | ⟨x₂, y₂, h₂⟩⟩,
  { refl },
  { rw [zero_def, zero_add, eq_neg_iff_eq_neg, neg_zero] },
  { refl },
  { simp only [neg_some],
    split,
    { intro h,
      by_cases hx : x₁ = x₂,
      { by_cases hy : y₁ = neg_y h₂,
        { exact ⟨hx, hy⟩ },
        { rw [some_add_some_of_y_ne h₁ h₂ hx hy] at h,
          contradiction } },
      { rw [some_add_some_of_x_ne h₁ h₂ hx] at h,
        contradiction } },
    { exact λ ⟨hx, hy⟩, some_add_some_of_y_eq h₁ h₂ hx hy } }
end

@[simp] lemma add_neg_eq_zero (P Q : E⟮K⟯) : P + -Q = 0 ↔ P = Q := by rw [add_eq_zero, neg_neg]

@[simp] lemma add_left_neg (P : E⟮K⟯) : -P + P = 0 := by rw [add_eq_zero]

@[simp] noncomputable def to_class_fun : E⟮K⟯ → additive (class_group $ E.weierstrass_ring K)
| 0            := 0
| (some _ _ h) := class_group.mk $ E.some_ideal_units h

variables {x₁ x₂ y₁ y₂ : K} (h₁ : E.weierstrass_equation x₁ y₁) (h₂ : E.weierstrass_equation x₂ y₂)

@[simp] lemma inv_some_class :
  class_group.mk (E.some_ideal_units h₁)⁻¹
    = class_group.mk (E.some_ideal_units $ weierstrass_equation_neg h₁) :=
sorry

@[simp] lemma some_class_mul_some_class_of_y_eq (hx : x₁ = x₂) (hy : y₁ = neg_y h₂) :
  class_group.mk (E.some_ideal_units h₁) * class_group.mk (E.some_ideal_units h₂) = 1 :=
sorry

@[simp] lemma some_class_mul_some_class_of_y_ne (hx : x₁ = x₂) (hy : y₁ ≠ neg_y h₂) :
  class_group.mk (E.some_ideal_units h₁) * class_group.mk (E.some_ideal_units h₂)
    = class_group.mk
      (E.some_ideal_units $ weierstrass_equation_dbl h₁ $ y_ne_of_y_ne h₁ h₂ hx hy) :=
sorry

@[simp] lemma some_class_mul_some_class_of_x_ne (hx : x₁ ≠ x₂) :
  class_group.mk (E.some_ideal_units h₁) * class_group.mk (E.some_ideal_units h₂)
    = class_group.mk (E.some_ideal_units $ weierstrass_equation_add h₁ h₂ hx) :=
sorry

noncomputable def to_class : E⟮K⟯ →+ additive (class_group $ E.weierstrass_ring K) :=
{ to_fun    := to_class_fun,
  map_zero' := rfl,
  map_add'  :=
  begin
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩),
    any_goals { simp only [zero_def, to_class_fun, _root_.zero_add, _root_.add_zero] },
    by_cases hx : x₁ = x₂,
    { by_cases hy : y₁ = neg_y h₂,
      { simpa only [some_add_some_of_y_eq h₁ h₂ hx hy]
          using (some_class_mul_some_class_of_y_eq h₁ h₂ hx hy).symm },
      { simpa only [some_add_some_of_y_ne h₁ h₂ hx hy]
          using (some_class_mul_some_class_of_y_ne h₁ h₂ hx hy).symm } },
    { simpa only [some_add_some_of_x_ne h₁ h₂ hx]
        using (some_class_mul_some_class_of_x_ne h₁ h₂ hx).symm }
  end }

@[simp] lemma to_class_zero : to_class (0 : E⟮K⟯) = 0 := rfl

@[simp] lemma to_class_some {x y : K} (h : E.weierstrass_equation x y) :
  to_class (some _ _ h) = class_group.mk (E.some_ideal_units h) :=
rfl

@[simp] lemma to_class.map_neg (P : E⟮K⟯) : to_class (-P) = -to_class P :=
begin
  rcases P with (_ | ⟨_, _, h⟩),
  { refl },
  { simpa only [neg_some, to_class_some] using (inv_some_class h).symm }
end

@[simp] lemma to_class_eq_zero (P : E⟮K⟯) : to_class P = 0 ↔ P = 0 :=
⟨begin
  intro hP,
  rcases P with (_ | ⟨x, y, h⟩),
  { refl },
  { sorry }
end, congr_arg to_class⟩

lemma to_class_injective : function.injective $ @to_class _ _ E K _ _ :=
λ _ _ h, by rw [← add_neg_eq_zero, ← to_class_eq_zero, map_add, h, to_class.map_neg, add_right_neg]

lemma add_comm (P Q : E⟮K⟯) : P + Q = Q + P := to_class_injective $ by simp only [map_add, add_comm]

lemma add_assoc (P Q R : E⟮K⟯) : P + Q + R = P + (Q + R) :=
  to_class_injective $ by simp only [map_add, add_assoc]

noncomputable instance : add_comm_group E⟮K⟯ :=
{ zero         := zero,
  neg          := neg,
  add          := add,
  zero_add     := zero_add,
  add_zero     := add_zero,
  add_left_neg := add_left_neg,
  add_comm     := add_comm,
  add_assoc    := add_assoc }

end point

end group_law

end EllipticCurve
