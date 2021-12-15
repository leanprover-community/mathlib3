import algebra.algebra.basic
import algebraic_geometry.EllipticCurve

-- TODO: move into `algebra.algebra.basic`
instance algebra.has_coe {K L : Type*} [field K] [field L] [algebra K L] : has_coe K L := ⟨ algebra_map K L ⟩

namespace EllipticCurve

-- let `K` be a field, let `E` be an elliptic curve over `K`, and let `L` be a field extension over `K`
variables {K : Type*} [field K] (E : EllipticCurve K) (L : Type*) [field L] [decidable_eq L] [algebra K L]

/-- The group of `L`-rational points `E(L)` on an elliptic curve `E` over `K`,
  which consists of the point at infinity and the affine points satisfying the Weierstrass equation. -/
inductive Point
  | Infinity
  | Affine (x y : L) (w : y ^ 2 + E.a1 * x * y + E.a3 * y = x ^ 3 + E.a2 * x ^ 2 + E.a4 * x + E.a6)
notation E/L := Point E L

open Point

/-- Zero in `E(L)`. -/
def zero : E/L := Infinity
instance has_zero : has_zero (E/L) := ⟨ zero E L ⟩

/-- Negation in `E(L)`. -/
def neg : E/L → E/L
  | 0              := 0
  | (Affine x y w) := Affine x (-y - E.a1 * x - E.a3) $ by rw [← w]; ring
instance has_neg : has_neg (E/L) := ⟨ neg E L ⟩

/-- Addition in `E(L)`. -/
def add : E/L → E/L → E/L
  | P                 0                 := P
  | 0                 Q                 := Q
  | (Affine x₁ y₁ w₁) (Affine x₂ y₂ w₂) :=
    -- add points with different x-coordinates
    if xNe : x₁ - x₂ ≠ 0 then
      let
        l  := (y₁ - y₂) * (x₁ - x₂)⁻¹,
        x₃ := l ^ 2 + E.a1 * l - E.a2 - x₁ - x₂,
        y₃ := -l * x₃ - E.a1 * x₃ - y₁ + l * x₁ - E.a3
      in Affine x₃ y₃ $ begin
        -- rewrite Weierstrass equations as w₁(x, y) = 0 and w₂(x, y) = 0
        rw [← sub_eq_zero] at w₁ w₂,
        -- substitute y
        have ySimp :
            y₃ ^ 2 + E.a1 * x₃ * y₃ + E.a3 * y₃
          = x₃ ^ 2 * (l ^ 2 + E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - E.a1 * x₁ * l + 2 * y₁ * l + E.a3 * l + E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - E.a3 * x₁ * l + y₁ ^ 2 + E.a3 * y₁)
          := by dsimp [y₃]; ring,
        -- substitute x
        have xSimp :
            x₃ ^ 2 * (l ^ 2 + E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - E.a1 * x₁ * l + 2 * y₁ * l + E.a3 * l + E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - E.a3 * x₁ * l + y₁ ^ 2 + E.a3 * y₁)
            - (x₃ ^ 3 + E.a2 * x₃ ^ 2 + E.a4 * x₃ + E.a6)
          = l * (l * (l * (l * (x₁ - x₂) * (-1)
                           + (-E.a1 * x₁ + 2 * E.a1 * x₂ + 2 * y₁ + E.a3))
                      + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + E.a1 ^ 2 * x₂ - 2 * E.a2 * x₂ + 3 * E.a1 * y₁ + E.a1 * E.a3 - E.a4))
                 + (-E.a1 * x₁ ^ 2 - 3 * E.a1 * x₁ * x₂ - 4 * x₁ * y₁ - 2 * E.a1 * x₂ ^ 2 - 2 * x₂ * y₁ - E.a1 * E.a2 * x₁ - 2 * E.a3 * x₁ - 2 * E.a1 * E.a2 * x₂ - E.a3 * x₂ + E.a1 ^ 2 * y₁ - 2 * E.a2 * y₁ - E.a1 * E.a4 - E.a2 * E.a3))
            + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * E.a2 * x₁ ^ 2 + 4 * E.a2 * x₁ * x₂ - E.a1 * x₁ * y₁ + 2 * E.a2 * x₂ ^ 2 - E.a1 * x₂ * y₁ + y₁ ^ 2 + E.a2 ^ 2 * x₁ + E.a4 * x₁ + E.a2 ^ 2 * x₂ + E.a4 * x₂ - E.a1 * E.a2 * y₁ + E.a3 * y₁ + E.a2 * E.a4 - E.a6)
          := by dsimp [x₃]; ring,
        -- substitute l auxiliary tactic
        have lSimp : ∀ {a b c : L}, l * a + b = c ↔ (y₁ - y₂) * a + (x₁ - x₂) * b + 0 = (x₁ - x₂) * c + 0 := begin
          intros a b c,
          rw [← mul_right_inj' xNe],
          rw [mul_add (x₁ - x₂)],
          rw [← mul_assoc (x₁ - x₂) l],
          rw [mul_comm (x₁ - x₂) l],
          rw [inv_mul_cancel_right₀ xNe],
          rw [← add_left_inj (0 : L)]
        end,
        -- substitute l step 1
        have lSimp1 :
            l * (x₁ - x₂) * (-1)
            + (-E.a1 * x₁ + 2 * E.a1 * x₂ + 2 * y₁ + E.a3)
          = -E.a1 * x₁ + 2 * E.a1 * x₂ + 2 * y₁ + E.a3 - y₁ + y₂
          := by rw [inv_mul_cancel_right₀ xNe]; ring,
        -- substitute l step 2
        have lSimp2 :
            l * (-E.a1 * x₁ + 2 * E.a1 * x₂ + 2 * y₁ + E.a3 - y₁ + y₂)
            + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + E.a1 ^ 2 * x₂ - 2 * E.a2 * x₂ + 3 * E.a1 * y₁ + E.a1 * E.a3 - E.a4)
          = 2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + E.a2 * x₁ + E.a1 ^ 2 * x₂ + E.a2 * x₂ - 2 * E.a2 * x₂ + E.a1 * y₁ + E.a1 * y₂ + E.a1 * E.a3
          := by rw [lSimp]; nth_rewrite_rhs 0 [← w₁]; nth_rewrite_lhs 0 [← w₂]; ring,
        -- substitute l step 3
        have lSimp3 :
            l * (2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + E.a2 * x₁ + E.a1 ^ 2 * x₂ + E.a2 * x₂ - 2 * E.a2 * x₂ + E.a1 * y₁ + E.a1 * y₂ + E.a1 * E.a3)
            + (-E.a1 * x₁ ^ 2 - 3 * E.a1 * x₁ * x₂ - 4 * x₁ * y₁ - 2 * E.a1 * x₂ ^ 2 - 2 * x₂ * y₁ - E.a1 * E.a2 * x₁ - 2 * E.a3 * x₁ - 2 * E.a1 * E.a2 * x₂ - E.a3 * x₂ + E.a1 ^ 2 * y₁ - 2 * E.a2 * y₁ - E.a1 * E.a4 - E.a2 * E.a3)
          = -2 * E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - E.a1 * x₂ ^ 2 - x₂ * y₁ - x₂ * y₂ - 2 * E.a3 * x₁ - E.a1 * E.a2 * x₂ - E.a3 * x₂ - E.a2 * y₁ - E.a2 * y₂ - E.a2 * E.a3
          := by apply_fun (λ x, x * E.a1) at w₁ w₂; rw [zero_mul] at w₁ w₂; rw [lSimp]; nth_rewrite_rhs 0 [← w₁]; nth_rewrite_lhs 0 [← w₂]; ring,
        -- substitute l step 4
        have lSimp4 :
            l * (-2 * E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - E.a1 * x₂ ^ 2 - x₂ * y₁ - x₂ * y₂ - 2 * E.a3 * x₁ - E.a1 * E.a2 * x₂ - E.a3 * x₂ - E.a2 * y₁ - E.a2 * y₂ - E.a2 * E.a3)
            + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * E.a2 * x₁ ^ 2 + 4 * E.a2 * x₁ * x₂ - E.a1 * x₁ * y₁ + 2 * E.a2 * x₂ ^ 2 - E.a1 * x₂ * y₁ + y₁ ^ 2 + E.a2 ^ 2 * x₁ + E.a4 * x₁ + E.a2 ^ 2 * x₂ + E.a4 * x₂ - E.a1 * E.a2 * y₁ + E.a3 * y₁ + E.a2 * E.a4 - E.a6)
          = 0
          := by apply_fun (λ x, x * (x₁ + 2 * x₂ + E.a2)) at w₁; apply_fun (λ x, x * (2 * x₁ + x₂ + E.a2)) at w₂; rw [zero_mul] at w₁ w₂; rw [lSimp]; nth_rewrite_lhs 0 [← w₁]; nth_rewrite_rhs 1 [← w₂]; ring,
        -- rewrite Weierstrass equation as w₃(x, y) = 0 and sequence steps
        rw [← sub_eq_zero, ySimp, xSimp, lSimp1, lSimp2, lSimp3, lSimp4]
      end
    -- add points with the same x-coordinate and y-coordinate
    else if yNe : y₁ + (y₂ + E.a1 * x₂ + E.a3) ≠ 0 then
      let
        l  := (3 * x₁ ^ 2 + 2 * E.a2 * x₁ + E.a4 - E.a1 * y₁) * (y₁ + (y₁ + E.a1 * x₁ + E.a3))⁻¹,
        x₃ := l ^ 2 + E.a1 * l - E.a2 - 2 * x₁,
        y₃ := -l * x₃ - E.a1 * x₃ - y₁ + l * x₁ - E.a3
      in Affine x₃ y₃ $ begin
        -- show x-coordinates are the same
        have xEq : x₁ = x₂
          := by simp at xNe; rw [← sub_eq_zero]; exact xNe,
        subst xEq,
        -- show y-coordinates are the same
        have yEq : y₁ = y₂ := begin
          rw [← w₂, ← sub_eq_zero] at w₁,
          have ySimp :
              y₁ ^ 2 + E.a1 * x₁ * y₁ + E.a3 * y₁ - (y₂ ^ 2 + E.a1 * x₁ * y₂ + E.a3 * y₂)
            = (y₁ - y₂) * (y₁ + (y₂ + E.a1 * x₁ + E.a3))
            := by ring,
          rw [ySimp, mul_eq_zero, sub_eq_zero] at w₁,
          cases w₁,
            exact w₁,
            contradiction,
        end,
        subst yEq,
        -- rewrite Weierstrass equation as w₁(x, y) = 0
        rw [← sub_eq_zero] at w₁,
        -- substitute y
        have ySimp :
            y₃ ^ 2 + E.a1 * x₃ * y₃ + E.a3 * y₃
          = x₃ ^ 2 * (l ^ 2 + E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - E.a1 * x₁ * l + 2 * y₁ * l + E.a3 * l + E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - E.a3 * x₁ * l + y₁ ^ 2 + E.a3 * y₁)
          := by dsimp [y₃]; ring,
        -- substitute x
        have xSimp :
            x₃ ^ 2 * (l ^ 2 + E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - E.a1 * x₁ * l + 2 * y₁ * l + E.a3 * l + E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - E.a3 * x₁ * l + y₁ ^ 2 + E.a3 * y₁)
            - (x₃ ^ 3 + E.a2 * x₃ ^ 2 + E.a4 * x₃ + E.a6)
          = l * (l * (l * (y₁ + (y₁ + E.a1 * x₁ + E.a3))
                      + (-3 * x₁ ^ 2 + E.a1 ^ 2 * x₁ - 2 * E.a2 * x₁ + 3 * E.a1 * y₁ + E.a1 * E.a3 - E.a4))
                 + (-6 * E.a1 * x₁ ^ 2 - 6 * x₁ * y₁ - 3 * E.a1 * E.a2 * x₁ - 3 * E.a3 * x₁ + E.a1 ^ 2 * y₁ - 2 * E.a2 * y₁ - E.a1 * E.a4 - E.a2 * E.a3))
            + (8 * x₁ ^ 3 + 8 * E.a2 * x₁ ^ 2 - 2 * E.a1 * x₁ * y₁ + y₁ ^ 2 + 2 * E.a2 ^ 2 * x₁ + 2 * E.a4 * x₁ - E.a1 * E.a2 * y₁ + E.a3 * y₁ + E.a2 * E.a4 - E.a6)
          := by dsimp [x₃]; ring,
        -- substitute l step 1
        have lSimp1 :
            l * (y₁ + (y₁ + E.a1 * x₁ + E.a3))
            + (-3 * x₁ ^ 2 + E.a1 ^ 2 * x₁ - 2 * E.a2 * x₁ + 3 * E.a1 * y₁ + E.a1 * E.a3 - E.a4)
          = (y₁ + (y₁ + E.a1 * x₁ + E.a3)) * E.a1
          := by rw [inv_mul_cancel_right₀ yNe]; ring,
        -- substitute l step 2
        have lSimp2 :
            l * ((y₁ + (y₁ + E.a1 * x₁ + E.a3)) * E.a1)
            + (-6 * E.a1 * x₁ ^ 2 - 6 * x₁ * y₁ - 3 * E.a1 * E.a2 * x₁ - 3 * E.a3 * x₁ + E.a1 ^ 2 * y₁ - 2 * E.a2 * y₁ - E.a1 * E.a4 - E.a2 * E.a3)
          = (y₁ + (y₁ + E.a1 * x₁ + E.a3)) * (-3 * x₁ - E.a2)
          := by rw [← mul_assoc l, inv_mul_cancel_right₀ yNe]; ring,
        -- substitute l step 3
        have lSimp3 :
            l * ((y₁ + (y₁ + E.a1 * x₁ + E.a3)) * (-3 * x₁ - E.a2))
            + (8 * x₁ ^ 3 + 8 * E.a2 * x₁ ^ 2 - 2 * E.a1 * x₁ * y₁ + y₁ ^ 2 + 2 * E.a2 ^ 2 * x₁ + 2 * E.a4 * x₁ - E.a1 * E.a2 * y₁ + E.a3 * y₁ + E.a2 * E.a4 - E.a6)
          = 0
          := by rw [← mul_assoc l, inv_mul_cancel_right₀ yNe, ← w₁]; ring,
        -- rewrite Weierstrass equation as w₃(x, y) = 0 and sequence steps
        rw [← sub_eq_zero, ySimp, xSimp, lSimp1, lSimp2, lSimp3]
      end
    -- add points with different y-coordinates
    else
      0
instance has_add : has_add (E/L) := ⟨ add E L ⟩

/-- Left identity in `E(L)`. -/
@[simp]
lemma zero_add : ∀ P : E/L, 0 + P = P
  | P := by cases P; refl

/-- Right identity in `E(L)`. -/
@[simp]
lemma add_zero : ∀ P : E/L, P + 0 = P
  | P := by cases P; refl

/-- Left negation in `E(L)`. -/
@[simp]
lemma add_left_neg : ∀ P : E/L, -P + P = 0
  | 0              := by refl
  | (Affine x y w) := by dsimp [has_neg.neg]; dsimp [neg]; dsimp [has_add.add]; simp [add]

/-- Associativity in `E(L)`. -/
lemma add_assoc : ∀ P Q R : E/L, (P + Q) + R = P + (Q + R)
  | 0                 Q                 R                 := by simp
  | P                 0                 R                 := by simp
  | P                 Q                 0                 := by simp
  | (Affine x₁ y₁ w₁) (Affine x₂ y₂ w₂) (Affine x₃ y₃ w₃) := sorry

/-- `E(L)` is an additive group. -/
instance add_group : add_group (E/L) :=
  { zero         := zero E L
  , neg          := neg E L
  , add          := add E L
  , zero_add     := zero_add E L
  , add_zero     := add_zero E L
  , add_left_neg := add_left_neg E L
  , add_assoc    := add_assoc E L
  }

-- TODO: `E(L)` is an additive commutative group

end EllipticCurve
