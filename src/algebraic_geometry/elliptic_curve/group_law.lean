import algebra.algebra.basic
import algebraic_geometry.elliptic_curve.EllipticCurve

local attribute [semireducible] with_zero

namespace EllipticCurve

variables {K : Type*} [field K]
variables (E : EllipticCurve K)
variables (L : Type*) [decidable_eq L] [field L] [algebra K L]

notation K↑L := algebra_map K L

/-- The group of `L`-rational points `E(L)` on an elliptic curve `E` over `K`,
    consisting of the point at infinity and the affine points satisfying a Weierstrass equation. -/
def point := with_zero {P : L × L // P.2 ^ 2 + (K↑L)E.a1 * P.1 * P.2 + (K↑L)E.a3 * P.2
                                   = P.1 ^ 3 + (K↑L)E.a2 * P.1 ^ 2 + (K↑L)E.a4 * P.1 + (K↑L)E.a6}

notation E/L := point E L

/-- Zero in `E(L)`. -/
instance has_zero : has_zero (E/L) := with_zero.has_zero

def neg : E/L → E/L
  | 0        := 0
  | (some P) := let ⟨⟨x, y⟩, w⟩ := P in
    some ⟨⟨x, -y - (K↑L)E.a1 * x - (K↑L)E.a3⟩, by rw [← w]; ring_nf⟩

/-- Negation in `E(L)`. -/
instance has_neg : has_neg (E/L) := ⟨neg E L⟩

def add : E/L → E/L → E/L
  | P         0       := P
  | 0         Q       := Q
  | (some P) (some Q) := let (⟨⟨x₁, y₁⟩, w₁⟩, ⟨⟨x₂, y₂⟩, w₂⟩) := (P, Q) in
    -- add points with different x-coordinates
    if xNe : x₁ - x₂ ≠ 0 then
      let
        l  := (y₁ - y₂) * (x₁ - x₂)⁻¹,
        x₃ := l ^ 2 + (K↑L)E.a1 * l - (K↑L)E.a2 - x₁ - x₂,
        y₃ := -l * x₃ - (K↑L)E.a1 * x₃ - y₁ + l * x₁ - (K↑L)E.a3
      in some ⟨⟨x₃, y₃⟩, begin
        -- rewrite Weierstrass equations as w₁(x, y) = 0 and w₂(x, y) = 0
        rw [← sub_eq_zero] at w₁ w₂,
        -- substitute y
        have ySimp :
            y₃ ^ 2 + (K↑L)E.a1 * x₃ * y₃ + (K↑L)E.a3 * y₃
          = x₃ ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - (K↑L)E.a1 * x₁ * l + 2 * y₁ * l + (K↑L)E.a3 * l
                    + (K↑L)E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (K↑L)E.a3 * x₁ * l + y₁ ^ 2 + (K↑L)E.a3 * y₁)
          := by dsimp [y₃]; ring,
        -- substitute x
        have xSimp :
            x₃ ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - (K↑L)E.a1 * x₁ * l + 2 * y₁ * l + (K↑L)E.a3 * l
                    + (K↑L)E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (K↑L)E.a3 * x₁ * l + y₁ ^ 2 + (K↑L)E.a3 * y₁)
            - (x₃ ^ 3 + (K↑L)E.a2 * x₃ ^ 2 + (K↑L)E.a4 * x₃ + (K↑L)E.a6)
          = l * (l * (l * (l * (x₁ - x₂) * (-1)
                           + (-(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3))
                      + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (K↑L)E.a1 ^ 2 * x₂ - 2 * (K↑L)E.a2 * x₂
                         + 3 * (K↑L)E.a1 * y₁ + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4))
                 + (-(K↑L)E.a1 * x₁ ^ 2 - 3 * (K↑L)E.a1 * x₁ * x₂ - 4 * x₁ * y₁
                    - 2 * (K↑L)E.a1 * x₂ ^ 2 - 2 * x₂ * y₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₁
                    - 2 * (K↑L)E.a3 * x₁ - 2 * (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂
                    + (K↑L)E.a1 ^ 2 * y₁ - 2 * (K↑L)E.a2 * y₁ - (K↑L)E.a1 * (K↑L)E.a4
                    - (K↑L)E.a2 * (K↑L)E.a3))
            + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (K↑L)E.a2 * x₁ ^ 2
               + 4 * (K↑L)E.a2 * x₁ * x₂ - (K↑L)E.a1 * x₁ * y₁ + 2 * (K↑L)E.a2 * x₂ ^ 2
               - (K↑L)E.a1 * x₂ * y₁ + y₁ ^ 2 + (K↑L)E.a2 ^ 2 * x₁ + (K↑L)E.a4 * x₁
               + (K↑L)E.a2 ^ 2 * x₂ + (K↑L)E.a4 * x₂ - (K↑L)E.a1 * (K↑L)E.a2 * y₁ + (K↑L)E.a3 * y₁
               + (K↑L)E.a2 * (K↑L)E.a4 - (K↑L)E.a6)
          := by dsimp [x₃]; ring,
        -- substitute l auxiliary tactic
        have lSimp : ∀ {a b c : L},
          l * a + b = c ↔ (y₁ - y₂) * a + (x₁ - x₂) * b + 0 = (x₁ - x₂) * c + 0
          := begin
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
            + (-(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3)
          = -(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3 - y₁ + y₂
          := by rw [inv_mul_cancel_right₀ xNe]; ring,
        -- substitute l step 2
        have lSimp2 :
            l * (-(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3 - y₁ + y₂)
            + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (K↑L)E.a1 ^ 2 * x₂ - 2 * (K↑L)E.a2 * x₂
               + 3 * (K↑L)E.a1 * y₁ + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4)
          = 2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (K↑L)E.a2 * x₁ + (K↑L)E.a1 ^ 2 * x₂ + (K↑L)E.a2 * x₂
            - 2 * (K↑L)E.a2 * x₂ + (K↑L)E.a1 * y₁ + (K↑L)E.a1 * y₂ + (K↑L)E.a1 * (K↑L)E.a3
          := by rw [lSimp]; nth_rewrite_rhs 0 [← w₁]; nth_rewrite_lhs 0 [← w₂]; ring,
        -- substitute l step 3
        have lSimp3 :
            l * (2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (K↑L)E.a2 * x₁ + (K↑L)E.a1 ^ 2 * x₂
                 + (K↑L)E.a2 * x₂ - 2 * (K↑L)E.a2 * x₂ + (K↑L)E.a1 * y₁ + (K↑L)E.a1 * y₂
                 + (K↑L)E.a1 * (K↑L)E.a3)
            + (-(K↑L)E.a1 * x₁ ^ 2 - 3 * (K↑L)E.a1 * x₁ * x₂ - 4 * x₁ * y₁ - 2 * (K↑L)E.a1 * x₂ ^ 2
               - 2 * x₂ * y₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₁ - 2 * (K↑L)E.a3 * x₁
               - 2 * (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂ + (K↑L)E.a1 ^ 2 * y₁
               - 2 * (K↑L)E.a2 * y₁ - (K↑L)E.a1 * (K↑L)E.a4 - (K↑L)E.a2 * (K↑L)E.a3)
          = -2 * (K↑L)E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (K↑L)E.a1 * x₂ ^ 2 - x₂ * y₁
            - x₂ * y₂ - 2 * (K↑L)E.a3 * x₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂
            - (K↑L)E.a2 * y₁ - (K↑L)E.a2 * y₂ - (K↑L)E.a2 * (K↑L)E.a3
          := by apply_fun (λ x, x * (K↑L)E.a1) at w₁ w₂; rw [zero_mul] at w₁ w₂; rw [lSimp];
                nth_rewrite_rhs 0 [← w₁]; nth_rewrite_lhs 0 [← w₂]; ring,
        -- substitute l step 4
        have lSimp4 :
            l * (-2 * (K↑L)E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (K↑L)E.a1 * x₂ ^ 2 - x₂ * y₁
                 - x₂ * y₂ - 2 * (K↑L)E.a3 * x₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂
                 - (K↑L)E.a2 * y₁ - (K↑L)E.a2 * y₂ - (K↑L)E.a2 * (K↑L)E.a3)
            + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (K↑L)E.a2 * x₁ ^ 2
               + 4 * (K↑L)E.a2 * x₁ * x₂ - (K↑L)E.a1 * x₁ * y₁ + 2 * (K↑L)E.a2 * x₂ ^ 2
               - (K↑L)E.a1 * x₂ * y₁ + y₁ ^ 2 + (K↑L)E.a2 ^ 2 * x₁ + (K↑L)E.a4 * x₁
               + (K↑L)E.a2 ^ 2 * x₂ + (K↑L)E.a4 * x₂ - (K↑L)E.a1 * (K↑L)E.a2 * y₁ + (K↑L)E.a3 * y₁
               + (K↑L)E.a2 * (K↑L)E.a4 - (K↑L)E.a6)
          = 0
          := by apply_fun (λ x, x * (x₁ + 2 * x₂ + (K↑L)E.a2)) at w₁;
                apply_fun (λ x, x * (2 * x₁ + x₂ + (K↑L)E.a2)) at w₂;
                rw [zero_mul] at w₁ w₂; rw [lSimp];
                nth_rewrite_lhs 0 [← w₁]; nth_rewrite_rhs 1 [← w₂]; ring,
        -- rewrite Weierstrass equation as w₃(x, y) = 0 and sequence steps
        rw [← sub_eq_zero, ySimp, xSimp, lSimp1, lSimp2, lSimp3, lSimp4]
      end⟩
    -- add points with the same x-coordinate and y-coordinate
    else if yNe : y₁ + (y₂ + (K↑L)E.a1 * x₂ + (K↑L)E.a3) ≠ 0 then
      let
        l  := (3 * x₁ ^ 2 + 2 * (K↑L)E.a2 * x₁ + (K↑L)E.a4 - (K↑L)E.a1 * y₁)
              * (y₁ + (y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3))⁻¹,
        x₃ := l ^ 2 + (K↑L)E.a1 * l - (K↑L)E.a2 - 2 * x₁,
        y₃ := -l * x₃ - (K↑L)E.a1 * x₃ - y₁ + l * x₁ - (K↑L)E.a3
      in some ⟨⟨x₃, y₃⟩, begin
        -- show x-coordinates are the same
        have xEq : x₁ = x₂
          := by simp at xNe; rw [← sub_eq_zero]; exact xNe,
        subst xEq,
        -- show y-coordinates are the same
        have yEq : y₁ = y₂
          := begin
            rw [← w₂, ← sub_eq_zero] at w₁,
            have ySimp :
                y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁
                - (y₂ ^ 2 + (K↑L)E.a1 * x₁ * y₂ + (K↑L)E.a3 * y₂)
              = (y₁ - y₂) * (y₁ + (y₂ + (K↑L)E.a1 * x₁ + (K↑L)E.a3))
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
            y₃ ^ 2 + (K↑L)E.a1 * x₃ * y₃ + (K↑L)E.a3 * y₃
          = x₃ ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - (K↑L)E.a1 * x₁ * l + 2 * y₁ * l + (K↑L)E.a3 * l
                    + (K↑L)E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (K↑L)E.a3 * x₁ * l + y₁ ^ 2 + (K↑L)E.a3 * y₁)
          := by dsimp [y₃]; ring,
        -- substitute x
        have xSimp :
            x₃ ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
            + x₃ * (-2 * x₁ * l ^ 2 - (K↑L)E.a1 * x₁ * l + 2 * y₁ * l + (K↑L)E.a3 * l
                    + (K↑L)E.a1 * y₁)
            + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (K↑L)E.a3 * x₁ * l + y₁ ^ 2 + (K↑L)E.a3 * y₁)
            - (x₃ ^ 3 + (K↑L)E.a2 * x₃ ^ 2 + (K↑L)E.a4 * x₃ + (K↑L)E.a6)
          = l * (l * (l * (y₁ + (y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3))
                      + (-3 * x₁ ^ 2 + (K↑L)E.a1 ^ 2 * x₁ - 2 * (K↑L)E.a2 * x₁ + 3 * (K↑L)E.a1 * y₁
                         + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4))
                 + (-6 * (K↑L)E.a1 * x₁ ^ 2 - 6 * x₁ * y₁ - 3 * (K↑L)E.a1 * (K↑L)E.a2 * x₁
                    - 3 * (K↑L)E.a3 * x₁ + (K↑L)E.a1 ^ 2 * y₁ - 2 * (K↑L)E.a2 * y₁
                    - (K↑L)E.a1 * (K↑L)E.a4 - (K↑L)E.a2 * (K↑L)E.a3))
            + (8 * x₁ ^ 3 + 8 * (K↑L)E.a2 * x₁ ^ 2 - 2 * (K↑L)E.a1 * x₁ * y₁ + y₁ ^ 2
               + 2 * (K↑L)E.a2 ^ 2 * x₁ + 2 * (K↑L)E.a4 * x₁ - (K↑L)E.a1 * (K↑L)E.a2 * y₁
               + (K↑L)E.a3 * y₁ + (K↑L)E.a2 * (K↑L)E.a4 - (K↑L)E.a6)
          := by dsimp [x₃]; ring,
        -- substitute l step 1
        have lSimp1 :
            l * (y₁ + (y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3))
            + (-3 * x₁ ^ 2 + (K↑L)E.a1 ^ 2 * x₁ - 2 * (K↑L)E.a2 * x₁ + 3 * (K↑L)E.a1 * y₁
               + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4)
          = (y₁ + (y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3)) * (K↑L)E.a1
          := by rw [inv_mul_cancel_right₀ yNe]; ring,
        -- substitute l step 2
        have lSimp2 :
            l * ((y₁ + (y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3)) * (K↑L)E.a1)
            + (-6 * (K↑L)E.a1 * x₁ ^ 2 - 6 * x₁ * y₁ - 3 * (K↑L)E.a1 * (K↑L)E.a2 * x₁
               - 3 * (K↑L)E.a3 * x₁ + (K↑L)E.a1 ^ 2 * y₁ - 2 * (K↑L)E.a2 * y₁
               - (K↑L)E.a1 * (K↑L)E.a4 - (K↑L)E.a2 * (K↑L)E.a3)
          = (y₁ + (y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3)) * (-3 * x₁ - (K↑L)E.a2)
          := by rw [← mul_assoc l, inv_mul_cancel_right₀ yNe]; ring,
        -- substitute l step 3
        have lSimp3 :
            l * ((y₁ + (y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3)) * (-3 * x₁ - (K↑L)E.a2))
            + (8 * x₁ ^ 3 + 8 * (K↑L)E.a2 * x₁ ^ 2 - 2 * (K↑L)E.a1 * x₁ * y₁ + y₁ ^ 2
               + 2 * (K↑L)E.a2 ^ 2 * x₁ + 2 * (K↑L)E.a4 * x₁ - (K↑L)E.a1 * (K↑L)E.a2 * y₁
               + (K↑L)E.a3 * y₁ + (K↑L)E.a2 * (K↑L)E.a4 - (K↑L)E.a6)
          = 0
          := by rw [← mul_assoc l, inv_mul_cancel_right₀ yNe, ← w₁]; ring,
        -- rewrite Weierstrass equation as w₃(x, y) = 0 and sequence steps
        rw [← sub_eq_zero, ySimp, xSimp, lSimp1, lSimp2, lSimp3]
      end⟩
    -- add points with different y-coordinates
    else
      0

/-- Addition in `E(L)`. -/
instance has_add : has_add (E/L) := ⟨add E L⟩

/-- Left identity in `E(L)`. -/
@[simp]
lemma zero_add : ∀ P : E/L, 0 + P = P := λ P, by cases P; refl

/-- Right identity in `E(L)`. -/
@[simp]
lemma add_zero : ∀ P : E/L, P + 0 = P := λ P, by cases P; refl

/-- Left negation in `E(L)`. -/
@[simp]
lemma add_left_neg : ∀ P : E/L, -P + P = 0
  | 0        := by refl
  | (some P) := let ⟨⟨_, _⟩, _⟩ := P in
    by dsimp [has_neg.neg]; dsimp [neg]; dsimp [has_add.add]; simp [add]

/-- Commutativity in `E(L)`. -/
lemma add_comm : ∀ (P Q : E/L), P + Q = Q + P
  | _         0       := by simp
  | 0         _       := by simp
  | (some P) (some Q) := let (⟨⟨x₁, y₁⟩, w₁⟩, ⟨⟨x₂, y₂⟩, w₂⟩) := (P, Q) in
    sorry

/-- Associativity in `E(L)`. -/
lemma add_assoc : ∀ P Q R : E/L, (P + Q) + R = P + (Q + R)
  | _        _        0        := by simp
  | _        0        _        := by simp
  | 0        _        _        := by simp
  | (some P) (some Q) (some R) := let (⟨⟨x₁, y₁⟩, w₁⟩, ⟨⟨x₂, y₂⟩, w₂⟩, ⟨⟨x₃, y₃⟩, w₃⟩) := (P, Q, R) in
    sorry

/-- `E(L)` is an additive commutative group. -/
instance add_comm_group : add_comm_group (E/L) :=
  { zero         := 0
  , neg          := neg E L
  , add          := add E L
  , zero_add     := zero_add E L
  , add_zero     := add_zero E L
  , add_left_neg := add_left_neg E L
  , add_comm     := add_comm E L
  , add_assoc    := add_assoc E L
  }

end EllipticCurve
