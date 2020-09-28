import algebra.star.basic
import algebra.invertible
import algebra.ordered_ring

universes u

variables (R : Type u)

section
variables {R} [monoid R] [star_monoid R]

def involution (r : R) : Prop := r * r = 1
def self_adjoint (r : R) : Prop := star r = r

structure is_chsh_tuple (A B C D : R) :=
(A_inv : involution A) (B_inv : involution B) (C_inv : involution C) (D_inv : involution D)
(A_sa : self_adjoint A) (B_sa : self_adjoint B) (C_sa : self_adjoint C) (D_sa : self_adjoint D)
(AB : A * B = B * A)
(AD : A * D = D * A)
(CB : C * B = B * C)
(CD : C * D = D * C)

end

section
variables {R}

lemma nat_mul_le_nat_mul [ordered_semiring R] {a b : R} (h : a ≤ b) (c : ℕ) : (c : R) * a ≤ c * b :=
sorry

lemma nonneg_of_two_mul_nonneg [ordered_semiring R] [invertible (2 : R)] {r : R} (h : 0 ≤ 2 * r) :
  0 ≤ r :=
begin
  have := mul_le_mul_of_nonneg_left h (by { simp, sorry, } : 0 ≤ ⅟(2 : R)),
  simpa using this,
end

/--
Given a CHSH tuple (A, B, C, D) in a *commutative* ordered *-ring with `⅟2`,
`A * B + B * C + C * D - A * D ≤ 2`.
-/
lemma commutative_chsh_inequality
  [ordered_comm_ring R] [star_ordered_ring R] [invertible (2 : R)]
  (A B C D : R) (T : is_chsh_tuple A B C D) :
  A * B + B * C + C * D - A * D ≤ 2 :=
begin
  let P := 2 + A * D - A * B - B * C - C * D,
  have i₁ : 0 ≤ P,
  { have idem : P * P = 2 * P,
    { dsimp [P], sorry },
    have sa : star P = P,
    { dsimp [P], sorry, },
    rw ←idem,
    conv_rhs { congr, rw ←sa, },
    exact star_mul_self_nonneg, },
  have i₂ : 0 ≤ 2 + A * D - A * B - B * C - C * D,
  { have := mul_le_mul_of_nonneg_left i₁ (sorry : 0 ≤ (2 : R)),
    simpa [P] using this, },
  sorry,
end


/--
In a noncommutative ordered *-ring with an invertible and central square root of two,
the best we can prove for a CHSH tuple (A, B, C, D) is
`A * B + B * C + C * D - A * D ≤ 2 * sqrt_two`.
-/
lemma noncommutative_chsh_inequality
  [ordered_ring R] [star_ordered_ring R]
  (sqrt_two : R) (h : sqrt_two^2 = 2) [invertible sqrt_two]
  (comm : ∀ r : R, sqrt_two * r = r * sqrt_two)
  (A B C D : R) (T : is_chsh_tuple A B C D) :
  A * B + B * C + C * D - A * D ≤ 2 * sqrt_two := sorry

-- In fact, this is optimal, witnessed by
-- `R = (matrix (fin 2) (fin 2) ℝ) ⊗ (matrix (fin 2) (fin 2) ℝ)`
-- and `A =

end
