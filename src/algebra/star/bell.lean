import algebra.star.basic
import algebra.algebra.ordered
import data.real.basic

/-!
# The Clauser-Horne-Shimony-Holt (CHSH) inequality.

Bell's inequality




## References

* J.F. Clauser; M.A. Horne; A. Shimony; R.A. Holt (1969),
  "Proposed experiment to test local hidden-variable theories",
  Phys. Rev. Lett., 23 (15): 880–4, doi:10.1103/PhysRevLett.23.880
* J.S. Bell (1964), "On the Einstein Podolsky Rosen Paradox",
  Physics Physique Физика, 1 (3): 195–200, doi:10.1103/PhysicsPhysiqueFizika.1.195,
  reproduced as Ch. 2 of J. S. Bell (1987), "Speakable and Unspeakable in Quantum Mechanics", CUP

-/

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

/--
Given a CHSH tuple (A, B, C, D) in a *commutative* ordered *-algebra over ℝ,
`A * B + B * C + C * D - A * D ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
lemma commutative_chsh_inequality
  [ordered_comm_ring R] [star_ordered_ring R] [ordered_algebra ℝ R]
  (A B C D : R) (T : is_chsh_tuple A B C D) :
  A * B + B * C + C * D - A * D ≤ 2 :=
begin
  let P := (1/2 : ℝ) • (2 + A * D - A * B - B * C - C * D),
  have i₁ : 0 ≤ P,
  { have idem : P * P = P,
    { dsimp [P],
      cancel_denoms,
      simp [add_mul, mul_add, sub_mul, mul_sub], },
    have sa : star P = P,
    { dsimp [P], sorry, },
    rw ←idem,
    conv_rhs { congr, rw ←sa, },
    exact star_mul_self_nonneg, },
  have i₂ : 0 ≤ 2 + A * D - A * B - B * C - C * D,
  { have := smul_le_smul_of_nonneg i₁ (by norm_num : 0 ≤ (2 : ℝ)),
    simpa [P, two_ne_zero] using this, },
  apply le_of_sub_nonneg,
  simp only [sub_add_eq_sub_sub, ←sub_add],
  convert i₂ using 1,
  abel,
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
