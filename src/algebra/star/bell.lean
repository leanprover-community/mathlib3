import algebra.star.basic
import algebra.algebra.ordered
import analysis.special_functions.pow

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

def involution (r : R) : Prop := r^2 = 1
def self_adjoint (r : R) : Prop := star r = r

structure is_chsh_tuple (A₀ A₁ B₀ B₁ : R) :=
(A₀_inv : A₀^2 = 1) (B₀_inv : B₀^2 = 1) (A₁_inv : A₁^2 = 1) (B₁_inv : B₁^2 = 1)
(A₀_sa : self_adjoint A₀) (B₀_sa : self_adjoint B₀) (A₁_sa : self_adjoint A₁) (B₁_sa : self_adjoint B₁)
(A₀B₀_commutes : A₀ * B₀ = B₀ * A₀)
(A₀B₁_commutes : A₀ * B₁ = B₁ * A₀)
(A₁B₀_commutes : A₁ * B₀ = B₀ * A₁)
(A₁B₁_commutes : A₁ * B₁ = B₁ * A₁)

-- namespace is_chsh_tuple
-- variables {A₀ A₁ B₀ B₁ : R}

-- @[simp] lemma involution_foo (A B : R) (inv : A^2 = 1) (commutes : A * B = B * A) :
--   A * (B * A) = B :=
-- by rw [←commutes, ←mul_assoc, ←pow_two, inv, one_mul]

-- end is_chsh_tuple

end

section
variables {R}

/--
Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered *-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
lemma commutative_chsh_inequality
  [ordered_comm_ring R] [star_ordered_ring R] [ordered_algebra ℝ R]
  (A₀ A₁ B₀ B₁ : R) (T : is_chsh_tuple A₀ A₁ B₀ B₁) :
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
begin
  let P := (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁),
  have i₁ : 0 ≤ P,
  { have idem : P * P = 2 * P,
    { -- If we have a Gröbner basis algorithm, this would be trivial.
      -- Without one, it is a painful mess!
      dsimp [P],
      simp [add_mul, mul_add, sub_mul, mul_sub, mul_comm, mul_assoc],
      have q := T.B₀_inv,
      have qq := T.A₁B₀_commutes.symm,
      simp [q, qq],
      },
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


local notation `√2` := (2^(2⁻¹ : ℝ) : ℝ)

@[simp] lemma sqrt_two_inv_sq : √2⁻¹ * √2⁻¹ = (2⁻¹ : ℝ) := sorry

@[simp] lemma foo {α : Type*} [add_comm_group α] [module ℝ α] {X : α} :
  2 •ℤ (2⁻¹ : ℝ) • X = X := sorry
@[simp] lemma foo' {α : Type*} [add_comm_group α] [module ℝ α] {X : α} :
  (-2) •ℤ (2⁻¹ : ℝ) • X = - X := sorry

example {α : Type} [add_comm_group α] {x y : α} (h : false) :
   x = - y :=
begin
  abel,
  abel, -- should fail, but instead inserts an additional `1 •ℤ `

  exfalso, assumption,
end

/--
In a noncommutative ordered *-algebra over ℝ,
the best we can prove for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
lemma noncommutative_chsh_inequality
  [ordered_comm_ring R] [star_ordered_ring R] [ordered_algebra ℝ R]
  (A₀ A₁ B₀ B₁ : R) (T : is_chsh_tuple A₀ A₁ B₀ B₁) :
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2^3 • 1 :=
begin
  let P := √2⁻¹ • (A₁ + A₀) - B₀,
  let Q := √2⁻¹ • (A₁ - A₀) - B₁,
  have w : √2^3 • 1 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁ = √2⁻¹ • (P^2 + Q^2),
  { dsimp [P, Q],
    simp only [pow_two, sub_mul, mul_sub, add_mul, mul_add, smul_add, smul_sub],
    simp only [algebra.mul_smul_comm, algebra.smul_mul_assoc, ←mul_smul, sqrt_two_inv_sq],
    simp only [←pow_two, T.A₀_inv, T.A₁_inv, T.B₀_inv, T.B₁_inv],
    simp only [←T.A₀B₀_commutes, ←T.A₀B₁_commutes, ←T.A₁B₀_commutes, ←T.A₁B₁_commutes],
    abel,
    abel,
    simp only [foo, foo'],
    abel,
    },
  have pos : 0 ≤ √2⁻¹ • (P^2 + Q^2), {
    have P_sa : P = star P := sorry,
    have Q_sa : Q = star Q := sorry,
    sorry,
  },
  apply le_of_sub_nonneg,
  simpa only [sub_add_eq_sub_sub, ←sub_add, w] using pos,
end

-- In fact, this is optimal, witnessed by
-- `R = (matrix (fin 2) (fin 2) ℝ) ⊗ (matrix (fin 2) (fin 2) ℝ)`
-- and `A =

end
