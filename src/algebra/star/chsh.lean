/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.star.basic
import algebra.order.algebra
import analysis.special_functions.pow

/-!
# The Clauser-Horne-Shimony-Holt inequality and Tsirelson's inequality.

We establish a version of the Clauser-Horne-Shimony-Holt (CHSH) inequality
(which is a generalization of Bell's inequality).
This is a foundational result which implies that
quantum mechanics is not a local hidden variable theory.

As usually stated the CHSH inequality requires substantial language from physics and probability,
but it is possible to give a statement that is purely about ordered `*`-algebras.
We do that here, to avoid as many practical and logical dependencies as possible.
Since the algebra of observables of any quantum system is an ordered `*`-algebra
(in particular a von Neumann algebra) this is a strict generalization of the usual statement.

Let `R` be a `*`-ring.

A CHSH tuple in `R` consists of
* four elements `A₀ A₁ B₀ B₁ : R`, such that
* each `Aᵢ` and `Bⱼ` is a self-adjoint involution, and
* the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that the four elements are observables (hence self-adjoint)
that take values ±1 (hence involutions), and that the `Aᵢ` are spacelike separated from the `Bⱼ`
(and hence commute).

The CHSH inequality says that when `R` is an ordered `*`-ring
(that is, a `*`-ring which is ordered, and for every `r : R`, `0 ≤ star r * r`),
which is moreover *commutative*, we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`

On the other hand, Tsirelson's inequality says that for any ordered `*`-ring we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2√2`

(A caveat: in the commutative case we need 2⁻¹ in the ring,
and in the noncommutative case we need √2 and √2⁻¹.
To keep things simple we just assume our rings are ℝ-algebras.)

The proofs I've seen in the literature either
assume a significant framework for quantum mechanics,
or assume the ring is a `C^*`-algebra.
In the `C^*`-algebra case,
the order structure is completely determined by the `*`-algebra structure:
`0 ≤ A` iff there exists some `B` so `A = star B * B`.
There's a nice proof of both bounds in this setting at
https://en.wikipedia.org/wiki/Tsirelson%27s_bound
The proof given here is purely algebraic.

## Future work

One can show that Tsirelson's inequality is tight.
In the `*`-ring of n-by-n complex matrices, if `A ≤ λ I` for some `λ : ℝ`,
then every eigenvalue has absolute value at most `λ`.
There is a CHSH tuple in 4-by-4 matrices such that
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` has `2√2` as an eigenvalue.

## References

* [Clauser, Horne, Shimony, Holt,
  *Proposed experiment to test local hidden-variable theories*][zbMATH06785026]
* [Bell, *On the Einstein Podolsky Rosen Paradox*][MR3790629]
* [Tsirelson, *Quantum generalizations of Bell's inequality*][MR577178]

-/

universes u

/--
A CHSH tuple in a `star_monoid R` consists of 4 self-adjoint involutions `A₀ A₁ B₀ B₁` such that
the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that `A₀` and `A₁` are a pair of boolean observables which
are spacelike separated from another pair `B₀` and `B₁` of boolean observables.
-/
@[nolint has_inhabited_instance]
structure is_CHSH_tuple {R} [monoid R] [star_monoid R] (A₀ A₁ B₀ B₁ : R) :=
(A₀_inv : A₀^2 = 1) (A₁_inv : A₁^2 = 1) (B₀_inv : B₀^2 = 1) (B₁_inv : B₁^2 = 1)
(A₀_sa : star A₀ = A₀) (A₁_sa : star A₁ = A₁) (B₀_sa : star B₀ = B₀) (B₁_sa : star B₁ = B₁)
(A₀B₀_commutes : A₀ * B₀ = B₀ * A₀)
(A₀B₁_commutes : A₀ * B₁ = B₁ * A₀)
(A₁B₀_commutes : A₁ * B₀ = B₀ * A₁)
(A₁B₁_commutes : A₁ * B₁ = B₁ * A₁)

variables {R : Type u}

/--
Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered `*`-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
lemma CHSH_inequality_of_comm
  [ordered_comm_ring R] [star_ordered_ring R] [algebra ℝ R] [ordered_smul ℝ R]
  (A₀ A₁ B₀ B₁ : R) (T : is_CHSH_tuple A₀ A₁ B₀ B₁) :
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
begin
  let P := (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁),
  have i₁ : 0 ≤ P,
  { have idem : P * P = 4 * P,
    { -- If we had a Gröbner basis algorithm, this would be trivial.
      -- Without one, it is somewhat tedious!
      dsimp [P],
      simp only [add_mul, mul_add, sub_mul, mul_sub, mul_comm, mul_assoc, add_assoc],
      repeat { conv in (B₀ * (A₀ * B₀))
      { rw [T.A₀B₀_commutes, ←mul_assoc B₀ B₀ A₀, ←sq, T.B₀_inv, one_mul], } },
      repeat { conv in (B₀ * (A₁ * B₀))
      { rw [T.A₁B₀_commutes, ←mul_assoc B₀ B₀ A₁, ←sq, T.B₀_inv, one_mul], } },
      repeat { conv in (B₁ * (A₀ * B₁))
      { rw [T.A₀B₁_commutes, ←mul_assoc B₁ B₁ A₀, ←sq, T.B₁_inv, one_mul], } },
      repeat { conv in (B₁ * (A₁ * B₁))
      { rw [T.A₁B₁_commutes, ←mul_assoc B₁ B₁ A₁, ←sq, T.B₁_inv, one_mul], } },
      conv in (A₀ * (B₀ * (A₀ * B₁)))
      { rw [←mul_assoc, T.A₀B₀_commutes, mul_assoc, ←mul_assoc A₀, ←sq, T.A₀_inv, one_mul], },
      conv in (A₀ * (B₁ * (A₀ * B₀)))
      { rw [←mul_assoc, T.A₀B₁_commutes, mul_assoc, ←mul_assoc A₀, ←sq, T.A₀_inv, one_mul], },
      conv in (A₁ * (B₀ * (A₁ * B₁)))
      { rw [←mul_assoc, T.A₁B₀_commutes, mul_assoc, ←mul_assoc A₁, ←sq, T.A₁_inv, one_mul], },
      conv in (A₁ * (B₁ * (A₁ * B₀)))
      { rw [←mul_assoc, T.A₁B₁_commutes, mul_assoc, ←mul_assoc A₁, ←sq, T.A₁_inv, one_mul], },
      simp only [←sq, T.A₀_inv, T.A₁_inv],
      simp only [mul_comm A₁ A₀, mul_comm B₁ B₀, mul_left_comm A₁ A₀, mul_left_comm B₁ B₀,
        mul_left_comm B₀ A₀, mul_left_comm B₀ A₁, mul_left_comm B₁ A₀, mul_left_comm B₁ A₁],
      norm_num,
      simp only [mul_comm _ (2 : R), mul_comm _ (4 : R),
        mul_left_comm _ (2 : R), mul_left_comm _ (4 : R)],
      abel,
      simp only [neg_mul_eq_neg_mul_symm, mul_one, int.cast_bit0, one_mul, int.cast_one,
        zsmul_eq_mul, int.cast_neg],
      simp only [←mul_assoc, ←add_assoc],
      norm_num, },
    have idem' : P = (1 / 4 : ℝ) • (P * P),
    { have h : 4 * P = (4 : ℝ) • P := by simp [algebra.smul_def],
      rw [idem, h, ←mul_smul],
      norm_num, },
    have sa : star P = P,
    { dsimp [P],
      simp only [star_add, star_sub, star_mul, star_bit0, star_one,
        T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa, mul_comm B₀, mul_comm B₁], },
    rw idem',
    conv_rhs { congr, skip, congr, rw ←sa, },
    convert smul_le_smul_of_nonneg (star_mul_self_nonneg : 0 ≤ star P * P) _,
    { simp, },
    { apply_instance, },
    { norm_num, }, },
  apply le_of_sub_nonneg,
  simpa only [sub_add_eq_sub_sub, ←sub_add] using i₁,
end

/-!
We now prove some rather specialized lemmas in preparation for the Tsirelson inequality,
which we hide in a namespace as they are unlikely to be useful elsewhere.
-/
local notation `√2` := (real.sqrt 2 : ℝ)

namespace tsirelson_inequality


/-!
Before proving Tsirelson's bound,
we prepare some easy lemmas about √2.
-/

-- This calculation, which we need for Tsirelson's bound,
-- defeated me. Thanks for the rescue from Shing Tak Lam!
lemma tsirelson_inequality_aux : √2 * √2 ^ 3 = √2 * (2 * √2⁻¹ + 4 * (√2⁻¹ * 2⁻¹)) :=
begin
  ring_nf,
  rw [mul_assoc, inv_mul_cancel, real.sqrt_eq_rpow, ←real.rpow_nat_cast, ←real.rpow_mul],
  { norm_num,
    rw show (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ (2 : ℕ), by { rw ←real.rpow_nat_cast, norm_num },
    norm_num },
  { norm_num, },
  { norm_num, },
end

lemma sqrt_two_inv_mul_self : √2⁻¹ * √2⁻¹ = (2⁻¹ : ℝ) :=
by { rw [←mul_inv₀], norm_num, }

end tsirelson_inequality
open tsirelson_inequality

/--
In a noncommutative ordered `*`-algebra over ℝ,
Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

We prove this by providing an explicit sum-of-squares decomposition
of the difference.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
lemma tsirelson_inequality
  [ordered_ring R] [star_ordered_ring R]
  [algebra ℝ R] [ordered_smul ℝ R] [star_module ℝ R]
  (A₀ A₁ B₀ B₁ : R) (T : is_CHSH_tuple A₀ A₁ B₀ B₁) :
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2^3 • 1 :=
begin
  -- abel will create `ℤ` multiplication. We will `simp` them away to `ℝ` multiplication.
  have M : ∀ (m : ℤ) (a : ℝ) (x : R), m • a • x = ((m : ℝ) * a) • x :=
    λ m a x, by rw [zsmul_eq_smul_cast ℝ, ← mul_smul],
  let P := √2⁻¹ • (A₁ + A₀) - B₀,
  let Q := √2⁻¹ • (A₁ - A₀) + B₁,
  have w : √2^3 • 1 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁ = √2⁻¹ • (P^2 + Q^2),
  { dsimp [P, Q],
    -- distribute out all the powers and products appearing on the RHS
    simp only [sq, sub_mul, mul_sub, add_mul, mul_add, smul_add, smul_sub],
    -- pull all coefficients out to the front, and combine `√2`s where possible
    simp only [algebra.mul_smul_comm, algebra.smul_mul_assoc, ←mul_smul, sqrt_two_inv_mul_self],
    -- replace Aᵢ * Aᵢ = 1 and Bᵢ * Bᵢ = 1
    simp only [←sq, T.A₀_inv, T.A₁_inv, T.B₀_inv, T.B₁_inv],
    -- move Aᵢ to the left of Bᵢ
    simp only [←T.A₀B₀_commutes, ←T.A₀B₁_commutes, ←T.A₁B₀_commutes, ←T.A₁B₁_commutes],
    -- collect terms, simplify coefficients, and collect terms again:
    abel,
    -- all terms coincide, but the last one. Simplify all other terms
    simp only [M],
    simp only [neg_mul_eq_neg_mul_symm, int.cast_bit0, one_mul, mul_inv_cancel_of_invertible,
      int.cast_one, one_smul, int.cast_neg, add_right_inj, neg_smul, ← add_smul],
    -- just look at the coefficients now:
    congr,
    exact mul_left_cancel₀ (by norm_num) tsirelson_inequality_aux, },
  have pos : 0 ≤ √2⁻¹ • (P^2 + Q^2), {
    have P_sa : star P = P,
    { dsimp [P],
      simp only [star_smul, star_add, star_sub, star_id_of_comm,
        T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa], },
    have Q_sa : star Q = Q,
    { dsimp [Q],
      simp only [star_smul, star_add, star_sub, star_id_of_comm,
        T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa], },
    have P2_nonneg : 0 ≤ P^2,
    { rw [sq],
      conv { congr, skip, congr, rw ←P_sa, },
      convert (star_mul_self_nonneg : 0 ≤ star P * P), },
    have Q2_nonneg : 0 ≤ Q^2,
    { rw [sq],
      conv { congr, skip, congr, rw ←Q_sa, },
      convert (star_mul_self_nonneg : 0 ≤ star Q * Q), },
    convert smul_le_smul_of_nonneg (add_nonneg P2_nonneg Q2_nonneg)
      (le_of_lt (show 0 < √2⁻¹, by norm_num)), -- `norm_num` can't directly show `0 ≤ √2⁻¹`
    simp, },
  apply le_of_sub_nonneg,
  simpa only [sub_add_eq_sub_sub, ←sub_add, w] using pos,
end
