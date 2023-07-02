/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
import data.nat.cast.with_top
import field_theory.is_alg_closed.basic
import ring_theory.witt_vector.discrete_valuation_ring

/-!
# Solving equations about the Frobenius map on the field of fractions of `𝕎 k`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The goal of this file is to prove `witt_vector.exists_frobenius_solution_fraction_ring`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `φ b * a = p ^ m * b`, where `φ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `𝕎 k` directly,
moving to the field of fractions at the end.
See `witt_vector.frobenius_rotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`witt_vector.witt_mul`, `witt_polynomial`) to show that they satisfy the desired equation.

Preliminary work is done in the dependency `ring_theory.witt_vector.mul_coeff`
to isolate the `n+1`st coefficients of `x` and `y` in the `n+1`st coefficient of `x*y`.

This construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].
We approximately follow an approach sketched on MathOverflow:
<https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors>

The result is a dependency for the proof of `witt_vector.isocrystal_classification`,
the classification of one-dimensional isocrystals over an algebraically closed field.
-/

noncomputable theory

namespace witt_vector

variables (p : ℕ) [hp : fact p.prime]
local notation `𝕎` := witt_vector p

namespace recursion_main

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `witt_poly_prod n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.

-/

section comm_ring
include hp
variables {k : Type*} [comm_ring k] [char_p k p]
open polynomial

/-- The root of this polynomial determines the `n+1`st coefficient of our solution. -/
def succ_nth_defining_poly (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k) : polynomial k :=
X^p * C (a₁.coeff 0 ^ (p^(n+1))) - X * C (a₂.coeff 0 ^ (p^(n+1)))
  + C (a₁.coeff (n+1) * ((bs 0)^p)^(p^(n+1)) +
      nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁) -
      a₂.coeff (n+1) * (bs 0)^p^(n+1) - nth_remainder p n bs (truncate_fun (n+1) a₂))

lemma succ_nth_defining_poly_degree [is_domain k] (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_defining_poly p n a₁ a₂ bs).degree = p :=
begin
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n+1))).degree = p,
  { rw [degree_mul, degree_C],
    { simp only [nat.cast_with_bot, add_zero, degree_X, degree_pow, nat.smul_one_eq_coe] },
    { exact pow_ne_zero _ ha₁ } },
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n+1)) - X * C (a₂.coeff 0 ^ p ^ (n+1))).degree = p,
  { rw [degree_sub_eq_left_of_degree_lt, this],
    rw [this, degree_mul, degree_C, degree_X, add_zero],
    { exact_mod_cast hp.out.one_lt },
    { exact pow_ne_zero _ ha₂ } },
  rw [succ_nth_defining_poly, degree_add_eq_left_of_degree_lt, this],
  apply lt_of_le_of_lt (degree_C_le),
  rw [this],
  exact_mod_cast hp.out.pos
end

end comm_ring

section is_alg_closed
include hp
variables {k : Type*} [field k] [char_p k p] [is_alg_closed k]

lemma root_exists (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ b : k, (succ_nth_defining_poly p n a₁ a₂ bs).is_root b :=
is_alg_closed.exists_root _ $
  by simp only [(succ_nth_defining_poly_degree p n a₁ a₂ bs ha₁ ha₂), hp.out.ne_zero,
    with_top.coe_eq_zero, ne.def, not_false_iff]

/-- This is the `n+1`st coefficient of our solution, projected from `root_exists`. -/
def succ_nth_val (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : k :=
classical.some (root_exists p n a₁ a₂ bs ha₁ ha₂)

lemma succ_nth_val_spec (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_defining_poly p n a₁ a₂ bs).is_root (succ_nth_val p n a₁ a₂ bs ha₁ ha₂) :=
classical.some_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)

lemma succ_nth_val_spec' (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_val p n a₁ a₂ bs ha₁ ha₂)^p * a₁.coeff 0 ^ (p^(n+1)) +
    a₁.coeff (n+1) * ((bs 0)^p)^(p^(n+1)) +
    nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁)
   = (succ_nth_val p n a₁ a₂ bs ha₁ ha₂) * a₂.coeff 0 ^ (p^(n+1)) +
     a₂.coeff (n+1) * (bs 0)^(p^(n+1)) + nth_remainder p n bs (truncate_fun (n+1) a₂) :=
begin
  rw ← sub_eq_zero,
  have := succ_nth_val_spec p n a₁ a₂ bs ha₁ ha₂,
  simp only [polynomial.map_add, polynomial.eval_X, polynomial.map_pow, polynomial.eval_C,
    polynomial.eval_pow, succ_nth_defining_poly, polynomial.eval_mul, polynomial.eval_add,
    polynomial.eval_sub, polynomial.map_mul, polynomial.map_sub, polynomial.is_root.def] at this,
  convert this using 1,
  ring
end

end is_alg_closed
end recursion_main

namespace recursion_base
include hp
variables {k : Type*} [field k] [is_alg_closed k]

lemma solution_pow (a₁ a₂ : 𝕎 k) :
  ∃ x : k, x^(p-1) = a₂.coeff 0 / a₁.coeff 0 :=
is_alg_closed.exists_pow_nat_eq _ $ by linarith [hp.out.one_lt, le_of_lt hp.out.one_lt]

/-- The base case (0th coefficient) of our solution vector. -/
def solution (a₁ a₂ : 𝕎 k) : k :=
classical.some $ solution_pow p a₁ a₂

lemma solution_spec (a₁ a₂ : 𝕎 k) :
  (solution p a₁ a₂)^(p-1) = a₂.coeff 0 / a₁.coeff 0 :=
classical.some_spec $ solution_pow p a₁ a₂

lemma solution_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  solution p a₁ a₂ ≠ 0 :=
begin
  intro h,
  have := solution_spec p a₁ a₂,
  rw [h, zero_pow] at this,
  { simpa [ha₁, ha₂] using _root_.div_eq_zero_iff.mp this.symm },
  { linarith [hp.out.one_lt, le_of_lt hp.out.one_lt] }
end

lemma solution_spec' {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (a₂ : 𝕎 k) :
  (solution p a₁ a₂)^p * a₁.coeff 0 = (solution p a₁ a₂) * a₂.coeff 0 :=
begin
  have := solution_spec p a₁ a₂,
  cases nat.exists_eq_succ_of_ne_zero hp.out.ne_zero with q hq,
  have hq' : q = p - 1 := by simp only [hq, tsub_zero, nat.succ_sub_succ_eq_sub],
  conv_lhs {congr, congr, skip, rw hq},
  rw [pow_succ', hq', this],
  field_simp [ha₁, mul_comm],
end

end recursion_base

open recursion_main recursion_base

section frobenius_rotation

section is_alg_closed
include hp
variables {k : Type*} [field k] [char_p k p] [is_alg_closed k]

/--
Recursively defines the sequence of coefficients for `witt_vector.frobenius_rotation`.
-/
noncomputable def frobenius_rotation_coeff {a₁ a₂ : 𝕎 k}
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : ℕ → k
| 0       := solution p a₁ a₂
| (n + 1) := succ_nth_val p n a₁ a₂ (λ i, frobenius_rotation_coeff i.val) ha₁ ha₂
using_well_founded { dec_tac := `[apply fin.is_lt] }

/--
For nonzero `a₁` and `a₂`, `frobenius_rotation a₁ a₂` is a Witt vector that satisfies the
equation `frobenius (frobenius_rotation a₁ a₂) * a₁ = (frobenius_rotation a₁ a₂) * a₂`.
-/
def frobenius_rotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : 𝕎 k :=
witt_vector.mk p (frobenius_rotation_coeff p ha₁ ha₂)

lemma frobenius_rotation_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  frobenius_rotation p ha₁ ha₂ ≠ 0 :=
begin
  intro h,
  apply solution_nonzero p ha₁ ha₂,
  simpa [← h, frobenius_rotation, frobenius_rotation_coeff] using witt_vector.zero_coeff p k 0
end

lemma frobenius_frobenius_rotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  frobenius (frobenius_rotation p ha₁ ha₂) * a₁ = (frobenius_rotation p ha₁ ha₂) * a₂ :=
begin
  ext n,
  induction n with n ih,
  { simp only [witt_vector.mul_coeff_zero, witt_vector.coeff_frobenius_char_p,
      frobenius_rotation, frobenius_rotation_coeff],
    apply solution_spec' _ ha₁ },
  { simp only [nth_remainder_spec, witt_vector.coeff_frobenius_char_p, frobenius_rotation_coeff,
      frobenius_rotation, fin.val_eq_coe],
    have := succ_nth_val_spec' p n a₁ a₂
      (λ (i : fin (n + 1)), frobenius_rotation_coeff p ha₁ ha₂ i.val) ha₁ ha₂,
    simp only [frobenius_rotation_coeff, fin.val_eq_coe, fin.val_zero] at this,
    convert this using 4,
    apply truncated_witt_vector.ext,
    intro i,
    simp only [fin.val_eq_coe, witt_vector.coeff_truncate_fun, witt_vector.coeff_frobenius_char_p],
    refl }
end

local notation `φ` := is_fraction_ring.field_equiv_of_ring_equiv (frobenius_equiv p k)

lemma exists_frobenius_solution_fraction_ring_aux
  (m n : ℕ) (r' q' : 𝕎 k) (hr' : r'.coeff 0 ≠ 0) (hq' : q'.coeff 0 ≠ 0)
  (hq : ↑p ^ n * q' ∈ non_zero_divisors (𝕎 k)) :
  let b : 𝕎 k := frobenius_rotation p hr' hq' in
  is_fraction_ring.field_equiv_of_ring_equiv
      (frobenius_equiv p k)
      (algebra_map (𝕎 k) (fraction_ring (𝕎 k)) b) *
    localization.mk (↑p ^ m * r') ⟨↑p ^ n * q', hq⟩ =
  ↑p ^ (m - n : ℤ) * algebra_map (𝕎 k) (fraction_ring (𝕎 k)) b :=
begin
  intros b,
  have key : witt_vector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * (p ^ n * q'),
  { have H := congr_arg (λ x : 𝕎 k, x * p ^ m * p ^ n) (frobenius_frobenius_rotation p hr' hq'),
    dsimp at H,
    refine (eq.trans _ H).trans _; ring },
  have hq'' : algebra_map (𝕎 k) (fraction_ring (𝕎 k)) q' ≠ 0,
  { have hq''' : q' ≠ 0 := λ h, hq' (by simp [h]),
    simpa only [ne.def, map_zero] using
      (is_fraction_ring.injective (𝕎 k) (fraction_ring (𝕎 k))).ne hq''' },
  rw zpow_sub₀ (fraction_ring.p_nonzero p k),
  field_simp [fraction_ring.p_nonzero p k],
  simp only [is_fraction_ring.field_equiv_of_ring_equiv,
    is_localization.ring_equiv_of_ring_equiv_eq, ring_equiv.coe_of_bijective],
  convert congr_arg (λ x, algebra_map (𝕎 k) (fraction_ring (𝕎 k)) x) key using 1,
  { simp only [ring_hom.map_mul, ring_hom.map_pow, map_nat_cast, frobenius_equiv_apply],
    ring },
  { simp only [ring_hom.map_mul, ring_hom.map_pow, map_nat_cast] }
end

lemma exists_frobenius_solution_fraction_ring {a : fraction_ring (𝕎 k)} (ha : a ≠ 0) :
  ∃ (b : fraction_ring (𝕎 k)) (hb : b ≠ 0) (m : ℤ), φ b * a = p ^ m * b :=
begin
  revert ha,
  refine localization.induction_on a _,
  rintros ⟨r, q, hq⟩ hrq,
  have hq0 : q ≠ 0 := mem_non_zero_divisors_iff_ne_zero.1 hq,
  have hr0 : r ≠ 0 := λ h, hrq (by simp [h]),
  obtain ⟨m, r', hr', rfl⟩ := exists_eq_pow_p_mul r hr0,
  obtain ⟨n, q', hq', rfl⟩ := exists_eq_pow_p_mul q hq0,
  let b := frobenius_rotation p hr' hq',
  refine ⟨algebra_map (𝕎 k) _ b, _, m - n, _⟩,
  { simpa only [map_zero] using
      (is_fraction_ring.injective (witt_vector p k) (fraction_ring (witt_vector p k))).ne
        (frobenius_rotation_nonzero p hr' hq')},
  exact exists_frobenius_solution_fraction_ring_aux p m n r' q' hr' hq' hq,
end

end is_alg_closed

end frobenius_rotation

end witt_vector
