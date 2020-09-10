/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.basic
import ring_theory.witt_vector.is_poly


/-! ## The Verschiebung operator -/

namespace witt_vector

variables {p : ℕ} {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

noncomputable theory
open mv_polynomial

variables (p)
include hp

def frobenius_poly_rat (n : ℕ) : mv_polynomial ℕ ℚ :=
bind₁ (witt_polynomial p ℚ ∘ λ n, n + 1) (X_in_terms_of_W p ℚ n)

lemma bind₁_frobenius_poly_rat_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly_rat p) (witt_polynomial p ℚ n) = (witt_polynomial p ℚ (n+1)) :=
begin
  delta frobenius_poly_rat,
  rw [← bind₁_bind₁, X_in_terms_of_W_prop₂, bind₁_X_right],
end

def frobenius_poly_aux (n : ℕ) : mv_polynomial ℕ ℤ :=
finsupp.map_range (λ r : ℚ, (r / p).num) (by { rw [zero_div], exact rat.coe_int_num 0 })
  (frobenius_poly_rat p n - (X n ^ p) : mv_polynomial ℕ ℚ)

def frobenius_poly (n : ℕ) : mv_polynomial ℕ ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0) (frobenius_poly_rat p n)

lemma map_frobenius_poly_aux (n : ℕ) :
  (C ↑p) * mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly_aux p n) + X n ^ p =
  frobenius_poly_rat p n :=
begin
  delta frobenius_poly_rat,
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  rw [X_in_terms_of_W_eq, alg_hom.map_mul, bind₁_C_right, alg_hom.map_sub, bind₁_X_right, alg_hom.map_sum],
  conv_rhs { congr, congr, skip, apply_congr, skip,
    rw [alg_hom.map_mul, alg_hom.map_pow, ← IH x (finset.mem_range.mp H)] },
  dsimp,
  rw [witt_polynomial_eq_sum_C_mul_X_pow, finset.sum_range_succ, finset.sum_range_succ],
  rw [nat.sub_self, nat.pow_zero],
  rw [sub_mul, mul_comm _ (C (⅟ ↑p ^ n)), mul_add, ← mul_assoc, ← C_mul, mul_add, ← mul_assoc, ← C_mul],
  rw [pow_add, ← mul_assoc, pow_one, pow_one],
  rw [← mul_pow, inv_of_mul_self, one_pow, one_mul, C_1, one_mul],
  rw [add_comm n, nat.add_sub_cancel, nat.pow_one, add_comm _ n],
  rw [add_left_comm, add_comm, ← add_sub, add_right_inj, ← add_sub],
end

lemma map_frobenius_poly (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  {  },
end

variables {p}

def frobenius_fun (x : 𝕎 R) : 𝕎 R :=
mk p $ λ n, (mv_polynomial.aeval (λ (k : ℕ), coeff k x)) (frobenius_poly p n)

lemma coeff_frobenius_fun (x : 𝕎 R) (n : ℕ) :
  coeff n (frobenius_fun x) = (mv_polynomial.aeval (λ (k : ℕ), coeff k x)) (frobenius_poly p n) :=
coeff_mk _ _ _

variables (p)

@[simps { fully_applied := ff }]
lemma frobenius_is_poly : is_poly p (λ R _Rcr, @frobenius_fun p R _ _Rcr) :=
{ poly := frobenius_poly p,
  coeff := by { introsI, apply coeff_frobenius_fun } }

lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1)) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial,
    map_witt_polynomial],
end

lemma frobenius_poly_zmod (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n) = X n ^ p :=
sorry

section char_p
variables [char_p R p]

-- move this
instance qwerty : algebra (zmod p) R :=
ring_hom.to_algebra (zmod.cast_hom (dvd_refl p) R)

@[simp]
lemma coeff_frobenius_fun_char_p (x : 𝕎 R) (n : ℕ) :
  coeff n (frobenius_fun x) = (x.coeff n) ^ p :=
begin
  rw [coeff_frobenius_fun],
  -- outline of the calculation, proofs follow below
  calc aeval (λ k, x.coeff k) (frobenius_poly p n)
      = aeval (λ k, x.coeff k) (mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n)) : _
  ... = aeval (λ k, x.coeff k) (X n ^ p : mv_polynomial ℕ (zmod p)) : _
  ... = (x.coeff n) ^ p : _,
  { conv_rhs { rw [aeval_eq_eval₂_hom, eval₂_hom_map_hom] },
    apply eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { rw frobenius_poly_zmod },
  { rw [alg_hom.map_pow, aeval_X] }
end

@[simp]
lemma frobenius_fun_zmodp (x : 𝕎 (zmod p)) :
  (frobenius_fun x) = x :=
by simp only [ext_iff, coeff_frobenius_fun_char_p, zmod.pow_card, eq_self_iff_true, forall_const]

end char_p

end witt_vector
