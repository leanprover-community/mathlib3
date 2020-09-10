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
def frobenius_poly (n : ℕ) : mv_polynomial ℕ ℤ :=
sorry

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
sorry

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
