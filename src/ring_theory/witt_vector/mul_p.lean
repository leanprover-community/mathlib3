/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.frobenius
import ring_theory.witt_vector.verschiebung

/-! ## Multiplication by `p` -/

namespace witt_vector

variables {p : ℕ} {R : Type*} [hp : fact p.prime] [comm_ring R]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial
noncomputable theory

include hp

variable (p)

noncomputable
def witt_mul_n : ℕ → ℕ → mv_polynomial ℕ ℤ
| 0     := λ k, 0
| (n+1) := λ k, bind₁ (function.uncurry $ ![(witt_mul_n n), X]) (witt_add p k)

variable {p}

lemma mul_n_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) :
  (x * n).coeff k = aeval (λ i, x.coeff i) (witt_mul_n p n k) :=
begin
  induction n with n ih generalizing k,
  { simp only [nat.nat_zero_eq_zero, nat.cast_zero, mul_zero,
      zero_coeff, witt_mul_n, alg_hom.map_zero], },
  { rw [witt_mul_n],
    simp only [nat.succ_eq_add_one, mul_add, mul_one, nat.cast_add, nat.cast_one],
    rw [aeval_bind₁, add_coeff],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext1 ⟨b, i⟩,
    fin_cases b;
    simp only [function.uncurry, ih, aeval_X,
      matrix.cons_val_zero, matrix.head_cons, matrix.cons_val_one], }
end

variables (p)

@[simps { fully_applied := ff }]
def mul_n_is_poly (n : ℕ) : is_poly p (λ R _Rcr x, by exactI x * n) :=
{ poly := witt_mul_n p n,
  coeff := λ k R _Rcr x, by exactI mul_n_coeff n x k }

lemma bind₁_witt_mul_n_witt_polynomial (n k : ℕ) :
  bind₁ (witt_mul_n p n) (witt_polynomial p ℤ k) = n * witt_polynomial p ℤ k :=
begin
  induction n with n ih,
  { -- we need `bind₁_zero_left` which is defeq to `aeval_zero`
    simp only [witt_mul_n, bind₁, aeval_zero', int.cast_zero, ring_hom.eq_int_cast, nat.cast_zero,
      zero_mul, constant_coeff_witt_polynomial], },
  { rw [witt_mul_n, ← bind₁_bind₁],
    erw [witt_structure_int_prop],
    simp only [alg_hom.map_add, nat.cast_succ, bind₁_X_right],
    rw [add_mul, one_mul],
    rw [bind₁_rename, bind₁_rename],
    simp only [ih, function.uncurry, function.comp, bind₁_X_left, alg_hom.id_apply,
      matrix.cons_val_zero, matrix.head_cons, matrix.cons_val_one], }
end

lemma frobenius_fun_comp_verschiebung :
  (frobenius_fun ∘ verschiebung : 𝕎 R → 𝕎 R) = λ x, x * p :=
begin
  have := is_poly.ext' ((frobenius_is_poly p).comp (verschiebung_is_poly p)) (mul_n_is_poly p p) _,
  { rw [function.funext_iff] at this,
    specialize this R,
    rw [function.funext_iff] at this,
    apply this, },
  intro n,
  rw [is_poly.comp_poly, ← bind₁_bind₁],
  rw [mul_n_is_poly_poly, frobenius_is_poly_poly],
  rw [bind₁_frobenius_poly_witt_polynomial],
  rw [bind₁_witt_mul_n_witt_polynomial],
  rw [verschiebung_is_poly_poly, bind₁_verschiebung_poly_witt_polynomial],
  refl,
end

lemma frobenius_fun_verschiebung (x : 𝕎 R) :
  frobenius_fun (verschiebung x) = x * p :=
congr_fun (frobenius_fun_comp_verschiebung p) x

lemma verschiebung_zmod (x : 𝕎 (zmod p)) :
  verschiebung x = x * p :=
begin
  rw [← frobenius_fun_verschiebung, frobenius_fun_zmodp],
end

-- this should be true not just for `char_p R p` but for general `nontrivial R`.
lemma coeff_p_pow [char_p R p] (i : ℕ) : (p ^ i : 𝕎 R).coeff i = 1 :=
begin
  induction i with i h,
  { simp only [one_coeff_zero, ne.def, pow_zero] },
  { rw [pow_succ', ← frobenius_fun_verschiebung, coeff_frobenius_fun_char_p,
        verschiebung_coeff_succ, h, one_pow], }
end

end witt_vector
