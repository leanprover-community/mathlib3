/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.is_poly

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mul_n_is_poly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace witt_vector

variables {p : ℕ} {R : Type*} [hp : fact p.prime] [comm_ring R]
local notation `𝕎` := witt_vector p -- type as `\bbW`

open mv_polynomial
noncomputable theory

include hp

variable (p)

/-- `witt_mul_n p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
noncomputable
def witt_mul_n : ℕ → ℕ → mv_polynomial ℕ ℤ
| 0     := 0
| (n+1) := λ k, bind₁ (function.uncurry $ ![(witt_mul_n n), X]) (witt_add p k)

variable {p}

lemma mul_n_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) :
  (x * n).coeff k = aeval x.coeff (witt_mul_n p n k) :=
begin
  induction n with n ih generalizing k,
  { simp only [nat.nat_zero_eq_zero, nat.cast_zero, mul_zero,
      zero_coeff, witt_mul_n, alg_hom.map_zero, pi.zero_apply], },
  { rw [witt_mul_n, nat.succ_eq_add_one, nat.cast_add, nat.cast_one, mul_add, mul_one,
      aeval_bind₁, add_coeff],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext1 ⟨b, i⟩,
    fin_cases b,
    { simp only [function.uncurry, matrix.cons_val_zero, ih] },
    { simp only [function.uncurry, matrix.cons_val_one, matrix.head_cons, aeval_X] } }
end

variables (p)

/-- Multiplication by `n` is a polynomial function. -/
@[is_poly] lemma mul_n_is_poly (n : ℕ) : is_poly p (λ R _Rcr x, by exactI x * n) :=
⟨⟨witt_mul_n p n, λ R _Rcr x, by { funext k, exactI mul_n_coeff n x k }⟩⟩

@[simp] lemma bind₁_witt_mul_n_witt_polynomial (n k : ℕ) :
  bind₁ (witt_mul_n p n) (witt_polynomial p ℤ k) = n * witt_polynomial p ℤ k :=
begin
  induction n with n ih,
  { simp only [witt_mul_n, nat.cast_zero, zero_mul, bind₁_zero_witt_polynomial] },
  { rw [witt_mul_n, ← bind₁_bind₁, witt_add, witt_structure_int_prop],
    simp only [alg_hom.map_add, nat.cast_succ, bind₁_X_right],
    rw [add_mul, one_mul, bind₁_rename, bind₁_rename],
    simp only [ih, function.uncurry, function.comp, bind₁_X_left, alg_hom.id_apply,
      matrix.cons_val_zero, matrix.head_cons, matrix.cons_val_one], }
end

end witt_vector
