/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hanting Zhang
-/
import ring_theory.polynomial.symmetric

/-!
# Vieta's Formula

The main result is `vieta.prod_X_add_C_eq_sum_esymm`, which shows that the product of linear terms
`λ + X i` is equal to a linear combination of the symmetric polynomials `mv_polynomial.esymm σ R j`.

## Implementation Notes:

We first take the viewpoint where the "roots" `X i` are variables. This means we work over
`polynomial (mv_polynomial σ R)`, which enables us to talk about linear combinations of
`mv_polynomial.esymm σ R j`. We then derive Vieta's formula in `polynomial R` by giving a
valuation from each `X i` to `r i`.

-/

universes u
open_locale big_operators

open finset polynomial

namespace vieta

variables {R : Type u} [comm_semiring R]
variables (σ : Type u) [fintype σ]

/-- Viewing `X i` as variables, the product of linear terms `λ + X i` is equal to
a linear combination of the symmetric polynomials `mv_polynomial.esymm σ R j`. -/
lemma prod_X_add_C_eq_sum_esymm :
  ∏ i : σ, (C (mv_polynomial.X i) + X) =
  ∑ j in range (fintype.card σ + 1), (C (mv_polynomial.esymm σ R j) * X ^ (fintype.card σ - j)) :=
begin
  classical,
  rw [prod_add, powerset_sum],
  refine sum_congr begin congr end (λ j hj, _),
  rw [mv_polynomial.esymm, C.map_sum, sum_mul],
  refine sum_congr rfl (λ t ht, _),
  have h : (univ \ t).card = fintype.card σ - j :=
  by { rw card_sdiff (mem_powerset_len.mp ht).1, congr, exact (mem_powerset_len.mp ht).2 },
  rw [(C : mv_polynomial σ R →+* polynomial (mv_polynomial σ R)).map_prod, prod_const, ← h],
  congr,
end

/-- The product of linear terms `X + r i` is equal to `∑ j in range (n + 1), e_j * X ^ (n - j)`,
where `e_j` is the `j`th symmetric polynomial of the constant terms `r i`. -/
lemma prod_X_add_C_eval {r : σ → R} : ∏ i : σ, (C (r i) + X) =
  ∑ i in range (fintype.card σ + 1),
    (∑ t in powerset_len i (univ : finset σ), ∏ i in t, C (r i)) * X ^ (fintype.card σ - i) :=
begin
  classical,
  have h := @prod_X_add_C_eq_sum_esymm _ _ σ _,
  apply_fun (map (mv_polynomial.eval r)) at h,
  rw [map_prod, map_sum] at h,
  convert h,
  funext,
  simp only [mv_polynomial.eval_X, map_add, map_C, map_X],
  funext,
  simp only [mv_polynomial.esymm, map_C, map_sum, C.map_sum, map_C, map_pow, map_X, map_mul],
  congr,
  funext,
  simp only [mv_polynomial.eval_prod, mv_polynomial.eval_X],
  rw (C : R →+* polynomial R).map_prod,
end

end vieta
