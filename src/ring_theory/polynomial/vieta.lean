/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import ring_theory.polynomial.basic
import ring_theory.polynomial.symmetric

/-!
# Vieta's Formula

The main result is `vieta.prod_X_add_C_eq_sum_esymm`, which shows that the product of linear terms
`λ + X i` is equal to a linear combination of the symmetric polynomials `esymm σ R j`.

## Implementation Notes:

We first take the viewpoint where the "roots" `X i` are variables. This means we work over
`polynomial (mv_polynomial σ R)`, which enables us to talk about linear combinations of
`esymm σ R j`. We then derive Vieta's formula in `polynomial R` by giving a
valuation from each `X i` to `r i`.

-/

open_locale big_operators polynomial

variables {R : Type*} [comm_semiring R]

namespace multiset

lemma sum_powerset_len {α : Type*} (S : multiset α) :
  S.powerset = ∑ k in finset.range(S.card + 1), (S.powerset_len k) :=
begin
  apply eq.symm,
  apply multiset.eq_of_le_of_card_le,
  { apply multiset.le_of_disjoint_sum_le,
    { exact λ _ _, multiset.powerset_len_le_powerset _ _, },
    { intros _ _ _ _ hxny _ htx hty,
      rw multiset.mem_powerset_len at htx,
      rw multiset.mem_powerset_len at hty,
      rw ←htx.right at hxny,
      rw hty.right at hxny,
      exact ne.irrefl hxny, }},
  { rw multiset.card_powerset,
    rw ( _ : card (∑ (k : ℕ) in finset.range (card S + 1), powerset_len k S)
      = ∑ (k : ℕ) in finset.range (card S + 1), card (powerset_len k S)),
    { conv_rhs { congr, skip, funext, rw multiset.card_powerset_len },
      apply eq.le,
      exact (nat.sum_range_choose S.card).symm, },
    exact map_sum card (λ (k : ℕ), multiset.powerset_len k S) (finset.range (S.card + 1))},
end

/-- A sum version of Vieta's formula for `multiset`: the product of the linear terms `X + λ` where
`λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s .-/
lemma prod_X_add_C_eq_sum_esymm (s : multiset R) :
  (s.map (λ r, polynomial.X + polynomial.C r)).prod =
  ∑ j in finset.range (s.card + 1), (polynomial.C (s.esymm j) * polynomial.X ^ (s.card - j)) :=
begin
  classical,
  rw [prod_map_add, antidiagonal_powerset, map_map, sum_powerset_len, function.comp,
    finset.sum_eq_multiset_sum, finset.sum_eq_multiset_sum, ←join, ←bind, map_bind, sum_bind],
  rw map_congr (eq.refl _),
  intros _ _,
  rw [esymm, ←sum_hom', ←sum_map_mul_right, map_congr (eq.refl _)],
  intros _ ht,
  rw mem_powerset_len at ht,
  simp [ht, map_const, prod_repeat, prod_hom', map_id', card_sub],
end

/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
lemma prod_X_add_C_coeff (s : multiset R) (k : ℕ) (h : k ≤ card s):
  polynomial.coeff (s.map (λ r, polynomial.X + polynomial.C r)).prod k =
    s.esymm (s.card - k) :=
begin
  have hk : multiset.filter (λ (x : ℕ), k = card s - x) (range (card s + 1)) = {card s - k} :=
  begin
    sorry ; { refine multiset.ext _ _ _,
    -- (λ a, ⟨λ ha, _, λ ha, _ ⟩),
    rw mem_singleton,
    have hσ := (tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp
      (mem_filter.mp ha).1)).mp ((mem_filter.mp ha).2).symm,
    symmetry,
    rwa [(tsub_eq_iff_eq_add_of_le h), add_comm],
    rw mem_filter,
    have haσ : a ∈ range (card σ + 1) :=
    by { rw mem_singleton.mp ha, exact mem_range_succ_iff.mpr (@tsub_le_self _ _ _ _ _ k) },
    refine ⟨haσ, eq.symm _⟩,
    rw tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp haσ),
     have hσ := (tsub_eq_iff_eq_add_of_le h).mp (mem_singleton.mp ha).symm,
     rwa add_comm, },
  end,
  simp [prod_X_add_C_eq_sum_esymm, esymm, polynomial.finset_sum_coeff,
    polynomial.coeff_C_mul_X_pow, finset.sum_ite, hk, sum_singleton, esymm, polynomial.eval_sum,
    polynomial.eval_prod, polynomial.eval_X, add_zero, finset.sum_const_zero] at *,
  sorry,
end

end multiset

namespace mv_polynomial

open finset polynomial fintype

variables (σ : Type*) [fintype σ]

/-- A sum version of Vieta's formula for `mv_polynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
lemma prod_C_add_X_eq_sum_esymm :
  (∏ i : σ, (polynomial.C (X i) + polynomial.X) : polynomial (mv_polynomial σ R) )=
  ∑ j in range (card σ + 1),
    (polynomial.C (esymm σ R j) * polynomial.X ^ (card σ - j)) :=
begin
  classical,
  rw [prod_add, sum_powerset],
  refine sum_congr begin congr end (λ j hj, _),
  rw [esymm, map_sum, sum_mul],
  refine sum_congr rfl (λ t ht, _),
  have h : (univ \ t).card = card σ - j :=
  by { rw card_sdiff (mem_powerset_len.mp ht).1, congr, exact (mem_powerset_len.mp ht).2 },
  rw [map_prod, prod_const, ← h],
end

end mv_polynomial
