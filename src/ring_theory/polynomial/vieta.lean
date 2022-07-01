/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import ring_theory.polynomial.basic
import ring_theory.polynomial.symmetric

/-!
# Vieta's Formula

The main result is `polynomial.prod_X_add_C_eq_sum_esymm`, which shows that the product of linear
terms `λ + X i` is equal to a linear combination of the symmetric polynomials `esymm σ R j`.

## Implementation Notes:

We first take the viewpoint where the "roots" `X i` are variables. This means we work over
`polynomial (mv_polynomial σ R)`, which enables us to talk about linear combinations of
`esymm σ R j`. We then derive Vieta's formula in `polynomial R` by giving a
valuation from each `X i` to `r i`. Finally, for `R` be an integral domain (so that `p.roots`
is defined for any `p : R[X]` as a multiset), we derive the relationship between the coefficients
and the roots of `p` for a polynomial `p` that splits (i.e. having as many roots as its degree).

-/

open_locale big_operators polynomial

open finset fintype

variables {R : Type*} [comm_semiring R]
variables (σ : Type*) [fintype σ]

namespace mv_polynomial

lemma esymm_to_sum (r : σ → R) (j : ℕ) : polynomial.C (eval r (esymm σ R j)) =
  ∑ t in powerset_len j (univ : finset σ), ∏ i in t, polynomial.C (r i) :=
by simp only [esymm, eval_sum, eval_prod, eval_X, map_sum, map_prod]

end mv_polynomial

namespace polynomial

/-- A sum version of Vieta's formula. Viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
lemma prod_C_add_X_eq_sum_esymm :
  (∏ i : σ, (C (mv_polynomial.X i) + X) : (mv_polynomial σ R)[X]) =
  ∑ j in range (card σ + 1), C (mv_polynomial.esymm σ R j) * X ^ (card σ - j) :=
begin
  classical,
  rw [prod_add, sum_powerset],
  refine sum_congr begin congr end (λ j hj, _),
  rw [mv_polynomial.esymm, map_sum, sum_mul],
  refine sum_congr rfl (λ t ht, _),
  have h : (univ \ t).card = card σ - j :=
  by { rw card_sdiff (mem_powerset_len.mp ht).1, congr, exact (mem_powerset_len.mp ht).2 },
  rw [map_prod, prod_const, ← h],
end

/-- A fully expanded sum version of Vieta's formula, evaluated at the roots.
The product of linear terms `X + r i` is equal to `∑ j in range (n + 1), e_j * X ^ (n - j)`,
where `e_j` is the `j`th symmetric polynomial of the constant terms `r i`. -/
lemma prod_C_add_X_eval (r : σ → R) : ∏ i : σ, (C (r i) + X) =
  ∑ i in range (card σ + 1), (∑ t in powerset_len i (univ : finset σ), ∏ i in t, C (r i)) *
  X ^ (card σ - i) :=
begin
  classical,
  have h := @prod_C_add_X_eq_sum_esymm _ _ σ _,
  apply_fun (map (mv_polynomial.eval r)) at h,
  rw [polynomial.map_prod, polynomial.map_sum] at h,
  convert h,
  simp only [mv_polynomial.eval_X, polynomial.map_add, map_C, map_X, eq_self_iff_true],
  funext,
  simp only [function.funext_iff, mv_polynomial.esymm, map_C, polynomial.map_sum, map_sum,
    map_C, polynomial.map_pow, map_X, polynomial.map_mul],
  congr,
  funext,
  simp only [eval_prod, mv_polynomial.eval_X, map_prod],
end

/-- Vieta's formula for the coefficients of the product of linear terms `X + r i`,
The `k`th coefficient is `∑ t in powerset_len (card σ - k) (univ : finset σ), ∏ i in t, r i`,
i.e. the symmetric polynomial `esymm σ R (card σ - k)` of the constant terms `r i`. -/
lemma prod_C_add_X_coeff (r : σ → R) (k : ℕ) (h : k ≤ card σ) :
  (∏ i : σ, (C (r i) + X)).coeff k =
  ∑ t in powerset_len (card σ - k) (univ : finset σ), ∏ i in t, r i :=
begin
  have hk : filter (λ (x : ℕ), k = card σ - x) (range (card σ + 1)) = {card σ - k},
  { refine finset.ext (λ a, ⟨λ ha, _, λ ha, _ ⟩),
    rw mem_singleton,
    have hσ := (tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp
      (mem_filter.mp ha).1)).mp (mem_filter.mp ha).2.symm,
    symmetry,
    rwa [tsub_eq_iff_eq_add_of_le h, add_comm],
    rw mem_filter,
    have haσ : a ∈ range (card σ + 1) :=
    by { rw mem_singleton.mp ha, exact mem_range_succ_iff.mpr (@tsub_le_self _ _ _ _ _ k) },
    refine ⟨haσ, eq.symm _⟩,
    rw tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp haσ),
    have hσ := (tsub_eq_iff_eq_add_of_le h).mp (mem_singleton.mp ha).symm,
    rwa add_comm },
  simp only [prod_C_add_X_eval, ← mv_polynomial.esymm_to_sum, finset_sum_coeff, coeff_C_mul_X_pow,
    sum_ite, hk, sum_singleton, mv_polynomial.esymm, mv_polynomial.eval_sum,
    mv_polynomial.eval_prod, mv_polynomial.eval_X, add_zero, sum_const_zero],
end

lemma _root_.multiset.prod_C_add_X_coeff (s : multiset R) (k : ℕ) (h : k ≤ s.card) :
  (s.map (λ r, C r + X)).prod.coeff k =
  ((s.powerset_len (s.card - k)).map multiset.prod).sum :=
begin
  rw ← s.map_enum_of_fin_card s.coe_to_list,
  rw [multiset.map_map, ← prod_eq_multiset_prod, prod_C_add_X_coeff],
  swap, { exact h.trans (fintype.card_fin _).ge },
  rw [multiset.powerset_len_map, ← map_val_val_powerset_len],
  rw [sum_eq_multiset_sum, multiset.map_map, multiset.map_map, multiset.card_map],
  refl,
end

lemma _root_.multiset.prod_X_sub_C_coeff {R} [comm_ring R] (s : multiset R) (k : ℕ)
  (h : k ≤ s.card) : (s.map (λ r, X - C r)).prod.coeff k =
  (-1) ^ (s.card - k) * ((s.powerset_len (s.card - k)).map multiset.prod).sum :=
begin
  convert (s.map (λ x, -x)).prod_C_add_X_coeff k _ using 2,
  { rw multiset.map_map, congr, ext1, rw [sub_eq_add_neg, ← C_neg, add_comm] },
  all_goals { rw multiset.card_map }, swap, { exact h },
  { rw [← multiset.sum_map_mul_left, multiset.powerset_len_map, multiset.map_map],
    congr' 1, apply multiset.map_congr rfl,
    intros x hx, convert ← x.prod_map_neg.symm, exact (multiset.mem_powerset_len.1 hx).2 },
end

/-- Vieta's formula for the coefficients and the roots of a split polynomial.
  When `R` is a field, use `polynomial.splits_iff_card_roots` to derive the
  condition `hroots` from `p.splits (ring_hom.id R)`.  -/
theorem vieta {R} [comm_ring R] [is_domain R] (p : R[X])
  (hroots : p.roots.card = p.nat_degree) (k : ℕ) (h : k ≤ p.nat_degree) :
  p.coeff k = p.leading_coeff * (-1) ^ (p.nat_degree - k) *
    ((p.roots.powerset_len (p.nat_degree - k)).map multiset.prod).sum :=
begin
  conv_lhs { rw ← C_leading_coeff_mul_prod_multiset_X_sub_C hroots },
  rw [coeff_C_mul, mul_assoc], congr,
  convert p.roots.prod_X_sub_C_coeff k _ using 3; rw hroots, exact h,
end

end polynomial
