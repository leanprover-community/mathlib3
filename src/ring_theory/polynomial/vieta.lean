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

lemma disjoint_of_disjoint_sum {α β : Type*} {i : finset β} {f : β → multiset α} {z : β}
  (h1 : z ∉ i) (h2 : ∀ x ∈ i, multiset.disjoint (f x) (f z)) :
  multiset.disjoint (f z) (∑ x in i, f x) :=
begin
  classical,
  apply finset.sum_induction f (λ (t : multiset α), disjoint (f z) t),
  { exact λ _ _ ha hb, disjoint_add_right.mpr ⟨ha, hb⟩ },
  { exact (zero_disjoint (f z)).symm},
  { exact λ x hx, (h2 x hx).symm },
end

lemma le_of_disjoint_sum_le {α β : Type*} {T : multiset α} {i : finset β} {f : β → multiset α}
  (h1 : ∀ x ∈ i, f x ≤ T) (h2 : ∀ x y ∈ i, x ≠ y → multiset.disjoint (f x) (f y)) :
  ∑ x in i, f x ≤ T :=
begin
  classical,
  induction i using finset.induction_on with z i hz hr,
  { simp only [finset.sum_empty, zero_le], },
  rw finset.sum_insert hz,
  have hdsj : disjoint (f z) (∑ x in i, f x),
  { refine disjoint_of_disjoint_sum hz _,
    intros x hx,
    have hxi : x ∈ insert z i, from finset.mem_insert_of_mem hx,
    have hzi : z ∈ insert z i, from finset.mem_insert_self z i,
    have hxz : x ≠ z,
    { contrapose! hz,
      rwa hz at hx, },
    exact ((h2 x hxi) z hzi) hxz,  },
  rw add_eq_union_iff_disjoint.mpr hdsj,
  rw union_le_iff,
  split,
  { exact h1 z (finset.mem_insert_self z i), },
  { apply hr,
    { intros x hx,
      have hxi : x ∈ insert z i, from finset.mem_insert_of_mem hx,
      exact h1 x hxi, },
    { intros x hx y hy,
      have hxi : x ∈ insert z i, from finset.mem_insert_of_mem hx,
      have hyi : y ∈ insert z i, from finset.mem_insert_of_mem hy,
      exact (h2 x hxi) y hyi, }},
end

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

end multiset

namespace mv_polynomial

open finset polynomial fintype

variables (σ : Type*) [fintype σ]

/-- A sum version of Vieta's formula. Viewing `X i` as variables,
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

/-- A fully expanded sum version of Vieta's formula, evaluated at the roots.
The product of linear terms `X + r i` is equal to `∑ j in range (n + 1), e_j * X ^ (n - j)`,
where `e_j` is the `j`th symmetric polynomial of the constant terms `r i`. -/
lemma prod_C_add_X_eval (r : σ → R) : ∏ i : σ, (polynomial.C (r i) + polynomial.X) =
  ∑ i in range (card σ + 1), (∑ t in powerset_len i (univ : finset σ),
    ∏ i in t, polynomial.C (r i)) * polynomial.X ^ (card σ - i) :=
begin
  classical,
  have h := @prod_C_add_X_eq_sum_esymm _ _ σ _,
  apply_fun (polynomial.map (eval r)) at h,
  rw [polynomial.map_prod, polynomial.map_sum] at h,
  convert h,
  simp only [eval_X, polynomial.map_add, polynomial.map_C, polynomial.map_X, eq_self_iff_true],
  funext,
  simp only [function.funext_iff, esymm, polynomial.map_C, polynomial.map_sum, map_sum,
    polynomial.map_C, polynomial.map_pow, polynomial.map_X, polynomial.map_mul],
  congr,
  funext,
  simp only [eval_prod, eval_X, map_prod],
end

lemma esymm_to_sum (r : σ → R) (j : ℕ) : polynomial.C (eval r (esymm σ R j)) =
  ∑ t in powerset_len j (univ : finset σ), ∏ i in t, polynomial.C (r i) :=
by simp only [esymm, eval_sum, eval_prod, eval_X, map_sum, map_prod]

/-- Vieta's formula for the coefficients of the product of linear terms `X + r i`,
The `k`th coefficient is `∑ t in powerset_len (card σ - k) (univ : finset σ), ∏ i in t, r i`,
i.e. the symmetric polynomial `esymm σ R (card σ - k)` of the constant terms `r i`. -/
lemma prod_C_add_X_coeff (r : σ → R) (k : ℕ) (h : k ≤ card σ):
  polynomial.coeff (∏ i : σ, (polynomial.C (r i) + polynomial.X)) k =
  ∑ t in powerset_len (card σ - k) (univ : finset σ), ∏ i in t, r i :=
begin
  have hk : filter (λ (x : ℕ), k = card σ - x) (range (card σ + 1)) = {card σ - k} :=
  begin
    refine finset.ext (λ a, ⟨λ ha, _, λ ha, _ ⟩),
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
    rwa add_comm,
  end,
  simp only [prod_C_add_X_eval, ← esymm_to_sum, finset_sum_coeff, coeff_C_mul_X_pow, sum_ite, hk,
    sum_singleton, esymm, eval_sum, eval_prod, eval_X, add_zero, sum_const_zero],
end

end mv_polynomial
