/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import ring_theory.polynomial.basic
import ring_theory.polynomial.symmetric
import data.fintype.card
import algebra.big_operators

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

open finset polynomial fintype

namespace mv_polynomial

variables {R : Type*} [comm_semiring R]
variables (σ : Type*) [fintype σ]

/-- A sum version of Vieta's formula. Viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
lemma prod_X_add_C_eq_sum_esymm :
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
lemma prod_X_add_C_eval (r : σ → R) : ∏ i : σ, (polynomial.C (r i) + polynomial.X) =
  ∑ i in range (card σ + 1), (∑ t in powerset_len i (univ : finset σ),
    ∏ i in t, polynomial.C (r i)) * polynomial.X ^ (card σ - i) :=
begin
  classical,
  have h := @prod_X_add_C_eq_sum_esymm _ _ σ _,
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
lemma prod_X_add_C_coeff (r : σ → R) (k : ℕ) (h : k ≤ card σ):
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
  simp only [prod_X_add_C_eval, ← esymm_to_sum, finset_sum_coeff, coeff_C_mul_X_pow, sum_ite, hk,
    sum_singleton, esymm, eval_sum, eval_prod, eval_X, add_zero, sum_const_zero],
end

end mv_polynomial

section xfr

variables {R : Type*} [comm_semiring R] [decidable_eq R]

-- TODO. use dot notation everywhere it's possible

lemma multiset.antidiagonal_powerset {α : Type*} [decidable_eq α] (s : multiset α) :
  s.antidiagonal =
      (multiset.map (λ (t : multiset α), ((t, s - t) : multiset α × multiset α)) s.powerset) :=
begin
  refine s.induction_on _ _,
  simp only [multiset.antidiagonal_zero, multiset.powerset_zero, zero_tsub,
    multiset.map_singleton],
  intros a s hs,
  rw [multiset.antidiagonal_cons, multiset.powerset_cons, multiset.map_add, hs, multiset.map_map],
  suffices : multiset.map (λ (x : multiset α), (x, a ::ₘ (s - x))) s.powerset
    = multiset.map (λ (t : multiset α), (t, a ::ₘ s - t)) s.powerset,
  { simpa only [_root_.prod_map, id.def, multiset.map_map, function.comp_app, multiset.sub_cons,
    multiset.erase_cons_head, add_left_inj], },
  rw multiset.map_congr (eq.refl _),
  intros _ h,
  rw prod.mk.inj_iff,
  split, refl,
  refine multiset.ext' _,
  intro _,
  rw [multiset.count_cons, multiset.count_sub, multiset.count_sub, multiset.count_cons],
  exact tsub_add_eq_add_tsub (multiset.count_le_of_le _ (multiset.mem_powerset.mp h)),
end

lemma multiset.count_nil_powerset {α : Type*} [decidable_eq (multiset α)] (s : multiset α) :
  multiset.count (0 : multiset α) s.powerset = 1 :=
begin
  refine s.induction_on _ _,
  simp only [multiset.powerset_zero, multiset.count_singleton_self],
  intros _ _ h,
  rw [multiset.powerset_cons, multiset.count_add, h],
  simp only [multiset.count_eq_zero_of_not_mem, multiset.mem_map, multiset.cons_ne_zero,
    and_false, exists_false, not_false_iff],
end

lemma multiset.powerset_len_eq_filter {α : Type*} [decidable_eq α] (s : multiset α) :
  ∀ k : ℕ, s.powerset_len k = multiset.filter (λ t, multiset.card t = k) s.powerset :=
begin
  refine s.induction _ _,
  intro k,
  cases k ; { refl, },
  intros _ s hk k,
  cases k,
  { rw [multiset.powerset_len_zero_left, multiset.powerset_cons, multiset.filter_add],
    rw (_ : multiset.filter (λ (t : multiset α), multiset.card t = 0) s.powerset = {0}),
    rw (_ : multiset.filter (λ (t : multiset α), multiset.card t = 0)
      (multiset.map (multiset.cons a) s.powerset) = 0),
    { rwa add_zero, },
    { rw multiset.filter_eq_nil,
      intros t ht,
      rw multiset.card_eq_zero,
      obtain ⟨r, hr⟩ := multiset.mem_map.mp ht,
      rw ←hr.right,
      exact multiset.cons_ne_zero, },
    { ext r,
      rw multiset.count_filter,
      by_cases (r = 0),
      { simp only [h, eq_self_iff_true, if_true, multiset.count_singleton_self,
         multiset.count_nil_powerset s, multiset.card_zero] },
      { simp only [h, if_false, multiset.count_eq_zero_of_not_mem, multiset.mem_singleton,
        not_false_iff, multiset.card_eq_zero], }}},
  { rw [multiset.powerset_len_cons, multiset.powerset_cons, multiset.filter_add],
    rw [hk k, hk k.succ, add_right_inj],
    rw [multiset.map_filter, multiset.map_congr],
    { congr, ext,
      simp only [function.comp_app, multiset.card_cons, add_left_inj 1], },
    { intros _ _, refl, }}
end

lemma multiset.powerset_sum_powerset_len {α : Type*} [decidable_eq α] (s : multiset α) :
  s.powerset = ∑ (k:ℕ) in finset.range (s.card+1), s.powerset_len k :=
begin
  rw ( _ : ∑ (k:ℕ) in finset.range (s.card+1), s.powerset_len k =
    ∑ (k:ℕ) in finset.range (s.card+1),  multiset.filter (λ t, t.card = k) s.powerset),
  swap,
  { rw finset.sum_congr, refl,
    intros k hk,
    exact multiset.powerset_len_eq_filter s k, },
  ext t,
  by_cases hts : t ≤ s,
  swap,
  { rw ( _ : multiset.count t s.powerset = 0),
    { rw [multiset.count_sum', finset.sum_eq_zero],
      simp only [hts, multiset.count_eq_zero_of_not_mem, multiset.mem_filter,
        multiset.mem_powerset, false_and, not_false_iff, eq_self_iff_true, implies_true_iff], },
    simp only [hts, multiset.count_eq_zero_of_not_mem, not_false_iff, multiset.mem_powerset], },
  { have : t.card ∈ range (s.card + 1),
    { rw finset.mem_range_succ_iff,
      exact multiset.card_le_of_le hts, },
    rw (finset.sum_erase_add (range (s.card + 1)) _ this).symm,
    rw multiset.count_add,
    rw ( _ :  multiset.count t (∑ (x : ℕ) in (range (s.card + 1)).erase t.card,
      multiset.filter (λ (t : multiset α), t.card = x) s.powerset) = 0),
    { rw ( _ : multiset.count t (multiset.filter (λ (r : multiset α), r.card = t.card) s.powerset)
      = multiset.count t s.powerset),
      { ring, },
      rw multiset.count_filter,
      simp only [eq_self_iff_true, if_true], },
    rw [multiset.count_sum', finset.sum_eq_zero],
    intros _ h₁,
    rw multiset.count_eq_zero,
    by_contra h₂,
    rw multiset.mem_filter at h₂,
    rw mem_erase at h₁,
    exact h₁.left.symm h₂.right },
end

lemma multiset.map_sum {α : Type*} {β : Type*} {ι : Type*} [decidable_eq ι]
  (s : finset ι) (f : α → β) (g : ι → multiset α) :
  ∑ (j : ι) in s, (multiset.map f (g j)) = (multiset.map f ∑ (j : ι) in s, g j) :=
begin
  refine s.induction_on _ _,
  simp only [finset.sum_empty, multiset.map_zero],
  intros _ _ h₁ h₂,
  simp only [h₁, h₂, sum_insert, not_false_iff, multiset.map_add],
end

def multiset.esymm (s : multiset R) (n : ℕ) : R := ((s.powerset_len n).map multiset.prod).sum

lemma multiset.prod_X_add_C_eq_sum_esymm (s : multiset R) :
  (s.map (λ r, polynomial.C r + polynomial.X)).prod = ∑ j in range (s.card + 1),
  (polynomial.C (multiset.esymm s j) * polynomial.X ^ (s.card - j)) :=
begin
  classical,
  rw [multiset.prod_map_add, multiset.antidiagonal_powerset, multiset.map_map,
     multiset.powerset_sum_powerset_len, ←multiset.map_sum, multiset.sum_sum],
  refine finset.sum_congr begin congr end (λ j hj, _),
  rw [function.comp, multiset.esymm, ←multiset.sum_hom', ←multiset.sum_map_mul_right],
  rw multiset.map_congr (eq.refl _),
  intros x hx,
  rw multiset.mem_powerset_len at hx,
  rw [multiset.map_const, multiset.prod_repeat, multiset.prod_hom'],
  simp only [hx, multiset.map_id', multiset.card_sub, multiset.mem_powerset_len],
end

end xfr
