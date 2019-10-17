/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial
import algebra.pi_instances
import algebra.geom_sum
import group_theory.order_of_element
import field_theory.finite.basic

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, K denotes a finite field with q elements.

## Main results

1. Let f be a multivariate polynomial in finitely many variables (X s, s : σ)
   such that the total degree of f is less than (q-1) * cardinality of σ.
   Then the evaluation of f on all points of `σ → K` (aka K^σ) sums to 0.
   (`sum_mv_polynomial_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions`).
   Let (f i) be a finite family of multivariate polynomials
   in finitely many variables (X s, s : σ) such that
   the sum of the total degrees of the f i is less than the cardinality of σ.
   Then the number of common solutions of the f i
   is divisible by the characteristic of K.

-/

universes u v

namespace finite_field
open mv_polynomial function finset

variables {K : Type*} [discrete_field K] [fintype K]
variables {σ : Type*} [fintype σ] [decidable_eq σ]

lemma sum_mv_polynomial_eq_zero (f : mv_polynomial σ K)
  (h : f.total_degree < (q - 1) * fintype.card σ) :
  univ.sum (λ x, f.eval x) = (0:K) :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  rcases char_p.exists K with ⟨p, _char_p⟩, resetI,
  rcases card K p with ⟨n, hp, hn⟩,
  simp only [eval, eval₂, finsupp.sum, id.def],
  rw [sum_comm, sum_eq_zero],
  intros d hd,
  rw [← mul_sum, mul_eq_zero], right,
  simp only [finsupp.prod],
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1,
  { contrapose! h,
    refine le_trans _ (finset.le_sup hd),
    have : univ.sum (λ s:σ, q-1) ≤ univ.sum (λ s, d s) := sum_le_sum (λ s _, h s),
    rw [sum_const, nat.smul_eq_mul, mul_comm, card_univ] at this,
    rwa [finsupp.sum, show d.support = univ, from _],
    rw eq_univ_iff_forall,
    intro i, rw [finsupp.mem_support_iff, ne.def, ← nat.le_zero_iff],
    push_neg, exact lt_of_lt_of_le hq (h _), },
  by_cases hd' : d.support = univ,
  { suffices claim : (univ.filter (λ (x : σ → K), ∀ j, j ≠ i → x j = 0)).sum (λ x, x i ^ d i) *
      (univ.filter (λ (x : σ → K), x i = 0)).sum
      (λ (x : σ → K), (univ \ finset.singleton i).prod (λ j, x j ^ d j)) = 0,
    { rw sum_mul_sum at claim,
      rw [← claim, hd'], symmetry,
      refine sum_bij (λ p _ j, if j = i then p.1 j else p.2 j) (λ _ _, mem_univ _) _ _ _,
      { rintros ⟨x,y⟩ hxy, rw [mem_product, mem_filter, mem_filter] at hxy,
        rw [← prod_sdiff (subset_univ (finset.singleton i)), prod_singleton, if_pos rfl, mul_comm],
        congr' 1, apply prod_congr rfl, intros j hj, rw [mem_sdiff, mem_singleton] at hj,
        rw if_neg hj.2, },
      { rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hx hy hxy, rw function.funext_iff at hxy, rw prod.mk.inj_iff,
        rw [mem_product, mem_filter, mem_filter] at hx hy,
        split; funext j; by_cases hj : j = i,
        { specialize hxy i, rw [if_pos rfl, if_pos rfl] at hxy, rwa hj },
        { simp only [true_and, mem_univ, ne.def] at hx hy, rw [hx.1 j hj, hy.1 j hj], },
        { dsimp at hx hy, rw [hj, hx.2.2, hy.2.2], },
        { specialize hxy j, rwa [if_neg hj, if_neg hj] at hxy }, },
      { intros x hx, refine ⟨⟨λ j, if j = i then x j else 0, λ j, if j = i then 0 else x j⟩, _, _⟩,
        { rw [mem_product, mem_filter, mem_filter],
          refine ⟨⟨mem_univ _, λ j hj, if_neg hj⟩, ⟨mem_univ _, _⟩⟩,
          simp only [if_true, if_pos rfl], },
        { funext j, split_ifs with hj; refl }, } },
    { rw mul_eq_zero, left,
      conv_rhs {rw ← sum_pow_lt_card_sub_one (d i) hi},
      refine sum_bij (λ x _, x i) (λ _ _, mem_univ _) (λ _ _, rfl) _ _,
      { intros x y hx hy H, rw mem_filter at hx hy,
        funext j, by_cases hj : j = i, {rwa hj},
        rw [hx.2 _ hj, hy.2 _ hj], },
      { intros a ha,
        refine ⟨λ j, if j = i then a else 0, _, (if_pos rfl).symm⟩,
        rw mem_filter,
        exact ⟨mem_univ _, λ j hj, dif_neg hj⟩ } } },
  { rw eq_univ_iff_forall at hd', push_neg at hd', rcases hd' with ⟨i₀, hi₀⟩,
    let stratified : finset (σ → K) := univ.bind (λ a : K, univ.filter (λ x, x i₀ = a)),
    suffices : stratified = univ,
    { rw [← this, sum_bind],
      { suffices aux : (λ (a : K), (univ.filter (λ (x : σ → K), x i₀ = a)).sum
            (λ (x : σ → K), finset.prod (d.support) (λ (j : σ), x j ^ d j))) =
          (λ (a : K), (univ.filter (λ (x : σ → K), x i₀ = 0)).sum
            (λ (x : σ → K), finset.prod (d.support) (λ (j : σ), x j ^ d j))),
        { simp [aux, add_monoid.smul_eq_mul, card_univ, cast_card_eq_zero], },
        funext a,
        refine sum_bij (λ x _ j, if j = i₀ then 0 else x j) _ _ _ _,
        { intros x hx, rw mem_filter at hx ⊢, exact ⟨mem_univ _, if_pos rfl⟩ },
        { intros x hx, apply prod_congr rfl, intros j hj, rw if_neg, rintro rfl, exact hi₀ hj },
        { intros x y hx hy hxy, rw mem_filter at hx hy, rw function.funext_iff at hxy ⊢,
          intros j, specialize hxy j,
          by_cases hj : j = i₀, { rw [hj, hx.2, hy.2] }, { rwa [if_neg hj, if_neg hj] at hxy } },
        { intros x hx, refine ⟨λ j, if j = i₀ then a else x j, _, _⟩,
          { rw mem_filter at hx ⊢, exact ⟨mem_univ _, if_pos rfl⟩ },
          { funext j, split_ifs with hj, { rw mem_filter at hx, rw [hj, hx.2] }, { refl } } } },
      { intros x hx y hy hxy, rw disjoint_iff, contrapose! hxy,
        rcases exists_mem_of_ne_empty hxy with ⟨z, hz⟩,
        rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hz,
        rcases hz with ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, refl } },
    { rw eq_univ_iff_forall, intro x, rw mem_bind,
      refine ⟨x i₀, mem_univ _, _⟩, rw mem_filter, exact ⟨mem_univ _, rfl⟩ } },
end

/-- The Chevalley–Warning theorem.
   Let (f i) be a finite family of multivariate polynomials
   in finitely many variables (X s, s : σ)
   over a finite field of characteristic p.
   Assume that the sum of the total degrees of the f i is less than the cardinality of σ.
   Then the number of common solutions of the f i is divisible by p. -/
theorem char_dvd_card_solutions (p : nat.primes) [char_p K p]
  {ι : Type*} [decidable_eq ι] (s : finset ι) (f : ι → (mv_polynomial σ K))
  (h : (s.sum $ λ i, (f i).total_degree) < fintype.card σ) :
  (p:ℕ) ∣ fintype.card {x : σ → K // ∀ i ∈ s, (f i).eval x = 0} :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  let F : mv_polynomial σ K := s.prod (λ i, (1 - (f i)^(q-1))),
  suffices : univ.sum (λ x, F.eval x) =
    fintype.card {x : σ → K // ∀ i ∈ s, (f i).eval x = 0},
  { rw [← char_p.cast_eq_zero_iff K, ← this],
    apply sum_mv_polynomial_eq_zero,
    calc F.total_degree ≤ s.sum (λ i, (1 - (f i)^(q-1)).total_degree) :
      total_degree_finset_prod s _
      ... ≤ s.sum (λ i, (q - 1) * (f i).total_degree) :
      begin
        apply sum_le_sum,
        intros i hi,
        refine le_trans (total_degree_sub _ _)
          (le_trans _ (total_degree_pow _ _)),
        simp only [max_eq_right, nat.zero_le, total_degree_one]
      end
      ... = (q - 1) * (s.sum $ λ i, (f i).total_degree) : mul_sum.symm
      ... < (q - 1) * (fintype.card σ) : by rwa mul_lt_mul_left hq },
  { let S : finset (σ → K) := univ.filter (λ x : σ → K, ∀ i ∈ s, (f i).eval x = 0),
    rw [fintype.card_of_subtype S, card_eq_sum_ones, nat_cast_sum, nat.cast_one,
     ← fintype.sum_extend_by_zero S],
    { apply sum_congr rfl,
      intros x hx, clear hx,
      rw show F.eval x = finset.prod s (λ (i : ι), (1 - f i ^ (q - 1)).eval x),
      { convert eval₂_prod _ _ _ _, exact is_semiring_hom.id },
      split_ifs with hx hx,
      { rw finset.prod_eq_one, intros i hi,
        rw mem_filter at hx,
        simp only [hx.right i hi, add_right_eq_self, neg_eq_zero, sub_eq_add_neg,
          eval_add, eval_pow, eval_one, eval_neg],
        exact zero_pow hq },
      { rw mem_filter at hx, push_neg at hx, simp only [false_or, mem_univ, not_true] at hx,
        rcases hx with ⟨i, hi, hx⟩,
        rw finset.prod_eq_zero hi,
        simp only [pow_card_sub_one_eq_one (eval x (f i)) hx, add_right_neg, sub_eq_add_neg,
          eval_add, eval_pow, eval_one, eval_neg], } },
    { intros x, simp only [mem_filter, mem_univ, true_and] } }
end

end finite_field
