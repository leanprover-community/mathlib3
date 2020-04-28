/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial
import algebra.pi_instances
import field_theory.finite

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, `K` denotes a finite field with `q` elements.

## Main results

1. Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
   such that the total degree of `f` is less than `(q-1)` times the cardinality of `σ`.
   Then the evaluation of `f` on all points of `σ → K` (aka `K^σ`) sums to `0`.
   (`sum_mv_polynomial_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions`).
   Let `f i` be a finite family of multivariate polynomials
   in finitely many variables (`X s`, `s : σ`) such that
   the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
   Then the number of common solutions of the `f i`
   is divisible by the characteristic of `K`.

-/

universes u v

namespace finite_field
open mv_polynomial function finset

variables {K : Type*} {σ : Type*} [fintype K] [field K] [fintype σ]
local notation `q` := fintype.card K

lemma exists_degree_lt_card_sub_one (f : mv_polynomial σ K)
  (h : f.total_degree < (q - 1) * fintype.card σ) (d : σ →₀ ℕ) (hd : d ∈ f.support) :
  ∃ i, d i < q - 1 :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  contrapose! h,
  refine le_trans _ (finset.le_sup hd),
  have : univ.sum (λ s:σ, q-1) ≤ univ.sum (λ s, d s) := sum_le_sum (λ s _, h s),
  rw [sum_const, nat.smul_eq_mul, mul_comm, card_univ] at this,
  rwa [finsupp.sum, show d.support = univ, from _],
  rw eq_univ_iff_forall,
  intro i, rw [finsupp.mem_support_iff, ← nat.pos_iff_ne_zero],
  exact lt_of_lt_of_le hq (h _),
end

lemma sum_mv_polynomial_eq_zero [decidable_eq σ] (f : mv_polynomial σ K)
  (h : f.total_degree < (q - 1) * fintype.card σ) :
  univ.sum (λ x, f.eval x) = (0:K) :=
begin
  simp only [eval, eval₂, finsupp.sum, id.def],
  rw [sum_comm, sum_eq_zero],
  intros d hd,
  rw [← mul_sum, mul_eq_zero], right,
  simp only [finsupp.prod],
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1, from exists_degree_lt_card_sub_one f h d hd,
  haveI : decidable_eq K := classical.dec_eq K,
  let S : finset (σ → K) := univ.filter (λ x, x i = 0),
  let stratified : finset (σ → K) := S.bind (λ x, univ.filter (λ y, ∀ j ≠ i, y j = x j)),
  have : stratified = univ,
  { simp only [eq_univ_iff_forall, mem_bind, true_and, exists_prop, mem_filter, mem_univ, ne.def],
    intro x,
    refine ⟨function.update x i 0, function.update_same _ _ _, _⟩,
    intros j hj, exact (function.update_noteq hj _ _).symm },
  rw [← this, sum_bind],
  swap,
  { rintros x hx y hy hxy z hz,
    apply hxy,
    funext j,
    by_cases hj : j = i,
    { subst j, rw mem_filter at hx hy, rw [hx.2, hy.2] },
    { simp only [true_and, mem_filter, mem_univ, inf_eq_inter, ne.def, mem_inter] at hz,
      cases hz with hzx hzy,
      rw [← hzx j hj, ← hzy j hj] } },
  rw sum_eq_zero,
  intros x hx,
  let T := d.support \ finset.singleton i,
  let c := T.prod (λ j, x j ^ d j),
  refine calc _ = univ.sum (λ a : K, c * a ^ d i) : _
            ... = c * univ.sum (λ a : K, a ^ d i) : by rw mul_sum
            ... = 0 : by rw [sum_pow_lt_card_sub_one _ hi, mul_zero],
  symmetry,
  apply sum_bij (λ a ha, function.update x i a),
  { intros a ha, simp only [true_and, mem_filter, mem_univ, ne.def],
    intros j hj, apply function.update_noteq hj },
  { intros a ha,
    by_cases hi : i ∈ d.support,
    { rw ← singleton_subset_iff at hi,
      show c * a ^ d i = d.support.prod (λ (j : σ), update x i a j ^ d j),
      rw [← prod_sdiff hi, prod_singleton, function.update_same],
      congr' 1,
      apply prod_congr rfl,
      simp only [and_imp, mem_sdiff, finsupp.mem_support_iff, ne.def, mem_singleton],
      intros j hdj hj,
      rw function.update_noteq hj, },
    { have hT : T = d.support,
      { apply sdiff_eq_self_of_disjoint, rwa ← disjoint_singleton at hi, },
      rw finsupp.not_mem_support_iff at hi,
      simp only [hi, mul_one, pow_zero, c, hT],
      apply prod_congr rfl,
      intros j hj,
      rw function.update_noteq,
      rintro rfl,
      rw finsupp.mem_support_iff at hj,
      contradiction } },
  { intros a b ha hb H,
    simpa only [function.update_same] using congr_fun H i, },
  { intros y hy, refine ⟨y i, mem_univ _, _⟩,
    funext j,
    by_cases hj : j = i,
    { subst j, exact (function.update_same i (y i) x).symm },
    { simp only [true_and, mem_filter, mem_univ, ne.def] at hy,
      simpa only [hy j hj] using (function.update_noteq hj (y i) x).symm, } },
end

variables [decidable_eq K] [decidable_eq σ]

/-- The Chevalley–Warning theorem.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
theorem char_dvd_card_solutions_family (p : ℕ) [char_p K p]
  {ι : Type*} (s : finset ι) (f : ι → (mv_polynomial σ K))
  (h : (s.sum $ λ i, (f i).total_degree) < fintype.card σ) :
  (p:ℕ) ∣ fintype.card {x : σ → K // ∀ i ∈ s, (f i).eval x = 0} :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  let F : mv_polynomial σ K := s.prod (λ i, (1 - (f i)^(q-1))),
  suffices : univ.sum (λ x, F.eval x) = fintype.card {x : σ → K // ∀ i ∈ s, (f i).eval x = 0},
  { rw [← char_p.cast_eq_zero_iff K, ← this],
    apply sum_mv_polynomial_eq_zero,
    calc F.total_degree ≤ s.sum (λ i, (1 - (f i)^(q-1)).total_degree) : total_degree_finset_prod s _
      ... ≤ s.sum (λ i, (q - 1) * (f i).total_degree) :
      begin
        apply sum_le_sum,
        intros i hi,
        refine le_trans (total_degree_sub _ _) (le_trans _ (total_degree_pow _ _)),
        simp only [max_eq_right, nat.zero_le, total_degree_one]
      end
      ... = (q - 1) * (s.sum $ λ i, (f i).total_degree) : mul_sum.symm
      ... < (q - 1) * (fintype.card σ) : by rwa mul_lt_mul_left hq },
  { let S : finset (σ → K) := univ.filter (λ x : σ → K, ∀ i ∈ s, (f i).eval x = 0),
    have hS : ∀ (x : σ → K), x ∈ S ↔ ∀ (i : ι), i ∈ s → eval x (f i) = 0,
    { intros x, simp only [mem_filter, mem_univ, true_and], },
    rw [fintype.card_of_subtype S hS, card_eq_sum_ones, sum_nat_cast, nat.cast_one,
        ← fintype.sum_extend_by_zero S],
    apply sum_congr rfl,
    intros x hx, clear hx,
    rw show F.eval x = finset.prod s (λ (i : ι), (1 - f i ^ (q - 1)).eval x),
    { convert eval₂_prod id _ _ _, exact is_semiring_hom.id },
    simp only [eval_sub, eval_pow, eval_one],
    split_ifs with hx hx,
    { rw finset.prod_eq_one,
      intros i hi,
      rw mem_filter at hx,
      simp only [hx.right i hi, add_right_eq_self, neg_eq_zero, zero_pow hq, sub_zero], },
    { obtain ⟨i, hi, hx⟩ : ∃ (i : ι), i ∈ s ∧ ¬eval x (f i) = 0,
      { simpa only [mem_filter, true_and, classical.not_forall, mem_univ, classical.not_imp] using hx },
      rw finset.prod_eq_zero hi,
      simp only [pow_card_sub_one_eq_one (eval x (f i)) hx, add_right_neg, sub_self], } }
end


/-- The Chevalley–Warning theorem.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_family` for a version that takes a family of polynomials `f i`. -/
theorem char_dvd_card_solutions (p : ℕ) [char_p K p]
  (f : mv_polynomial σ K) (h : f.total_degree < fintype.card σ) :
  (p:ℕ) ∣ fintype.card {x : σ → K // f.eval x = 0} :=
begin
  let F : unit → mv_polynomial σ K := λ _, f,
  convert char_dvd_card_solutions_family p univ F _ using 1,
  { apply fintype.card_congr,
    apply equiv.subtype_congr_right,
    simp only [fintype.univ_punit, iff_self, forall_eq, singleton_eq_singleton,
      mem_singleton, forall_true_iff], },
  { simpa only [fintype.univ_punit, singleton_eq_singleton, sum_singleton] using h, }
end

end finite_field
