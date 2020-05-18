/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial
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

open_locale big_operators

section

instance subtype.unique {α : Type*} (a : α) : unique {x // x = a} :=
{ default := ⟨a, rfl⟩,
  uniq := λ ⟨x, h⟩, subtype.val_injective h }

instance subtype.not_not_unique {α : Type*} (p : α → Prop) [decidable_pred p] [unique {x // p x}] :
  unique {x // ¬ ¬ p x} :=
(equiv.subtype_congr_right $ λ a, not_not).unique_of_equiv ‹_›

end

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
  (∑ x, f.eval x) = 0 :=
begin
  haveI : decidable_eq K := classical.dec_eq K,
  calc (∑ x, f.eval x) = ∑ x : σ → K, ∑ d in f.support, f.coeff d * ∏ i, x i ^ d i : _
                   ... = ∑ d in f.support, ∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i : sum_comm
                   ... = 0 : sum_eq_zero _,
  { simp only [eval, eval₂, finsupp.sum, id.def, finsupp.prod_pow], refl, },

  intros d hd,
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1, from exists_degree_lt_card_sub_one f h d hd,
  let cd : K := f.coeff d,
  calc (∑ x : σ → K, cd * ∏ i, x i ^ d i) = cd * (∑ x : σ → K, ∏ i, x i ^ d i) : mul_sum.symm
                                      ... = 0 : (mul_eq_zero.mpr ∘ or.inr) _,

  calc (∑ x : σ → K, ∏ i, x i ^ d i) =
          ∑ (x₀ : {j // j ≠ i} → K) (x : {x : σ → K // x ∘ coe = x₀}),
            ∏ j, (x : σ → K) j ^ d j     : (fintype.sum_fiberwise _ _).symm
                                 ... = 0 : fintype.sum_eq_zero _ _,

  intros x₀,
  let e : K ≃ {x // x ∘ coe = x₀} :=  (equiv.fun_unique _ _).symm.trans (equiv.subtype_preimage _ x₀).symm,
  calc (∑ x : {x : σ → K // x ∘ coe = x₀}, ∏ j, (x : σ → K) j ^ d j) =
                  ∑ a : K, ∏ j : σ, (e a : σ → K) j ^ d j      : (finset.sum_equiv e _).symm
            ... = ∑ a : K, (∏ j, x₀ j ^ d j) * a ^ d i         : fintype.sum_congr _ _ _
            ... = (∏ j, x₀ j ^ d j) * ∑ a : K, a ^ d i         : by rw mul_sum
            ... = 0 : by rw [sum_pow_lt_card_sub_one _ hi, mul_zero],

  intros a,
  let e' : {j // j = i} ⊕ {j // j ≠ i} ≃ σ := equiv.sum_compl _,
  calc (∏ j : σ, (e a : σ → K) j ^ d j) =
          (e a : σ → K) i ^ d i * (∏ (j : {j // j ≠ i}), (e a : σ → K) j ^ d j) :
  begin
    rw [← finset.prod_equiv e', fintype.prod_sum_type],
    have this : _ = (e a : σ → K) i ^ d i := @fintype.prod_unique {j // j = i} _ _ _ (λ j, (e a : σ → K) j ^ d j),
    rw ← this,
    congr,
  end
                                    ... = a ^ d i * (∏ j, x₀ j ^ d j) : _
                                    ... = (∏ j, x₀ j ^ d j) * a ^ d i : mul_comm _ _,

  show (e a : σ → K) i ^ d i * (∏ (j : {j // j ≠ i}), (e a : σ → K) j ^ d j) =
    a ^ d i * ∏ j, x₀ j ^ d j,
  congr' 1,
  { simp [e, equiv.subtype_preimage_symm_apply_coe_neg _ x₀ _ _ (not_not.mpr rfl)], },
  { apply fintype.prod_congr,
    rintros ⟨j, hj⟩,
    show (e a : σ → K) j ^ d j = x₀ ⟨j, hj⟩ ^ d j,
    simp [e, equiv.subtype_preimage_symm_apply_coe_pos _ x₀ _ _ hj], }
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
    simp only [fintype.univ_punit, iff_self, forall_eq, mem_singleton, forall_true_iff], },
  { simpa only [fintype.univ_punit, sum_singleton] using h, }
end

end finite_field
