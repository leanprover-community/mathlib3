/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial
import algebra.pi_instances
import field_theory.finite
import tactic.nth_rewrite

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

section

variables {α : Type*} {β : Type*}

@[simp] lemma equiv.sigma_preimage_equiv_apply (f : α → β) (x : Σ b, {x // f x = b}) :
  (equiv.sigma_preimage_equiv f) x = x.2.1 := rfl

def equiv.sum_compl (p : α → Prop) [decidable_pred p] :
  {a // p a} ⊕ {a // ¬ p a} ≃ α :=
{ to_fun := sum.elim coe coe,
  inv_fun := λ a, if h : p a then sum.inl ⟨a, h⟩ else sum.inr ⟨a, h⟩,
  left_inv := by { rintros (⟨x,hx⟩|⟨x,hx⟩); dsimp; [rw dif_pos, rw dif_neg], },
  right_inv := λ a, by { dsimp, split_ifs; refl } }

def equiv.not_not (p : α → Prop) [decidable_pred p] :
  {x // ¬ ¬ p x} ≃ {x // p x} :=
{ to_fun := λ ⟨x, h⟩, ⟨x, not_not.mp h⟩,
  inv_fun := λ ⟨x, h⟩, ⟨x, not_not.mpr h⟩,
  left_inv := λ ⟨x, h⟩, rfl,
  right_inv := λ ⟨x, h⟩, rfl }

def equiv.foo (p : α → Prop) [decidable_pred p] (x₀ : {a // p a} → β) :
  {x : α → β // x ∘ coe = x₀} ≃ ({a // ¬ p a} → β) :=
{ to_fun := λ x, x.1 ∘ coe,
  inv_fun := λ x, ⟨λ a, if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩,
    funext $ λ ⟨a, h⟩, dif_pos h⟩,
  left_inv := λ ⟨x, hx⟩, subtype.val_injective $ funext $ λ a,
    (by { dsimp, split_ifs; [ rw ← hx, skip ]; refl }),
  right_inv := λ x, funext $ λ ⟨a, h⟩, by { dsimp, rw [dif_neg h], } }

variables (α)

def equiv.bar [unique α] : (α → β) ≃ β :=
{ to_fun := λ f, f (default α),
  inv_fun := λ b a, b,
  left_inv := λ f, funext $ λ a, congr_arg f $ subsingleton.elim _ _,
  right_inv := λ b, rfl }

end

section

variables {α : Type*} {γ : Type*} [fintype α] [comm_monoid γ]

@[simp] lemma finsupp.prod_pow (f : α →₀ ℕ) (g : α → γ) :
  f.prod (λ a b, g a ^ b) = univ.prod (λ a : α, g a ^ (f a)) :=
begin
  classical,
  rw [finsupp.prod, ← fintype.prod_extend_by_one f.support, prod_congr rfl],
  intros a ha,
  split_ifs with h h,
  { refl },
  { rw [finsupp.not_mem_support_iff.mp h, pow_zero] }
end

end

section

variables {α : Type*} {α₁ : Type*} {α₂ : Type*} {β : Type*} [fintype α₁] [fintype α₂] [comm_monoid β]

@[to_additive]
lemma finset.prod_sum_univ (f : α₁ ⊕ α₂ → β) :
  univ.prod f = univ.prod (f ∘ sum.inl) * univ.prod (f ∘ sum.inr) :=
begin
  classical,
  let s : finset (α₁ ⊕ α₂) := univ.image sum.inr,
  rw [← prod_sdiff (subset_univ s),
      ← @prod_image (α₁ ⊕ α₂) _ _ _ _ _ _ sum.inl,
      ← @prod_image (α₁ ⊕ α₂) _ _ _ _ _ _ sum.inr],
  { congr, rw finset.ext, rintro (a|a);
    { simp only [mem_image, exists_eq, mem_sdiff, mem_univ, exists_false,
        exists_prop_of_true, not_false_iff, and_self, not_true, and_false], } },
  all_goals { intros, solve_by_elim [sum.inl.inj, sum.inr.inj], }
end

end

section

instance subtype.unique {α : Type*} (a : α) : unique {x // x = a} :=
{ default := ⟨a, rfl⟩,
  uniq := λ ⟨x, h⟩, subtype.val_injective h }

instance subtype.not_not_unique {α : Type*} (p : α → Prop) [decidable_pred p] [unique {x // p x}] :
  unique {x // ¬ ¬ p x} :=
(equiv.not_not p).unique_of_equiv ‹_›

end

lemma sum_mv_polynomial_eq_zero [decidable_eq σ] (f : mv_polynomial σ K)
  (h : f.total_degree < (q - 1) * fintype.card σ) :
  univ.sum (λ x, f.eval x) = (0:K) :=
begin
  simp only [eval, eval₂, finsupp.sum, id.def],
  rw [sum_comm, sum_eq_zero],
  intros d hd,
  rw [← mul_sum, mul_eq_zero], right,
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1, from exists_degree_lt_card_sub_one f h d hd,

  haveI : decidable_eq K := classical.dec_eq K,

  refine calc _ = univ.sum (λ (x₀ : {j // j ≠ i} → K),
         univ.sum (λ (x : {x : σ → K // x ∘ coe = x₀}),
              ((λ (x : σ → K), d.prod (λ (n : σ), pow (x n)))) x.1)) : _
              ... = 0 : sum_eq_zero _,
  { let e := equiv.sigma_preimage_equiv (λ x, x ∘ coe : (σ → K) → ({j // j ≠ i} → K)),
    rw [← sum_equiv e, ← univ_sigma_univ, sum_sigma], refl, },

  intros x₀ hx₀,
  let c := univ.prod (λ j, x₀ j ^ d j),
  refine calc _ = univ.sum (λ a : K, c * a ^ d i) : _
            ... = c * univ.sum (λ a : K, a ^ d i) : by rw mul_sum
            ... = 0 : by rw [sum_pow_lt_card_sub_one _ hi, mul_zero],

  let e' : {x // x ∘ coe = x₀} ≃ K := (equiv.foo _ x₀).trans (equiv.bar _),
  rw [← sum_equiv e'.symm],

  apply sum_congr rfl,
  intros a ha,

  let e'' : {j // j = i} ⊕ {j // j ≠ i} ≃ σ := equiv.sum_compl _,
  dsimp,
  rw [finsupp.prod_pow, ← prod_equiv e'', finset.prod_sum_univ, mul_comm],
  congr' 1,
  { apply prod_congr rfl,
    rintros ⟨j, hj⟩ _,
    dsimp [e'', equiv.sum_compl, equiv.foo, equiv.bar],
    rw dif_pos hj, },
  { simp only [comp_app, prod_singleton, univ_unique, singleton_eq_singleton],
    dsimp [e'', equiv.sum_compl, equiv.foo, equiv.bar],
    rw dif_neg, { refl }, { rw not_not, refl } }
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
