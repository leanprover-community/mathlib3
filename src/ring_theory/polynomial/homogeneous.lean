/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial
import data.fintype.card

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/

open_locale big_operators

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

/-
TODO
* create definition for `∑ i in d.support, d i`
* define graded rings, and show that mv_polynomial is an example
-/

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def is_homogeneous [comm_semiring R] (φ : mv_polynomial σ R) (n : ℕ) :=
∀ ⦃d⦄, coeff d φ ≠ 0 → ∑ i in d.support, d i = n

section
variables [comm_semiring R]

variables {σ R}

lemma is_homogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
  is_homogeneous (monomial d r) n :=
begin
  intros c hc,
  rw coeff_monomial at hc,
  split_ifs at hc with h,
  { subst c, exact hn },
  { contradiction }
end
variables (σ) {R}

lemma is_homogeneous_C (r : R) :
  is_homogeneous (C r : mv_polynomial σ R) 0 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.zero_apply, finset.sum_const_zero],
end

variables (σ R)

lemma is_homogeneous_zero (n : ℕ) : is_homogeneous (0 : mv_polynomial σ R) n :=
λ d hd, false.elim (hd $ coeff_zero _)

lemma is_homogeneous_one : is_homogeneous (1 : mv_polynomial σ R) 0 :=
is_homogeneous_C _ _

variables {σ} (R)

lemma is_homogeneous_X (i : σ) :
  is_homogeneous (X i : mv_polynomial σ R) 1 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.support_single_ne_zero one_ne_zero, finset.sum_singleton],
  exact finsupp.single_eq_same
end

end

namespace is_homogeneous
variables [comm_semiring R] {φ ψ : mv_polynomial σ R} {m n : ℕ}

lemma coeff_eq_zero (hφ : is_homogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
  coeff d φ = 0 :=
by { have aux := mt (@hφ d) hd, classical, rwa not_not at aux }

lemma inj_right (hm : is_homogeneous φ m) (hn : is_homogeneous φ n) (hφ : φ ≠ 0) :
  m = n :=
begin
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ,
  rw [← hm hd, ← hn hd]
end

lemma add (hφ : is_homogeneous φ n) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ + ψ) n :=
begin
  intros c hc,
  rw coeff_add at hc,
  obtain h|h : coeff c φ ≠ 0 ∨ coeff c ψ ≠ 0,
  { contrapose! hc, simp only [hc, add_zero] },
  { exact hφ h },
  { exact hψ h }
end

lemma sum {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) n) :
  is_homogeneous (∑ i in s, φ i) n :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { intro, simp only [is_homogeneous_zero, finset.sum_empty] },
  { intros i s his IH h,
    simp only [his, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).add (IH _),
    intros j hjs,
    exact h j (finset.mem_insert_of_mem hjs) }
end

lemma mul (hφ : is_homogeneous φ m) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ * ψ) (m + n) :=
begin
  intros c hc,
  rw [coeff_mul] at hc,
  obtain ⟨⟨d, e⟩, hde, H⟩ := finset.exists_ne_zero_of_sum_ne_zero hc,
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0,
  { contrapose! H, cases H with H H; simp only [H, zero_mul, mul_zero] },
  specialize hφ aux.1, specialize hψ aux.2,
  rw finsupp.mem_antidiagonal_support at hde,
  classical,
  have hd' : d.support ⊆ d.support ∪ e.support := finset.subset_union_left _ _,
  have he' : e.support ⊆ d.support ∪ e.support := finset.subset_union_right _ _,
  rw [← hde, ← hφ, ← hψ, finset.sum_subset (finsupp.support_add),
    finset.sum_subset hd', finset.sum_subset he', ← finset.sum_add_distrib],
  { congr },
  all_goals { intros i hi, apply finsupp.not_mem_support_iff.mp }
end

lemma prod {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) (n i)) :
  is_homogeneous (∏ i in s, φ i) (∑ i in s, n i) :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { intro, simp only [is_homogeneous_one, finset.sum_empty, finset.prod_empty] },
  { intros i s his IH h,
    simp only [his, finset.prod_insert, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).mul (IH _),
    intros j hjs,
    exact h j (finset.mem_insert_of_mem hjs) }
end

lemma total_degree (hφ : is_homogeneous φ n) (h : φ ≠ 0) :
  total_degree φ = n :=
begin
  rw total_degree,
  apply le_antisymm,
  { apply finset.sup_le,
    intros d hd,
    rw finsupp.mem_support_iff at hd,
    rw [finsupp.sum, hφ hd], },
  { obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h,
    simp only [← hφ hd, finsupp.sum],
    replace hd := finsupp.mem_support_iff.mpr hd,
    exact finset.le_sup hd, }
end

end is_homogeneous

section
noncomputable theory
open_locale classical
open finset

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneous_component [comm_semiring R] (n : ℕ) :
  mv_polynomial σ R →+ mv_polynomial σ R :=
{ to_fun := λ φ, ∑ d in φ.support.filter (λ d, ∑ i in d.support, d i = n), monomial d (coeff d φ),
  map_zero' := by simp only [monomial_zero, sum_const_zero, coeff_zero],
  map_add' :=
  begin
    intros φ ψ, rw ext_iff, intro d, rw [coeff_add],
    by_cases hd : ∑ i in d.support, d i = n,
    { iterate 3 { rw [coeff_sum, sum_eq_single d], },
      { simp only [if_true, eq_self_iff_true, coeff_add, coeff_monomial], },
      all_goals
      { try { intros _ _ h, rw [coeff_monomial, if_neg h], }, },
      all_goals
      { intro h, rw [mem_filter, not_and'] at h, specialize h hd,
        rw [finsupp.not_mem_support_iff] at h, rwa [coeff_monomial, if_pos rfl], }, },
    { iterate 3 { rw [coeff_sum, sum_eq_zero], },
      { rw [add_zero] },
      all_goals
      { intros _ h, rw [mem_filter] at h,
        rw [coeff_monomial, if_neg], rintro rfl, exact hd h.2, }, }
  end }

section homogeneous_component
open finset
variables [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R)

lemma homogeneous_component_apply :
  homogeneous_component n φ =
  ∑ d in φ.support.filter (λ d, ∑ i in d.support, d i = n), monomial d (coeff d φ) := rfl

lemma homogeneous_component_is_homogeneous :
  (homogeneous_component n φ).is_homogeneous n :=
begin
  rw [homogeneous_component_apply],
  intros d hd,
  rw [coeff_sum] at hd,
  obtain ⟨d', hd', H⟩ := exists_ne_zero_of_sum_ne_zero hd,
  dsimp at H,
  rw [coeff_monomial] at H,
  split_ifs at H with h,
  { cases h, rw [mem_filter] at hd', exact hd'.2 },
  { contradiction }
end

lemma homogeneous_component_zero : homogeneous_component 0 φ = C (coeff 0 φ) :=
begin
  rw [homogeneous_component_apply, sum_eq_single (0 : σ →₀ ℕ)],
  { refl, },
  { intros d hd hd', rw [mem_filter, sum_eq_zero_iff] at hd,
    exfalso, apply hd', ext i,
    by_cases hi : i ∈ d.support,
    { rw [hd.2 i hi, finsupp.zero_apply], },
    { rw finsupp.not_mem_support_iff at hi,
      rwa finsupp.zero_apply } },
  { rw [mem_filter, not_and'],
    intro h, suffices : coeff 0 φ = 0, { rw [this, monomial_zero], },
    rw finsupp.not_mem_support_iff at h, apply h,
    rw sum_eq_zero, intros, rw finsupp.zero_apply }
end

lemma homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
  homogeneous_component n φ = 0 :=
begin
  rw [homogeneous_component_apply, sum_eq_zero],
  intros d hd, rw mem_filter at hd,
  exfalso, exact h _ hd.1 hd.2
end

lemma homogeneous_component_eq_zero (h : φ.total_degree < n) :
  homogeneous_component n φ = 0 :=
begin
  apply homogeneous_component_eq_zero',
  rw [total_degree, finset.sup_lt_iff] at h,
  { intros d hd, exact ne_of_lt (h d hd), },
  { exact lt_of_le_of_lt (nat.zero_le _) h, }
end

lemma sum_homogeneous_component :
  ∑ i in range (φ.total_degree + 1), homogeneous_component i φ = φ :=
begin
  rw ext_iff, intro d,
  rw [coeff_sum, sum_eq_single (∑ i in d.support, d i)],
  { rw [homogeneous_component_apply, coeff_sum, sum_eq_single d, coeff_monomial, if_pos rfl],
    { intros _ _ h, rw [coeff_monomial, if_neg h], },
    { rw [mem_filter, not_and'], intro h,
      suffices : coeff d φ = 0, { rw [this, monomial_zero, coeff_zero], },
      { rw finsupp.not_mem_support_iff at h, apply h rfl, } } },
  { intros n hn, contrapose!, rw eq_comm, apply homogeneous_component_is_homogeneous n φ, },
  { rw [mem_range, not_lt, nat.succ_le_iff],
    intro h,
    apply coeff_eq_zero_of_total_degree_lt,
    apply lt_of_le_of_lt _ h,
    rw [homogeneous_component_eq_zero _ _ h],
    exact nat.zero_le _, }
end

end homogeneous_component

end

end mv_polynomial
