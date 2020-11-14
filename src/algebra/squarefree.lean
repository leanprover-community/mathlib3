/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.unique_factorization_domain
import ring_theory.int.basic
import number_theory.divisors

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

## Main Definitions
 - `squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_multiplicity_le_one`: `x` is `squarefree` iff for every `y`, either
  `multiplicity y x ≤ 1` or `is_unit y`.
 - `unique_factorization_monoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.
 - `nat.squarefree_iff_nodup_factors`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.
## Tags
squarefree, multiplicity

-/

variables {R : Type*}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def squarefree [monoid R] (r : R) : Prop := ∀ x : R, x * x ∣ r → is_unit x

@[simp]
lemma is_unit.squarefree [comm_monoid R] {x : R} (h : is_unit x) :
  squarefree x :=
λ y hdvd, is_unit_of_mul_is_unit_left (is_unit_of_dvd_unit hdvd h)

@[simp]
lemma squarefree_one [comm_monoid R] : squarefree (1 : R) :=
is_unit_one.squarefree

@[simp]
lemma not_squarefree_zero [monoid_with_zero R] [nontrivial R] : ¬ squarefree (0 : R) :=
begin
  rw [squarefree, not_forall],
  exact ⟨0, not_imp.2 (by simp)⟩,
end

@[simp]
lemma irreducible.squarefree [comm_monoid R] {x : R} (h : irreducible x) :
  squarefree x :=
begin
  rintros y ⟨z, hz⟩,
  rw mul_assoc at hz,
  rcases h.2 _ _ hz with hu | hu,
  { exact hu },
  { apply is_unit_of_mul_is_unit_left hu },
end

@[simp]
lemma prime.squarefree [comm_cancel_monoid_with_zero R] {x : R} (h : prime x) :
  squarefree x :=
(irreducible_of_prime h).squarefree

lemma squarefree_of_dvd_of_squarefree [comm_monoid R]
  {x y : R} (hdvd : x ∣ y) (hsq : squarefree y) :
  squarefree x :=
λ a h, hsq _ (dvd.trans h hdvd)

namespace multiplicity
variables [comm_monoid R] [decidable_rel (has_dvd.dvd : R → R → Prop)]

lemma squarefree_iff_multiplicity_le_one (r : R) :
  squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ is_unit x :=
begin
  rw [squarefree],
  refine forall_congr (λ a, _),
  rw [or_iff_not_imp_left, ← pow_two, pow_dvd_iff_le_multiplicity, ← one_add_one_eq_two,
    enat.coe_add, enat.coe_one, enat.add_one_le_iff_lt, lt_iff_not_ge],
  apply enat.coe_ne_top,
end

end multiplicity

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero R] [nontrivial R] [unique_factorization_monoid R]
variables [normalization_monoid R] [decidable_eq R]

lemma squarefree_iff_nodup_factors {x : R} (x0 : x ≠ 0) :
  squarefree x ↔ multiset.nodup (factors x) :=
begin
  have drel : decidable_rel (has_dvd.dvd : R → R → Prop),
  { classical,
    apply_instance, },
  haveI := drel,
  rw [multiplicity.squarefree_iff_multiplicity_le_one, multiset.nodup_iff_count_le_one],
  split; intros h a,
  { by_cases hmem : a ∈ factors x,
    { rcases h a with h | h,
      { rw [multiplicity_eq_count_factors (irreducible_of_factor _ hmem) x0,
          ← enat.coe_one, enat.coe_le_coe, normalize_factor _ hmem] at h,
        apply h },
      { exfalso,
        apply (irreducible_of_factor _ hmem).1 h } },
    { rw multiset.count_eq_zero_of_not_mem,
        { simp },
        { apply hmem } } },
  { by_cases hu : is_unit a,
    { right,
      apply hu },
    left,
    by_cases h0 : a = 0,
    { rw [h0, multiplicity.multiplicity_eq_zero_of_not_dvd],
      { simp },
      rw zero_dvd_iff,
      apply x0 },
    rcases wf_dvd_monoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩,
    apply le_trans (multiplicity.multiplicity_le_multiplicity_of_dvd hdvd),
    rw [multiplicity_eq_count_factors hib x0, ← enat.coe_one, enat.coe_le_coe],
    apply h }
end

end unique_factorization_monoid

--move this
lemma multiset.prod_dvd_prod {α : Type*} [comm_monoid α] {x y : multiset α} (h : x ≤ y) :
  x.prod ∣ y.prod :=
begin
  rcases multiset.le_iff_exists_add.1 h with ⟨z, rfl⟩,
  simp,
end

namespace nat

lemma squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) :
  squarefree n ↔ n.factors.nodup :=
begin
  rw [unique_factorization_monoid.squarefree_iff_nodup_factors h0, nat.factors_eq],
  simp,
end

instance : decidable_pred (squarefree : ℕ → Prop)
| 0 := is_false not_squarefree_zero
| (n + 1) := decidable_of_iff _ (squarefree_iff_nodup_factors (nat.succ_ne_zero n)).symm

open unique_factorization_monoid

lemma divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
  (n.divisors.filter squarefree).val =
    (unique_factorization_monoid.factors n).to_finset.powerset.val.map (λ x, x.val.prod) :=
begin
  rw multiset.nodup_ext (finset.nodup _) (multiset.nodup_map_on _ (finset.nodup _)),
  { intro a,
    simp only [multiset.mem_filter, id.def, multiset.mem_map, finset.filter_val, ← finset.mem_def,
      mem_divisors],
    split,
    { rintro ⟨⟨an, h0⟩, hsq⟩,
      use (unique_factorization_monoid.factors a).to_finset,
      simp only [id.def, finset.mem_powerset],
      rcases an with ⟨b, rfl⟩,
      rw mul_ne_zero_iff at h0,
      rw unique_factorization_monoid.squarefree_iff_nodup_factors h0.1 at hsq,
      rw [multiset.to_finset_subset, multiset.to_finset_val, multiset.erase_dup_eq_self.2 hsq,
        ← associated_iff_eq, factors_mul h0.1 h0.2],
      exact ⟨multiset.subset_of_le (multiset.le_add_right _ _), factors_prod h0.1⟩ },
    { rintro ⟨s, hs, rfl⟩,
      rw [finset.mem_powerset, ← finset.val_le_iff, multiset.to_finset_val] at hs,
      have hs0 : s.val.prod ≠ 0,
      { rw [ne.def, multiset.prod_eq_zero_iff],
        simp only [exists_prop, id.def, exists_eq_right],
        intro con,
        apply not_irreducible_zero (irreducible_of_factor 0
            (multiset.mem_erase_dup.1 (multiset.mem_of_le hs con))) },
      rw [dvd_iff_dvd_of_rel_right (factors_prod h0).symm],
      refine ⟨⟨multiset.prod_dvd_prod (le_trans hs (multiset.erase_dup_le _)), h0⟩, _⟩,
      have h := unique_factorization_monoid.factors_unique irreducible_of_factor
        (λ x hx, irreducible_of_factor x (multiset.mem_of_le
          (le_trans hs (multiset.erase_dup_le _)) hx)) (factors_prod hs0),
      rw [associated_eq_eq, multiset.rel_eq] at h,
      rw [unique_factorization_monoid.squarefree_iff_nodup_factors hs0, h],
      apply s.nodup } },
  { intros x hx y hy h,
    rw [← finset.val_inj, ← multiset.rel_eq, ← associated_eq_eq],
    rw [← finset.mem_def, finset.mem_powerset] at hx hy,
    apply unique_factorization_monoid.factors_unique _ _ (associated_iff_eq.2 h),
    { intros z hz,
      apply irreducible_of_factor z,
      rw ← multiset.mem_to_finset,
      apply hx hz },
    { intros z hz,
      apply irreducible_of_factor z,
      rw ← multiset.mem_to_finset,
      apply hy hz } }
end

open_locale big_operators

lemma sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0)
  {α : Type*} [add_comm_monoid α] {f : ℕ → α} :
  ∑ i in (n.divisors.filter squarefree), f i =
    ∑ i in (unique_factorization_monoid.factors n).to_finset.powerset, f (i.val.prod) :=
by rw [finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, multiset.map_map,
    finset.sum_eq_multiset_sum]

end nat
