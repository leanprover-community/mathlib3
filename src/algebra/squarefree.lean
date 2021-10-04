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
  erw [not_forall],
  exact ⟨0, (by simp)⟩,
end

@[simp]
lemma irreducible.squarefree [comm_monoid R] {x : R} (h : irreducible x) :
  squarefree x :=
begin
  rintros y ⟨z, hz⟩,
  rw mul_assoc at hz,
  rcases h.is_unit_or_is_unit hz with hu | hu,
  { exact hu },
  { apply is_unit_of_mul_is_unit_left hu },
end

@[simp]
lemma prime.squarefree [comm_cancel_monoid_with_zero R] {x : R} (h : prime x) :
  squarefree x :=
h.irreducible.squarefree

lemma squarefree_of_dvd_of_squarefree [comm_monoid R]
  {x y : R} (hdvd : x ∣ y) (hsq : squarefree y) :
  squarefree x :=
λ a h, hsq _ (h.trans hdvd)

namespace multiplicity
variables [comm_monoid R] [decidable_rel (has_dvd.dvd : R → R → Prop)]

lemma squarefree_iff_multiplicity_le_one (r : R) :
  squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ is_unit x :=
begin
  refine forall_congr (λ a, _),
  rw [← sq, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_le, imp_congr],
  swap, { refl },
  convert enat.add_one_le_iff_lt (enat.coe_ne_top 1),
  norm_cast,
end

end multiplicity

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero R] [nontrivial R] [unique_factorization_monoid R]
variables [normalization_monoid R]

lemma squarefree_iff_nodup_normalized_factors [decidable_eq R] {x : R} (x0 : x ≠ 0) :
  squarefree x ↔ multiset.nodup (normalized_factors x) :=
begin
  have drel : decidable_rel (has_dvd.dvd : R → R → Prop),
  { classical,
    apply_instance, },
  haveI := drel,
  rw [multiplicity.squarefree_iff_multiplicity_le_one, multiset.nodup_iff_count_le_one],
  split; intros h a,
  { by_cases hmem : a ∈ normalized_factors x,
    { have ha := irreducible_of_normalized_factor _ hmem,
      rcases h a with h | h,
      { rw ← normalize_normalized_factor _ hmem,
        rw [multiplicity_eq_count_normalized_factors ha x0] at h,
        assumption_mod_cast },
      { have := ha.1, contradiction, } },
    { simp [multiset.count_eq_zero_of_not_mem hmem] } },
  { rw or_iff_not_imp_right, intro hu,
    by_cases h0 : a = 0,
    { simp [h0, x0] },
    rcases wf_dvd_monoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩,
    apply le_trans (multiplicity.multiplicity_le_multiplicity_of_dvd_left hdvd),
    rw [multiplicity_eq_count_normalized_factors hib x0],
    specialize h (normalize b),
    assumption_mod_cast }
end

lemma dvd_pow_iff_dvd_of_squarefree {x y : R} {n : ℕ} (hsq : squarefree x) (h0 : n ≠ 0) :
  x ∣ y ^ n ↔ x ∣ y :=
begin
  classical,
  by_cases hx : x = 0,
  { simp [hx, pow_eq_zero_iff (nat.pos_of_ne_zero h0)] },
  by_cases hy : y = 0,
  { simp [hy, zero_pow (nat.pos_of_ne_zero h0)] },
  refine ⟨λ h, _, λ h, h.pow h0⟩,
  rw [dvd_iff_normalized_factors_le_normalized_factors hx (pow_ne_zero n hy),
    normalized_factors_pow,
    ((squarefree_iff_nodup_normalized_factors hx).1 hsq).le_nsmul_iff_le h0] at h,
  rwa dvd_iff_normalized_factors_le_normalized_factors hx hy,
end

end unique_factorization_monoid

namespace nat

lemma squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) :
  squarefree n ↔ n.factors.nodup :=
begin
  rw [unique_factorization_monoid.squarefree_iff_nodup_normalized_factors h0, nat.factors_eq],
  simp,
end

instance : decidable_pred (squarefree : ℕ → Prop)
| 0 := is_false not_squarefree_zero
| (n + 1) := decidable_of_iff _ (squarefree_iff_nodup_factors (nat.succ_ne_zero n)).symm

open unique_factorization_monoid

lemma divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
  (n.divisors.filter squarefree).val =
    (unique_factorization_monoid.normalized_factors n).to_finset.powerset.val.map
      (λ x, x.val.prod) :=
begin
  rw multiset.nodup_ext (finset.nodup _) (multiset.nodup_map_on _ (finset.nodup _)),
  { intro a,
    simp only [multiset.mem_filter, id.def, multiset.mem_map, finset.filter_val, ← finset.mem_def,
      mem_divisors],
    split,
    { rintro ⟨⟨an, h0⟩, hsq⟩,
      use (unique_factorization_monoid.normalized_factors a).to_finset,
      simp only [id.def, finset.mem_powerset],
      rcases an with ⟨b, rfl⟩,
      rw mul_ne_zero_iff at h0,
      rw unique_factorization_monoid.squarefree_iff_nodup_normalized_factors h0.1 at hsq,
      rw [multiset.to_finset_subset, multiset.to_finset_val, multiset.erase_dup_eq_self.2 hsq,
        ← associated_iff_eq, normalized_factors_mul h0.1 h0.2],
      exact ⟨multiset.subset_of_le (multiset.le_add_right _ _), normalized_factors_prod h0.1⟩ },
    { rintro ⟨s, hs, rfl⟩,
      rw [finset.mem_powerset, ← finset.val_le_iff, multiset.to_finset_val] at hs,
      have hs0 : s.val.prod ≠ 0,
      { rw [ne.def, multiset.prod_eq_zero_iff],
        simp only [exists_prop, id.def, exists_eq_right],
        intro con,
        apply not_irreducible_zero (irreducible_of_normalized_factor 0
            (multiset.mem_erase_dup.1 (multiset.mem_of_le hs con))) },
      rw (normalized_factors_prod h0).symm.dvd_iff_dvd_right,
      refine ⟨⟨multiset.prod_dvd_prod (le_trans hs (multiset.erase_dup_le _)), h0⟩, _⟩,
      have h := unique_factorization_monoid.factors_unique irreducible_of_normalized_factor
        (λ x hx, irreducible_of_normalized_factor x (multiset.mem_of_le
          (le_trans hs (multiset.erase_dup_le _)) hx)) (normalized_factors_prod hs0),
      rw [associated_eq_eq, multiset.rel_eq] at h,
      rw [unique_factorization_monoid.squarefree_iff_nodup_normalized_factors hs0, h],
      apply s.nodup } },
  { intros x hx y hy h,
    rw [← finset.val_inj, ← multiset.rel_eq, ← associated_eq_eq],
    rw [← finset.mem_def, finset.mem_powerset] at hx hy,
    apply unique_factorization_monoid.factors_unique _ _ (associated_iff_eq.2 h),
    { intros z hz,
      apply irreducible_of_normalized_factor z,
      rw ← multiset.mem_to_finset,
      apply hx hz },
    { intros z hz,
      apply irreducible_of_normalized_factor z,
      rw ← multiset.mem_to_finset,
      apply hy hz } }
end

open_locale big_operators

lemma sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0)
  {α : Type*} [add_comm_monoid α] {f : ℕ → α} :
  ∑ i in (n.divisors.filter squarefree), f i =
    ∑ i in (unique_factorization_monoid.normalized_factors n).to_finset.powerset, f (i.val.prod) :=
by rw [finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, multiset.map_map,
    finset.sum_eq_multiset_sum]

lemma sq_mul_squarefree_of_pos {n : ℕ} (hn : 0 < n) :
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ squarefree a :=
begin
  let S := {s ∈ finset.range (n + 1) | s ∣ n ∧ ∃ x, s = x ^ 2},
  have hSne : S.nonempty,
  { use 1,
    have h1 : 0 < n ∧ ∃ (x : ℕ), 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩,
    simpa [S] },
  let s := finset.max' S hSne,
  have hs : s ∈ S := finset.max'_mem S hSne,
  simp only [finset.sep_def, S, finset.mem_filter, finset.mem_range] at hs,
  obtain ⟨hsn1, ⟨a, hsa⟩, ⟨b, hsb⟩⟩ := hs,
  rw hsa at hn,
  obtain ⟨hlts, hlta⟩ := canonically_ordered_comm_semiring.mul_pos.mp hn,
  rw hsb at hsa hn hlts,
  refine ⟨a, b, hlta, (pow_pos_iff zero_lt_two).mp hlts, hsa.symm, _⟩,
  rintro x ⟨y, hy⟩,
  rw nat.is_unit_iff,
  by_contra hx,
  refine lt_le_antisymm _ (finset.le_max' S ((b * x) ^ 2) _),
  { simp_rw [S, hsa, finset.sep_def, finset.mem_filter, finset.mem_range],
    refine ⟨lt_succ_iff.mpr (le_of_dvd hn _), _, ⟨b * x, rfl⟩⟩; use y; rw hy; ring },
  { convert lt_mul_of_one_lt_right hlts
      (one_lt_pow 2 x zero_lt_two (one_lt_iff_ne_zero_and_ne_one.mpr ⟨λ h, by simp * at *, hx⟩)),
    rw mul_pow },
end

lemma sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) :
  ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ squarefree (a + 1) :=
begin
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h,
  refine ⟨a₁.pred, b₁.pred, _, _⟩;
  simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁],
end

lemma sq_mul_squarefree (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ squarefree a :=
begin
  cases n,
  { exact ⟨1, 0, (by simp), squarefree_one⟩ },
  { obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n),
    exact ⟨a, b, h₁, h₂⟩ },
end

end nat
