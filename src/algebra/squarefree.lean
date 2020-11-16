/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.unique_factorization_domain
import ring_theory.int.basic

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
  refine forall_congr (λ a, _),
  rw [← pow_two, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_le, imp_congr],
  swap, { refl },
  convert enat.add_one_le_iff_lt (enat.coe_ne_top _),
  norm_cast,
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
    { have ha := irreducible_of_factor _ hmem,
      rcases h a with h | h,
      { rw ← normalize_factor _ hmem,
        rw [multiplicity_eq_count_factors ha x0] at h,
        assumption_mod_cast },
      { have := ha.1, contradiction, } },
    { simp [multiset.count_eq_zero_of_not_mem hmem] } },
  { rw or_iff_not_imp_right, intro hu,
    by_cases h0 : a = 0,
    { simp [h0, x0] },
    rcases wf_dvd_monoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩,
    apply le_trans (multiplicity.multiplicity_le_multiplicity_of_dvd hdvd),
    rw [multiplicity_eq_count_factors hib x0],
    specialize h (normalize b),
    assumption_mod_cast }
end

end unique_factorization_monoid

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

end nat
