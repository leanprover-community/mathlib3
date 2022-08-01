/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.unique_factorization_domain

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `data/nat/squarefree`.

## Main Definitions
 - `squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_multiplicity_le_one`: `x` is `squarefree` iff for every `y`, either
  `multiplicity y x ≤ 1` or `is_unit y`.
 - `unique_factorization_monoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.

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
  exact ⟨0, by simv⟩,
end

lemma squarefree.ne_zero [monoid_with_zero R] [nontrivial R] {m : R}
  (hm : squarefree (m : R)) : m ≠ 0 :=
begin
  rintro rfl,
  exact not_squarefree_zero hm,
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
lemma prime.squarefree [cancel_comm_monoid_with_zero R] {x : R} (h : prime x) :
  squarefree x :=
h.irreducible.squarefree

lemma squarefree.of_mul_left [comm_monoid R] {m n : R} (hmn : squarefree (m * n)) : squarefree m :=
(λ p hp, hmn p (dvd_mul_of_dvd_left hp n))

lemma squarefree.of_mul_right [comm_monoid R] {m n : R} (hmn : squarefree (m * n)) : squarefree n :=
(λ p hp, hmn p (dvd_mul_of_dvd_right hp m))

lemma squarefree_of_dvd_of_squarefree [comm_monoid R]
  {x y : R} (hdvd : x ∣ y) (hsq : squarefree y) :
  squarefree x :=
λ a h, hsq _ (h.trans hdvd)

namespace multiplicity

section comm_monoid

variables [comm_monoid R] [decidable_rel (has_dvd.dvd : R → R → Prop)]

lemma squarefree_iff_multiplicity_le_one (r : R) :
  squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ is_unit x :=
begin
  refine forall_congr (λ a, _),
  rw [← sq, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_le, imp_congr _ iff.rfl],
  simpa using part_enat.add_one_le_iff_lt (part_enat.coe_ne_top 1)
end

end comm_monoid

section cancel_comm_monoid_with_zero

variables [cancel_comm_monoid_with_zero R] [wf_dvd_monoid R]

lemma finite_prime_left {a b : R} (ha : prime a) (hb : b ≠ 0) :
  multiplicity.finite a b :=
begin
  classical,
  revert hb,
  refine wf_dvd_monoid.induction_on_irreducible b (by contradiction) (λ u hu hu', _)
    (λ b p hb hp ih hpb, _),
  { rw [multiplicity.finite_iff_dom, multiplicity.is_unit_right ha.not_unit hu],
    exact part_enat.dom_coe 0, },
  { refine multiplicity.finite_mul ha
      (multiplicity.finite_iff_dom.mpr
        (part_enat.dom_of_le_coe (show multiplicity a p ≤ ↑1, from _))) (ih hb),
    norm_cast,
    exact (((multiplicity.squarefree_iff_multiplicity_le_one p).mp hp.squarefree a)
      .resolve_right ha.not_unit) }
end

end cancel_comm_monoid_with_zero

end multiplicity

section irreducible
variables [comm_monoid_with_zero R] [wf_dvd_monoid R]

lemma irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
  (∀ x : R, irreducible x → ¬ x * x ∣ r) ↔ ((r = 0 ∧ ∀ x : R, ¬irreducible x) ∨ squarefree r) :=
begin
  symmetry,
  split,
  { rintro (⟨rfl, h⟩ | h),
    { simpa using h },
    intros x hx t,
    exact hx.not_unit (h x t) },
  intro h,
  rcases eq_or_ne r 0 with rfl | hr,
  { exact or.inl (by simpa using h) },
  right,
  intros x hx,
  by_contra i,
  have : x ≠ 0,
  { rintro rfl,
    apply hr,
    simpa only [zero_dvd_iff, mul_zero] using hx},
  obtain ⟨j, hj₁, hj₂⟩ := wf_dvd_monoid.exists_irreducible_factor i this,
  exact h _ hj₁ ((mul_dvd_mul hj₂ hj₂).trans hx),
end

lemma squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
  squarefree r ↔ ∀ x : R, irreducible x → ¬ x * x ∣ r :=
by simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

lemma squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
  {r : R} (hr : ∃ (x : R), irreducible x) :
  squarefree r ↔ ∀ x : R, irreducible x → ¬ x * x ∣ r :=
begin
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ←not_exists],
  simv only [hr, not_true, false_or, and_false],
end

end irreducible

namespace unique_factorization_monoid
variables [cancel_comm_monoid_with_zero R] [nontrivial R] [unique_factorization_monoid R]
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
    { simv [multiset.count_eq_zero_of_not_mem hmem] } },
  { rw or_iff_not_imp_right, intro hu,
    by_cases h0 : a = 0,
    { simv [h0, x0] },
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
  { simv [hx, pow_eq_zero_iff (nat.pos_of_ne_zero h0)] },
  by_cases hy : y = 0,
  { simv [hy, zero_pow (nat.pos_of_ne_zero h0)] },
  refine ⟨λ h, _, λ h, h.pow h0⟩,
  rw [dvd_iff_normalized_factors_le_normalized_factors hx (pow_ne_zero n hy),
    normalized_factors_pow,
    ((squarefree_iff_nodup_normalized_factors hx).1 hsq).le_nsmul_iff_le h0] at h,
  rwa dvd_iff_normalized_factors_le_normalized_factors hx hy,
end

end unique_factorization_monoid
