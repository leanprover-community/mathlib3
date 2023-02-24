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
  exact ⟨0, by simp⟩,
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

lemma squarefree.squarefree_of_dvd [comm_monoid R]
  {x y : R} (hdvd : x ∣ y) (hsq : squarefree y) :
  squarefree x :=
λ a h, hsq _ (h.trans hdvd)

section squarefree_gcd_of_squarefree

variables {α : Type*} [cancel_comm_monoid_with_zero α] [gcd_monoid α]

lemma squarefree.gcd_right (a : α) {b : α} (hb : squarefree b) :
  squarefree (gcd a b) :=
hb.squarefree_of_dvd (gcd_dvd_right _ _)

lemma squarefree.gcd_left {a : α} (b : α) (ha : squarefree a) :
  squarefree (gcd a b) :=
ha.squarefree_of_dvd (gcd_dvd_left _ _)

end squarefree_gcd_of_squarefree

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
  simp only [hr, not_true, false_or, and_false],
end

end irreducible

section is_radical

variables [cancel_comm_monoid_with_zero R]

theorem is_radical.squarefree {x : R} (h0 : x ≠ 0) (h : is_radical x) : squarefree x :=
begin
  rintro z ⟨w, rfl⟩,
  specialize h 2 (z * w) ⟨w, by simp_rw [pow_two, mul_left_comm, ← mul_assoc]⟩,
  rwa [← one_mul (z * w), mul_assoc, mul_dvd_mul_iff_right, ← is_unit_iff_dvd_one] at h,
  rw [mul_assoc, mul_ne_zero_iff] at h0, exact h0.2,
end

variable [gcd_monoid R]

theorem squarefree.is_radical {x : R} (hx : squarefree x) : is_radical x :=
(is_radical_iff_pow_one_lt 2 one_lt_two).2 $ λ y hy, and.right $ (dvd_gcd_iff x x y).1
begin
  by_cases gcd x y = 0, { rw h, apply dvd_zero },
  replace hy := ((dvd_gcd_iff x x _).2 ⟨dvd_rfl, hy⟩).trans gcd_pow_right_dvd_pow_gcd,
  obtain ⟨z, hz⟩ := gcd_dvd_left x y,
  nth_rewrite 0 hz at hy ⊢,
  rw [pow_two, mul_dvd_mul_iff_left h] at hy,
  obtain ⟨w, hw⟩ := hy,
  exact (hx z ⟨w, by rwa [mul_right_comm, ←hw]⟩).mul_right_dvd.2 dvd_rfl,
end

theorem is_radical_iff_squarefree_or_zero {x : R} : is_radical x ↔ squarefree x ∨ x = 0 :=
⟨λ hx, (em $ x = 0).elim or.inr (λ h, or.inl $ hx.squarefree h),
  or.rec squarefree.is_radical $ by { rintro rfl, rw zero_is_radical_iff, apply_instance }⟩

theorem is_radical_iff_squarefree_of_ne_zero {x : R} (h : x ≠ 0) : is_radical x ↔ squarefree x :=
⟨is_radical.squarefree h, squarefree.is_radical⟩

end is_radical

namespace unique_factorization_monoid
variables [cancel_comm_monoid_with_zero R] [unique_factorization_monoid R]

lemma squarefree_iff_nodup_normalized_factors [normalization_monoid R] [decidable_eq R] {x : R}
  (x0 : x ≠ 0) : squarefree x ↔ multiset.nodup (normalized_factors x) :=
begin
  have drel : decidable_rel (has_dvd.dvd : R → R → Prop),
  { classical,
    apply_instance, },
  haveI := drel,
  rw [multiplicity.squarefree_iff_multiplicity_le_one, multiset.nodup_iff_count_le_one],
  haveI := nontrivial_of_ne x 0 x0,
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
  haveI := unique_factorization_monoid.to_gcd_monoid R,
  exact ⟨hsq.is_radical n y, λ h, h.pow h0⟩,
end

end unique_factorization_monoid
