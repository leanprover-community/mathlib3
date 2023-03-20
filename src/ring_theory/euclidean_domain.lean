/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import algebra.gcd_monoid.basic
import algebra.euclidean_domain.basic
import ring_theory.ideal.basic
import ring_theory.principal_ideal_domain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/

noncomputable theory
open_locale classical
open euclidean_domain set ideal

section gcd_monoid

variables {R : Type*} [euclidean_domain R] [gcd_monoid R]

lemma gcd_ne_zero_of_left (p q : R) (hp : p ≠ 0) :
  gcd_monoid.gcd p q ≠ 0 :=
λ h, hp $ eq_zero_of_zero_dvd (h ▸ gcd_dvd_left p q)

lemma gcd_ne_zero_of_right (p q : R) (hp : q ≠ 0) :
  gcd_monoid.gcd p q ≠ 0 :=
λ h, hp $ eq_zero_of_zero_dvd (h ▸ gcd_dvd_right p q)

lemma left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) :
  p / gcd_monoid.gcd p q ≠ 0 :=
begin
  obtain ⟨r, hr⟩ := gcd_monoid.gcd_dvd_left p q,
  obtain ⟨pq0, r0⟩ : gcd_monoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hp),
  rw [hr, mul_comm, mul_div_cancel _ pq0] { occs := occurrences.pos [1] },
  exact r0,
end

lemma right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) :
  q / gcd_monoid.gcd p q ≠ 0 :=
begin
  obtain ⟨r, hr⟩ := gcd_monoid.gcd_dvd_right p q,
  obtain ⟨pq0, r0⟩ : gcd_monoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hq),
  rw [hr, mul_comm, mul_div_cancel _ pq0] { occs := occurrences.pos [1] },
  exact r0,
end

end gcd_monoid

namespace euclidean_domain

/-- Create a `gcd_monoid` whose `gcd_monoid.gcd` matches `euclidean_domain.gcd`. -/
def gcd_monoid (R) [euclidean_domain R] : gcd_monoid R :=
{ gcd := gcd,
  lcm := lcm,
  gcd_dvd_left := gcd_dvd_left,
  gcd_dvd_right := gcd_dvd_right,
  dvd_gcd := λ a b c, dvd_gcd,
  gcd_mul_lcm := λ a b, by rw euclidean_domain.gcd_mul_lcm,
  lcm_zero_left := lcm_zero_left,
  lcm_zero_right := lcm_zero_right }

variables {α : Type*} [euclidean_domain α] [decidable_eq α]

theorem span_gcd {α} [euclidean_domain α] (x y : α) :
  span ({gcd x y} : set α) = span ({x, y} : set α) :=
begin
  letI := euclidean_domain.gcd_monoid α,
  exact span_gcd x y,
end

theorem gcd_is_unit_iff {α} [euclidean_domain α] {x y : α} :
  is_unit (gcd x y) ↔ is_coprime x y :=
begin
  letI := euclidean_domain.gcd_monoid α,
  exact gcd_is_unit_iff x y,
end

-- this should be proved for UFDs surely?
theorem is_coprime_of_dvd {α} [euclidean_domain α] {x y : α}
  (nonzero : ¬ (x = 0 ∧ y = 0)) (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
begin
  letI := euclidean_domain.gcd_monoid α,
  exact is_coprime_of_dvd x y nonzero H,
end

-- this should be proved for UFDs surely?
theorem dvd_or_coprime {α} [euclidean_domain α] (x y : α)
  (h : irreducible x) : x ∣ y ∨ is_coprime x y :=
begin
  letI := euclidean_domain.gcd_monoid α,
  exact dvd_or_coprime x y h,
end

end euclidean_domain
