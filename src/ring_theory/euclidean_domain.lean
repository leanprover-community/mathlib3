/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import algebra.gcd_monoid.basic
import ring_theory.coprime.basic
import ring_theory.ideal.basic

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

open gcd_monoid

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
