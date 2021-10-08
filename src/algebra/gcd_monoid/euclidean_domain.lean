/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import algebra.euclidean_domain
import algebra.gcd_monoid.basic

/-!
# Euclidean domains with normalizing `gcd`

This file contains some results on types satisfying both `euclidean_domain` and `gcd_monoid`,
such as `polynomial K` where `K` is a field.
-/

variables {R : Type*} [euclidean_domain R]

namespace euclidean_domain

section gcd_monoid

variables [gcd_monoid R]

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

end euclidean_domain
