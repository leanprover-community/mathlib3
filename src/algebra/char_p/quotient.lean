/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/

import algebra.char_p.basic
import algebra.ring_quot

/-!
# Characteristic of quotients rings
-/

universes u v

namespace char_p

theorem quotient (R : Type u) [comm_ring R] (p : ℕ) [hp1 : fact p.prime] (hp2 : ↑p ∈ nonunits R) :
  char_p (ideal.span {p} : ideal R).quotient p :=
have hp0 : (p : (ideal.span {p} : ideal R).quotient) = 0,
  from (ideal.quotient.mk (ideal.span {p} : ideal R)).map_nat_cast p ▸
    ideal.quotient.eq_zero_iff_mem.2 (ideal.subset_span $ set.mem_singleton _),
ring_char.of_eq $ or.resolve_left ((nat.dvd_prime hp1.1).1 $ ring_char.dvd hp0) $ λ h1,
hp2 $ is_unit_iff_dvd_one.2 $ ideal.mem_span_singleton.1 $ ideal.quotient.eq_zero_iff_mem.1 $
@@subsingleton.elim (@@char_p.subsingleton _ $ ring_char.of_eq h1) _ _

/-- If an ideal does not contain any coercions of natural numbers other than zero, then its quotient
inherits the characteristic of the underlying ring. -/
lemma quotient' {R : Type*} [comm_ring R] (p : ℕ) [char_p R p] (I : ideal R)
  (h : ∀ x : ℕ, (x : R) ∈ I → (x : R) = 0) :
  char_p I.quotient p :=
⟨λ x, begin
  rw [←cast_eq_zero_iff R p x, ←(ideal.quotient.mk I).map_nat_cast],
  refine quotient.eq'.trans (_ : ↑x - 0 ∈ I ↔ _),
  rw sub_zero,
  exact ⟨h x, λ h', h'.symm ▸ I.zero_mem⟩,
end⟩

end char_p
