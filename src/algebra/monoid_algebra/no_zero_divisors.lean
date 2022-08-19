/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.mv_polynomial.equiv

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

This file proves that the `add_monoid_algebra R A` has no zero-divisors under the assumption that
the semiring `R` itself has no zero-divisors and assuming that the addition on `A` satisfies some
monotonicity assumptions.

The eventual goal is to weaken some of these assumptions, by showing that they can be realized by
choosing an appropriate linear extension of a partial order on `A`.
-/

namespace add_monoid_algebra

variables {R A : Type*} [semiring R] [linear_order A]

section a_version_with_different_typeclass_assumptions
variables [add_left_cancel_monoid A] {a b : A} {f g : A →₀ R}

/--  This lemma is extracted from the proof of `add_monoid_algebra.mul_apply_of_le`.  It has
somewhat weaker typeclass assumptions, but also proves a weaker result. -/
lemma single_mul_single_add_apply' {r : R} (s : R) (fb : f.support.max < b) :
  (finsupp.single a r * (finsupp.single b s + f) : add_monoid_algebra R A) (a + b) = r * s :=
begin
  rw [mul_add, single_mul_single, finsupp.add_apply, finsupp.single_eq_same],
  convert add_zero _,
  refine finsupp.not_mem_support_iff.mp (λ h, _),
  refine not_not.mpr ((support_mul (finsupp.single a r) f) h) _,
  simp only [finsupp.mem_support_single, finset.mem_bUnion, ne.def, finset.mem_singleton,
    exists_prop, not_exists, not_and, and_imp, forall_eq, add_right_inj],
  intros _ x xs,
  refine (with_bot.coe_lt_coe.mp _).ne',
  refine lt_of_le_of_lt _ fb,
  refine le_trans _ (finset.coe_max' ⟨_, xs⟩).le,
  exact with_bot.coe_le_coe.mpr (f.support.le_max' _ _),
end

end a_version_with_different_typeclass_assumptions

section covariant_lt
variables [has_add A] [covariant_class A A (+) (<)]
   {a b : A} {f g : A →₀ R}

/--  This lemma is extracted from the proof of `add_monoid_algebra.mul_apply_of_le`.  It has
somewhat weaker typeclass assumptions, but also proves a weaker result. -/
lemma single_mul_single_add_apply {r : R} (s : R) (fb : f.support.max < b) :
  (finsupp.single a r * (finsupp.single b s + f) : add_monoid_algebra R A) (a + b) = r * s :=
begin
  rw [mul_add, single_mul_single, finsupp.add_apply, finsupp.single_eq_same],
  convert add_zero _,
  refine finsupp.not_mem_support_iff.mp (λ h, _),
  refine not_not.mpr ((support_mul (finsupp.single a r) f) h) _,
  simp only [finsupp.mem_support_single, finset.mem_bUnion, ne.def, finset.mem_singleton,
    exists_prop, not_exists, not_and, and_imp, forall_eq],
  intros _ x xs,
  refine (add_lt_add_left (with_bot.coe_lt_coe.mp _) _).ne',
  refine lt_of_le_of_lt _ fb,
  refine le_trans _ (finset.coe_max' ⟨_, xs⟩).le,
  exact with_bot.coe_le_coe.mpr (f.support.le_max' _ _),
end

variables [covariant_class A A (function.swap (+)) (<)]

lemma mul_apply_of_le (fa : f.support.max ≤ a) (gb : g.support.max ≤ b) :
  (f * g : add_monoid_algebra R A) (a + b) = f a * g b :=
begin
  rw [← f.erase_add_single a, add_mul, finsupp.add_apply, finsupp.add_apply, add_mul],
  convert zero_add _,
  { refine finsupp.not_mem_support_iff.mp (λ h, _),
    refine not_not.mpr ((support_mul _ g) h) _,
    simp only [finsupp.support_erase, finset.mem_bUnion, finset.mem_erase, ne.def,
      finset.mem_singleton, exists_prop, not_exists, not_and, and_imp],
    haveI : covariant_class A A (+) (≤) := has_add.to_covariant_class_left A,
    refine λ x xa xf y yg, (add_lt_add_of_lt_of_le (lt_of_le_of_ne _ xa) _).ne',
    repeat { exact with_bot.coe_le_coe.mp ((finset.coe_le_max_of_mem ‹_›).trans ‹_›) } },
  { --rw [finsupp.erase_same, zero_mul, zero_add],
    convert zero_add _,
    { rw [finsupp.erase_same, zero_mul] },
    { nth_rewrite 0 ← g.single_add_erase b,
      rw finsupp.single_eq_same,
      refine single_mul_single_add_apply _ _,
      rw [finsupp.support_erase],
      refine (lt_of_le_of_ne ((finset.max_mono (g.support.erase_subset b)).trans gb) _),
      exact finset.max_erase_ne_self } },
end

protected lemma no_zero_divisors [no_zero_divisors R] : no_zero_divisors (add_monoid_algebra R A) :=
begin
  refine ⟨λ a b ab, _⟩,
  contrapose! ab,
  apply_fun (λ x : add_monoid_algebra R A, x (a.support.max' (finsupp.support_nonempty_iff.mpr ab.1)
    + b.support.max' (finsupp.support_nonempty_iff.mpr ab.2))),
  simp only [finsupp.coe_zero, pi.zero_apply],
  rw mul_apply_of_le;
  try { exact (finset.coe_max' _).ge },
  refine mul_ne_zero_iff.mpr ⟨_, _⟩;
  exact finsupp.mem_support_iff.mp (finset.max'_mem _ _),
end

end covariant_lt

end add_monoid_algebra
