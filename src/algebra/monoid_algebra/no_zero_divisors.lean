/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.mv_polynomial.equiv

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

This file proves that the `add_monoid_algebra R A` has no zero-divisors under the following
assumptions
* the semiring `R` itself has no zero-divisors;
* the grading type `A` has an addition, a linear order and both addition on the left and addition
  on the right are strictly monotone functions.

The eventual goal is to weaken the assumptions on `A`.  For instance, imposing the same monotonicity
assumptions on addition, but requiring the order on `A` to be a partial_order instead of a linear
order should be enough:
* TODO: a linear extension preserving the monotonicity assumptions should always exist.

This is not (yet) formalized, though.

###  Remarks

We use `covariant_class` assumptions on `A`.  In combination with `linear_order A`, these
assumptions actually imply that `A` is cancellative.  However, cancellativity alone in not enough.

Indeed, using `zmod 2`, that is `ℤ / 2 ℤ`, as the grading type `A`, there are examples of
`add_monoid_algebra`s containing non-zero zero divisors:
```lean
import data.zmod.defs
import algebra.monoid_algebra.basic

open finsupp add_monoid_algebra

example {R} [ring R] [nontrivial R] :
  ∃ x y : add_monoid_algebra R (zmod 2), x * y = 0 ∧ x ≠ 0 ∧ y ≠ 0 :=
begin
  --  use `[1 (mod 2)] - 1` and `[1 (mod 2)] + 1`, the rest is easy
  refine ⟨single 1 1 - single (0 : zmod 2) 1, single 1 1 + single (0 : zmod 2) 1, _, _⟩,
  { simp [sub_mul, mul_add, single_mul_single, sub_eq_zero], refl },
  { simp [←finsupp.single_neg, single_eq_single_iff, sub_eq_add_neg, ←eq_neg_iff_add_eq_zero.not] }
end
```
In this case, the grading type is the additive monoid `zmod 2` which is an abelian group (and,
in particular, it is cancellative).
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
