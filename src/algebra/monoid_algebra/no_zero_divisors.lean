/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.mv_polynomial.equiv

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s
-/

section PR_15978
namespace finset

variables {α : Type*} [linear_order α] {s : finset α} {a : α}

lemma max_eq_max' (hs : s.nonempty) : s.max = s.max' hs :=
begin
  revert hs,
  refine s.induction_on _ _; clear s,
  { rintro ⟨_, ⟨⟩⟩ },
  { intros a s as hs as0,
    by_cases s0 : s.nonempty,
    { rw [max_insert, max'_insert _ _ s0, hs s0, with_bot.coe_max, max_comm] },
    { rcases not_nonempty_iff_eq_empty.mp s0 with rfl,
      simp only [insert_emptyc_eq, max_singleton, max'_singleton] } }
end

lemma max'_erase_ne_self (s0 : (s.erase a).nonempty) :
  (s.erase a).max' s0 ≠ a :=
begin
  refine λ h, (s.not_mem_erase a) _,
  nth_rewrite 0 ← h,
  exact finset.max'_mem _ _
end

lemma max_erase_ne_self : (s.erase a).max ≠ a :=
begin
  by_cases s0 : (s.erase a).nonempty,
  { refine ne_of_eq_of_ne (finset.max_eq_max' s0) _,
    exact with_bot.coe_eq_coe.not.mpr (max'_erase_ne_self _) },
  { rw [finset.not_nonempty_iff_eq_empty.mp s0, finset.max_empty],
    exact with_bot.bot_ne_coe }
end

end finset
end PR_15978

namespace add_monoid_algebra

variables {R A : Type*} [semiring R] [linear_order A]

section a_version_with_different_typeclass_assumptions
variables [add_monoid A] [covariant_class A A ((+)) (<)] {a b : A} {f g : A →₀ R}

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
    exists_prop, not_exists, not_and, and_imp, forall_eq],
  intros _ x xs,
  refine (add_lt_add_left (with_bot.coe_lt_coe.mp _) _).ne',
  refine lt_of_le_of_lt _ fb,
  refine le_trans _ (finset.max_eq_max' ⟨_, xs⟩).ge,
  exact with_bot.coe_le_coe.mpr (f.support.le_max' _ _),
end

end a_version_with_different_typeclass_assumptions

variables [add_left_cancel_monoid A] {a b : A} {f g : A →₀ R}

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
    exists_prop, not_exists, not_and, and_imp, forall_eq, add_right_inj],
  intros _ x xs,
  refine (with_bot.coe_lt_coe.mp _).ne',
  refine lt_of_le_of_lt _ fb,
  refine le_trans _ (finset.max_eq_max' ⟨_, xs⟩).ge,
  exact with_bot.coe_le_coe.mpr (f.support.le_max' _ _),
end

lemma mul_apply_of_le [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (<)]
  (fa : f.support.max ≤ a) (gb : g.support.max ≤ b) :
  (f * g : add_monoid_algebra R A) (a + b) = f a * g b :=
begin
  rw [← f.erase_add_single a, add_mul, finsupp.add_apply, finsupp.add_apply, add_mul],
  convert zero_add _,
  { refine finsupp.not_mem_support_iff.mp (λ h, _),
    refine not_not.mpr ((support_mul _ g) h) _,
    simp only [finsupp.support_erase, finset.mem_bUnion, finset.mem_erase, ne.def,
      finset.mem_singleton, exists_prop, not_exists, not_and, and_imp],
    refine λ x xa xf y yg, ne_of_gt (add_lt_add_of_lt_of_le (lt_of_le_of_ne _ xa) _),
    repeat { exact with_bot.coe_le_coe.mp (le_trans (finset.coe_le_max_of_mem ‹_›) ‹_›) } },
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

protected lemma no_zero_divisors
  [no_zero_divisors R] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (<)] :
  no_zero_divisors (add_monoid_algebra R A) :=
begin
  refine ⟨λ a b ab, _⟩,
  contrapose! ab,
  apply_fun (λ x : add_monoid_algebra R A, x (a.support.max' (finsupp.support_nonempty_iff.mpr ab.1)
    + b.support.max' (finsupp.support_nonempty_iff.mpr ab.2))),
  simp only [finsupp.coe_zero, pi.zero_apply, ne.def],
  rw mul_apply_of_le;
  try { exact (le_of_eq (finset.max_eq_max' _)) },
  refine mul_ne_zero_iff.mpr ⟨_, _⟩;
  exact finsupp.mem_support_iff.mp (finset.max'_mem _ _),
end

end add_monoid_algebra
