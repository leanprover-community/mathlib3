/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

This file proves that the `add_monoid_algebra R A` has no zero-divisors under the following
assumptions:
* * the semiring `R` itself has no zero-divisors;
* * the grading type `A` is a linearly ordered, add right cancel semigroup with strictly monotone
    left addition.

These conditions on `A` are sometimes referred to as `left-ordered`.  We also prove the symmetric
`right-ordered` result.

The eventual goal is to weaken the assumptions on `A`.
-/

namespace add_monoid_algebra
open finsupp

variables {R A : Type*} [semiring R]

/--  The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
lemma mul_apply_add_eq_mul_of_forall_ne [has_add A] {f g : add_monoid_algebra R A} {a0 b0 : A}
  (h : ∀ {a b : A}, a ∈ f.support → b ∈ g.support → (a ≠ a0 ∨ b ≠ b0) → a + b ≠ a0 + b0) :
  (f * g) (a0 + b0) = f a0 * g b0 :=
begin
  classical,
  rw mul_apply,
  refine (finset.sum_eq_single a0 _ _).trans _,
  { exact λ b H hb, finset.sum_eq_zero (λ x H1, if_neg (h H H1 (or.inl hb))) },
  { exact λ af0, by simp [not_mem_support_iff.mp af0] },
  { refine (finset.sum_eq_single b0 (λ b bg b0, _) _).trans (if_pos rfl),
    { by_cases af : a0 ∈ f.support,
      { exact if_neg (h af bg (or.inr b0)) },
      { simp only [not_mem_support_iff.mp af, zero_mul, if_t_t] } },
    { exact λ bf0, by simp [not_mem_support_iff.mp bf0] } },
end

section left_or_right_orderability

lemma left.exists_add_of_mem_support_single_mul [add_left_cancel_semigroup A]
  {g : add_monoid_algebra R A} (a x : A)
  (hx : x ∈ (single a 1 * g : add_monoid_algebra R A).support) :
  ∃ b ∈ g.support, a + b = x :=
by rwa [support_single_mul _ _ (λ y, by rw one_mul : ∀ y : R, 1 * y = 0 ↔ _), finset.mem_map] at hx

lemma right.exists_add_of_mem_support_single_mul [add_right_cancel_semigroup A]
  {f : add_monoid_algebra R A} (b x : A)
  (hx : x ∈ (f * single b 1 : add_monoid_algebra R A).support) :
  ∃ a ∈ f.support, a + b = x :=
by rwa [support_mul_single _ _ (λ y, by rw mul_one : ∀ y : R, y * 1 = 0 ↔ _), finset.mem_map] at hx

/--  If `R` is a semiring with no non-trivial zero-divisors and `A` is a left-ordered add right
cancel semigroup, then `add_monoid_algebra R A` also contains no non-zero zero-divisors. -/
lemma no_zero_divisors.of_left_ordered [no_zero_divisors R]
  [add_right_cancel_semigroup A] [linear_order A] [covariant_class A A (+) (<)] :
  no_zero_divisors (add_monoid_algebra R A) :=
⟨λ f g fg, begin
  contrapose! fg,
  rw [← support_nonempty_iff, ← support_nonempty_iff] at fg,
  cases fg with f0 g0,
  refine support_nonempty_iff.mp _,
  obtain ⟨a, ha, H⟩ := right.exists_add_of_mem_support_single_mul (g.support.min' g0)
    ((f * single (g.support.min' g0) 1 : add_monoid_algebra R A).support.min'
      (by rw support_mul_single; simp [f0])) (finset.min'_mem _ _),
  refine ⟨a + g.support.min' g0, mem_support_iff.mpr _⟩,
  rw mul_apply_add_eq_mul_of_forall_ne _,
  { refine mul_ne_zero _ _,
    exacts [mem_support_iff.mp ha, mem_support_iff.mp (finset.min'_mem _ _)] },
  { rw H,
    rintro b c bf cg (hb | hc); refine ne_of_gt _,
    { refine lt_of_lt_of_le (_ : _ < b + g.support.min' g0 ) _,
      { apply finset.min'_lt_of_mem_erase_min',
        rw ← H,
        apply finset.mem_erase_of_ne_of_mem,
        { simpa only [ne.def, add_left_inj] },
        { rw support_mul_single _ _ (λ y, by rw mul_one : ∀ y : R, y * 1 = 0 ↔ _),
          simpa only [finset.mem_map, add_right_embedding_apply, add_left_inj, exists_prop,
            exists_eq_right]} },
      { haveI : covariant_class A A (+) (≤) := has_add.to_covariant_class_left A,
        exact add_le_add_left (finset.min'_le _ _ cg) _ } },
    { refine lt_of_le_of_lt (_ : _ ≤ b + g.support.min' g0) _,
      { apply finset.min'_le,
        rw support_mul_single _ _ (λ y, by rw mul_one : ∀ y : R, y * 1 = 0 ↔ _),
        simp only [bf, finset.mem_map, add_right_embedding_apply, add_left_inj, exists_prop,
          exists_eq_right] },
      { refine add_lt_add_left _ _,
        exact finset.min'_lt_of_mem_erase_min' _ _ (finset.mem_erase.mpr ⟨hc, cg⟩) } } }
end⟩

/--  If `R` is a semiring with no non-trivial zero-divisors and `A` is a right-ordered add left
cancel semigroup, then `add_monoid_algebra R A` also contains no non-zero zero-divisors. -/
lemma no_zero_divisors.of_right_ordered [no_zero_divisors R]
  [add_left_cancel_semigroup A] [linear_order A] [covariant_class A A (function.swap (+)) (<)] :
  no_zero_divisors (add_monoid_algebra R A) :=
⟨λ f g fg, begin
  contrapose! fg,
  rw [← support_nonempty_iff, ← support_nonempty_iff] at fg,
  cases fg with f0 g0,
  refine support_nonempty_iff.mp _,
  obtain ⟨a, ha, H⟩ := left.exists_add_of_mem_support_single_mul (f.support.min' f0)
    ((single (f.support.min' f0) 1 * g : add_monoid_algebra R A).support.min'
      (by rw support_single_mul; simp [g0])) (finset.min'_mem _ _),
  refine ⟨f.support.min' f0 + a, mem_support_iff.mpr _⟩,
  rw mul_apply_add_eq_mul_of_forall_ne _,
  { refine mul_ne_zero _ _,
    exacts [mem_support_iff.mp (finset.min'_mem _ _), mem_support_iff.mp ha] },
  { rw H,
    rintro b c bf cg (hb | hc); refine ne_of_gt _,
    { refine lt_of_le_of_lt (_ : _ ≤ f.support.min' f0 + c) _,
      { apply finset.min'_le,
        rw support_single_mul _ _ (λ y, by rw one_mul : ∀ y : R, 1 * y = 0 ↔ _),
        simp only [cg, finset.mem_map, add_left_embedding_apply, add_right_inj, exists_prop,
          exists_eq_right] },
      { refine add_lt_add_right _ _,
        exact finset.min'_lt_of_mem_erase_min' _ _ (finset.mem_erase.mpr ⟨hb, bf⟩) } },
    { refine lt_of_lt_of_le (_ : _ < f.support.min' f0 + c) _,
      { apply finset.min'_lt_of_mem_erase_min',
        rw ← H,
        apply finset.mem_erase_of_ne_of_mem,
        { simpa only [ne.def, add_right_inj] },
        { rw support_single_mul _ _ (λ y, by rw one_mul : ∀ y : R, 1 * y = 0 ↔ _),
          simpa only [finset.mem_map, add_left_embedding_apply, add_right_inj, exists_prop,
            exists_eq_right]} },
      { haveI : covariant_class A A (function.swap (+)) (≤) := has_add.to_covariant_class_right A,
        exact add_le_add_right (finset.min'_le _ _ bf) _ } } }
end⟩

end left_or_right_orderability

end add_monoid_algebra
