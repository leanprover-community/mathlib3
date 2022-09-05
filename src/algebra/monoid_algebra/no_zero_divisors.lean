/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.support

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

This file studies the interaction between typeclass assumptions on two Types `R` and `A` and
whether `add_monoid_algebra R A` has non-zero zero-divisors.  For some background on related
questions, see [Kaplansky's Conjectures](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures),
especially the *zero divisor conjecture*.

_Conjecture._
Let `K` be a field, and `G` a torsion-free group. The group ring `K[G]` does not contain
nontrivial zero divisors, that is, it is a domain.

We formalize in this file the well-known result that if `R` is a field and `A` is a left-ordered
group, then `R[A]` contains no non-zero zero-divisors.  Some of these assumptions can be trivially
weakened: below we mention what assumptions are sufficient for the proofs in this file.

##  Main results

* `no_zero_divisors.of_left_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add right cancel semigroup with strictly monotone
  left addition, then `add_monoid_algebra R A` has no non-zero zero-divisors.
* `no_zero_divisors.of_right_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add left cancel semigroup with strictly monotone
  right addition, then `add_monoid_algebra R A` has no non-zero zero-divisors.

The conditions on `A` imposed in `no_zero_divisors.of_left_ordered` are sometimes referred to as
`left-ordered`.
The conditions on `A` imposed in `no_zero_divisors.of_right_ordered` are sometimes referred to as
`right-ordered`.

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.
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
  let gmin : A := g.support.min' (support_nonempty_iff.mpr fg.2),
  refine support_nonempty_iff.mp _,
  obtain ⟨a, ha, H⟩ := right.exists_add_of_mem_support_single_mul gmin
    ((f * single gmin 1 : add_monoid_algebra R A).support.min'
      (by rw support_mul_single; simp [support_nonempty_iff.mpr fg.1])) (finset.min'_mem _ _),
  refine ⟨a + gmin, mem_support_iff.mpr _⟩,
  rw mul_apply_add_eq_mul_of_forall_ne _,
  { refine mul_ne_zero _ _,
    exacts [mem_support_iff.mp ha, mem_support_iff.mp (finset.min'_mem _ _)] },
  { rw H,
    rintro b c bf cg (hb | hc); refine ne_of_gt _,
    { refine lt_of_lt_of_le (_ : _ < b + gmin ) _,
      { apply finset.min'_lt_of_mem_erase_min',
        rw ← H,
        apply finset.mem_erase_of_ne_of_mem,
        { simpa only [ne.def, add_left_inj] },
        { rw support_mul_single _ _ (λ y, by rw mul_one : ∀ y : R, y * 1 = 0 ↔ _),
          simpa only [finset.mem_map, add_right_embedding_apply, add_left_inj, exists_prop,
            exists_eq_right] } },
      { haveI : covariant_class A A (+) (≤) := has_add.to_covariant_class_left A,
        exact add_le_add_left (finset.min'_le _ _ cg) _ } },
    { refine lt_of_le_of_lt (_ : _ ≤ b + gmin) _,
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
  let fmin : A := f.support.min' (support_nonempty_iff.mpr fg.1),
  refine support_nonempty_iff.mp _,
  obtain ⟨a, ha, H⟩ := left.exists_add_of_mem_support_single_mul fmin
    ((single fmin 1 * g : add_monoid_algebra R A).support.min'
      (by rw support_single_mul; simp [support_nonempty_iff.mpr fg.2])) (finset.min'_mem _ _),
  refine ⟨fmin + a, mem_support_iff.mpr _⟩,
  rw mul_apply_add_eq_mul_of_forall_ne _,
  { refine mul_ne_zero _ _,
    exacts [mem_support_iff.mp (finset.min'_mem _ _), mem_support_iff.mp ha] },
  { rw H,
    rintro b c bf cg (hb | hc); refine ne_of_gt _,
    { refine lt_of_le_of_lt (_ : _ ≤ fmin + c) _,
      { apply finset.min'_le,
        rw support_single_mul _ _ (λ y, by rw one_mul : ∀ y : R, 1 * y = 0 ↔ _),
        simp only [cg, finset.mem_map, add_left_embedding_apply, add_right_inj, exists_prop,
          exists_eq_right] },
      { refine add_lt_add_right _ _,
        exact finset.min'_lt_of_mem_erase_min' _ _ (finset.mem_erase.mpr ⟨hb, bf⟩) } },
    { refine lt_of_lt_of_le (_ : _ < fmin + c) _,
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
