/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

This file proves that the `add_monoid_algebra R A` has no zero-divisors under the following
assumptions
* the semiring `R` itself has no zero-divisors;
* the grading type `A` has an addition, a linear order and both addition on the left and addition
  on the right are strictly monotone functions.

The eventual goal is to weaken the assumptions on `A`.  For instance, can we trade `linear_order A`
for some stronger monotonicity conditions?

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
  refine ⟨of' _ _ 1 - single 0 1, of' _ _ 1 +  single 0 1, _, _⟩,
  { simp [sub_mul, mul_add, single_mul_single, sub_eq_zero], refl },
  { simp [←finsupp.single_neg, single_eq_single_iff, sub_eq_add_neg, ←eq_neg_iff_add_eq_zero.not] }
end
```
In this case, the grading type is the additive monoid `zmod 2` which is an abelian group (and,
in particular, it is cancellative).
-/

namespace add_monoid_algebra
open finsupp

variables {R A : Type*} [semiring R]

section a_version_with_different_typeclass_assumptions

section no_covariant
variables [add_left_cancel_semigroup A] {a b : A} {f : add_monoid_algebra R A}

lemma mul_apply_add_eq_mul_of_forall_ne {f g : add_monoid_algebra R A} {a0 b0 : A}
  (h : ∀ a b : A, a ∈ f.support → b ∈ g.support → (a ≠ a0 ∨ b ≠ b0) → a + b ≠ a0 + b0) :
  (f * g) (a0 + b0) = f a0 * g b0 :=
begin
  classical,
  rw mul_apply,
  refine (finset.sum_eq_single a0 _ _).trans _,
  { exact λ b H (hb : b ≠ a0), finset.sum_eq_zero (λ x H1, if_neg (h b x H H1 (or.inl hb))) },
  { exact λ af0, by simp [not_mem_support_iff.mp af0] },
  { refine (finset.sum_eq_single b0 _ _).trans _,
    { exact λ _ _ _, if_neg (by simpa only [add_right_inj]) },
    { exact λ bf0, by simp [not_mem_support_iff.mp bf0] },
    { exact if_pos rfl } },
end

lemma exists_add_of_mem_support_single_mul {g : add_monoid_algebra R A} (a x : A)
  (hx : x ∈ (single a 1 * g : add_monoid_algebra R A).support) :
  ∃ b, b ∈ g.support ∧ a + b = x :=
begin
  rw support_single_mul _ _ (λ y, by rw one_mul : ∀ y : R, 1 * y = 0 ↔ _) at hx,
  simpa only [finset.mem_map, exists_prop] using hx,
end

/--  This lemma is extracted from the proof of `add_monoid_algebra.mul_apply_of_le`.  It has
somewhat weaker typeclass assumptions, but also proves a weaker result. -/
lemma single_mul_apply' (r : R) :
  (single a r * f : add_monoid_algebra R A) (a + b) = r * f b :=
begin
  convert mul_apply_add_eq_mul_of_forall_ne _,
  { exact single_eq_same.symm },
  { rintros x y hx hy (hnx | hny),
    { simpa [mem_support_iff, ne.def, single_apply_eq_zero, hnx] using hx },
    { simp only [mem_support_iff, single_apply_ne_zero] at hx,
      rcases hx with ⟨rfl, hx⟩,
      simpa } },
/-
  classical,
  nth_rewrite 0 ← f.erase_add_single b,
  rw [mul_add, single_mul_single, finsupp.add_apply, finsupp.single_eq_same],
  convert zero_add _,
  refine finsupp.not_mem_support_iff.mp (λ h, _),
  refine not_not.mpr ((support_mul (finsupp.single a r) (f.erase b)) h) _,
  simpa only [finsupp.mem_support_single, finset.mem_bUnion, ne.def, finset.mem_singleton,
    exists_prop, not_exists, not_and, and_imp, forall_eq, finsupp.support_erase, add_right_inj]
    using λ _ x xs, (finset.ne_of_mem_erase xs).symm,
-/
end

end no_covariant

variables [no_zero_divisors R] [add_left_cancel_monoid A] [linear_order A]
  [covariant_class A A (function.swap (+)) (<)] {f g : add_monoid_algebra R A} {a b : A}

lemma no_zero_divisors.of_right_ordered : no_zero_divisors (add_monoid_algebra R A) :=
⟨λ f g fg, begin
  contrapose! fg,
  rw [← support_nonempty_iff, ← support_nonempty_iff] at fg,
  cases fg with f0 g0,
  refine support_nonempty_iff.mp _,
  obtain ⟨a, ha, H⟩ := exists_add_of_mem_support_single_mul (f.support.min' f0)
    ((single (f.support.min' f0) 1 * g : add_monoid_algebra R A).support.min'
      (by rw support_single_mul; simp [g0])) (finset.min'_mem _ _),
  refine ⟨f.support.min' f0 + a, mem_support_iff.mpr _⟩,
  rw mul_apply_add_eq_mul_of_forall_ne _,
  { simp only [ne.def, mul_eq_zero, not_or_distrib, mem_support_iff.mp ha, not_false_iff, and_true],
    exact mem_support_iff.mp (finset.min'_mem _ _) },
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

end a_version_with_different_typeclass_assumptions

section covariant_lt
variables [has_add A] [partial_order A] [covariant_class A A (+) (<)] {a t b : A} {f g : A →₀ R}

/--  The "top" element of `finsupp.single a r * f`  is the product of `r` and
the "top" element of `f`.  Here, "top" is simply an upper bound for the elements
of the support of `f` (e.g. the product is `0` if "top" is not a maximum).

The corresponding statement for a general product `f * g` is `add_monoid_algebra.mul_apply_of_le`.
It is proved with a further `covariant_class` assumption. -/
lemma single_mul_apply_of_le (r : R) (ft : ∀ a ∈ f.support, a ≤ t) :
  (finsupp.single a r * f : add_monoid_algebra R A) (a + t) = r * f t :=
begin
  classical,
  nth_rewrite 0 ← f.erase_add_single t,
  rw [mul_add, single_mul_single, finsupp.add_apply, finsupp.single_eq_same],
  convert zero_add _,
  refine finsupp.not_mem_support_iff.mp (λ h, _),
  refine not_not.mpr ((support_mul (finsupp.single a r) (f.erase t)) h) _,
  simp only [finsupp.mem_support_single, finset.mem_bUnion, ne.def, finset.mem_singleton,
    exists_prop, not_exists, not_and, and_imp, forall_eq, finsupp.support_erase],
  intros _ x xs,
  refine (add_lt_add_left (with_bot.coe_lt_coe.mp _) _).ne',
  refine with_bot.coe_lt_coe.mpr ((ft _ (finset.mem_of_mem_erase xs)).lt_of_ne _),
  exact finset.ne_of_mem_erase xs,
end

/--  The "bottom" element of `finsupp.single a r * f`  is the product of `r` and
the "bottom" element of `f`.  Here, "bottom" is simply a lower bound for the elements
of the support of `f` (e.g. the product is `0` if "bottom" is not a minimum).

The corresponding statement for a general product `f * g` is `add_monoid_algebra.mul_apply_of_le'`.
It is proved with a further `covariant_class` assumption. -/
lemma single_mul_apply_of_le' (r : R) (fb : ∀ a ∈ f.support, b ≤ a) :
  (finsupp.single a r * f : add_monoid_algebra R A) (a + b) = r * f b :=
@single_mul_apply_of_le _ Aᵒᵈ _ _ _ _ _ _ _ _ fb

variables [covariant_class A A (function.swap (+)) (<)]

/--  The "top" element of `f * g`  is the product of the "top" elements of `f` and of `g`.
Here, "top" is simply an upper bound for the elements of the support of the corresponding
polynomial (e.g. the product is `0` if "top" is not a maximum). -/
lemma mul_apply_of_le (fa : ∀ i ∈ f.support, i ≤ a) (gt : ∀ i ∈ g.support, i ≤ t) :
  (f * g : add_monoid_algebra R A) (a + t) = f a * g t :=
begin
  classical,
  nth_rewrite 0 ← f.erase_add_single a,
  rw [add_mul, finsupp.add_apply, single_mul_apply_of_le _ gt],
  convert zero_add _,
  refine finsupp.not_mem_support_iff.mp (λ h, _),
  refine not_not.mpr ((support_mul _ g) h) _,
  simp only [finsupp.support_erase, finset.mem_bUnion, finset.mem_erase, ne.def,
    finset.mem_singleton, exists_prop, not_exists, not_and, and_imp],
  haveI : covariant_class A A (+) (≤) := has_add.to_covariant_class_left A,
  exact λ x xa xf y yg, (add_lt_add_of_lt_of_le ((fa _ xf).lt_of_ne xa) (gt _ yg)).ne',
end

/--  The "bottom" element of `f * g`  is the product of the "bottom" elements of `f` and of `g`.
Here, "bottom" is simply a lower bound for the elements of the support of the corresponding
polynomial (e.g. the product is `0` if "bottom" is not a minimum). -/
lemma mul_apply_of_le' (fa : ∀ i ∈ f.support, a ≤ i) (gb : ∀ i ∈ g.support, b ≤ i) :
  (f * g : add_monoid_algebra R A) (a + b) = f a * g b :=
@mul_apply_of_le _ Aᵒᵈ _ _ _ _ _ _ _ _ _ fa gb

lemma mul_apply_eq_zero_of_lt (fa : ∀ i ∈ f.support, a ≤ i) (gb : ∀ i ∈ g.support, b < i) :
  (f * g : add_monoid_algebra R A) (a + b) = 0 :=
begin
  rw mul_apply_of_le' fa (λ x hx, (gb _ hx).le),
  convert mul_zero _,
  exact finsupp.not_mem_support_iff.mp (λ bg, (lt_irrefl b (gb b bg)).elim),
end

end covariant_lt

variables [no_zero_divisors R] [has_add A] [linear_order A] [covariant_class A A (+) (<)]
  [covariant_class A A (function.swap (+)) (<)]

protected lemma no_zero_divisors : no_zero_divisors (add_monoid_algebra R A) :=
begin
  refine ⟨λ f g fg, _⟩,
  contrapose! fg,
  apply_fun (λ x : add_monoid_algebra R A, x (f.support.max' (finsupp.support_nonempty_iff.mpr fg.1)
    + g.support.max' (finsupp.support_nonempty_iff.mpr fg.2))),
  simp only [finsupp.coe_zero, pi.zero_apply],
  rw mul_apply_of_le;
  try { exact finset.le_max' _ },
  refine mul_ne_zero_iff.mpr ⟨_, _⟩;
  exact finsupp.mem_support_iff.mp (finset.max'_mem _ _),
end

end add_monoid_algebra
