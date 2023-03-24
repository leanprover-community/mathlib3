/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.support

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

* `no_zero_divisors.bi_ordered` shows that if `R` is a semiring `R` with no non-zero
  zero-divisors, `A` has an addition, a linear order and both addition on the left and addition
  on the right are strictly monotone functions,
  then `add_monoid_algebra R A` has no non-zero zero-divisors.

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.

###  Remarks

To prove `no_zero_divisors.bi_ordered`,
we use `covariant_class` assumptions on `A`.  In combination with `linear_order A`, these
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

/--  The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
lemma mul_apply_add_eq_mul_of_forall_ne [has_add A]
  {f g : add_monoid_algebra R A} {a0 b0 : A}
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

section covariant_lt
variables [has_add A] [partial_order A] [covariant_class A A (+) (<)] {a t b : A} {f g : A →₀ R}

/--  The "top" element of `finsupp.single a r * f`  is the product of `r` and
the "top" element of `f`.  Here, "top" is simply an upper bound for the elements
of the support of `f` (e.g. the product is `0` if "top" is not a maximum).

The corresponding statement for a general product `f * g` is `add_monoid_algebra.mul_apply_of_le`.
It is proved with a further `covariant_class` assumption. -/
lemma single_mul_apply_of_le (r : R) (ft : ∀ a ∈ f.support, a ≤ t) :
  (single a r * f : add_monoid_algebra R A) (a + t) = r * f t :=
begin
  classical,
  nth_rewrite 0 ← f.erase_add_single t,
  rw [mul_add, single_mul_single, add_apply, single_eq_same],
  convert zero_add _,
  refine not_mem_support_iff.mp (λ h, _),
  refine not_not.mpr ((support_mul (single a r) (f.erase t)) h) _,
  simp only [mem_support_single, finset.mem_bUnion, ne.def, finset.mem_singleton,
    exists_prop, not_exists, not_and, and_imp, forall_eq, support_erase],
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
  (single a r * f : add_monoid_algebra R A) (a + b) = r * f b :=
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
  rw [add_mul, add_apply, single_mul_apply_of_le _ gt],
  convert zero_add _,
  refine not_mem_support_iff.mp (λ h, _),
  refine not_not.mpr ((support_mul _ g) h) _,
  simp only [support_erase, finset.mem_bUnion, finset.mem_erase, ne.def,
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
  exact not_mem_support_iff.mp (λ bg, (lt_irrefl b (gb b bg)).elim),
end

end covariant_lt

variables [no_zero_divisors R] [has_add A] [linear_order A] [covariant_class A A (+) (<)]
  [covariant_class A A (function.swap (+)) (<)]

protected lemma no_zero_divisors.bi_ordered : no_zero_divisors (add_monoid_algebra R A) :=
begin
  refine ⟨λ f g fg, _⟩,
  contrapose! fg,
  apply_fun (λ x : add_monoid_algebra R A, x (f.support.max' (support_nonempty_iff.mpr fg.1)
    + g.support.max' (support_nonempty_iff.mpr fg.2))),
  simp only [coe_zero, pi.zero_apply],
  rw mul_apply_of_le;
  try { exact finset.le_max' _ },
  refine mul_ne_zero_iff.mpr ⟨_, _⟩;
  exact mem_support_iff.mp (finset.max'_mem _ _),
end

end add_monoid_algebra
