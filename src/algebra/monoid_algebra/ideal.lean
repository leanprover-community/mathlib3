/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import algebra.monoid_algebra.division
import ring_theory.ideal.basic

/-!
# Lemmas about ideals of `monoid_algebra` and `add_monoid_algebra`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {k A G : Type*}

/-- If `x` belongs to the ideal generated by generators in `s`, then every element of the support of
`x` factors through an element of `s`.

We could spell `∃ d, m = d * m` as `mul_opposite.op m' ∣ mul_opposite.op m` but this would be worse.
-/
lemma monoid_algebra.mem_ideal_span_of_image
  [monoid G] [semiring k] {s : set G} {x : monoid_algebra k G} :
  x ∈ ideal.span (monoid_algebra.of k G '' s) ↔ ∀ m ∈ x.support, ∃ m' ∈ s, ∃ d, m = d * m' :=
begin
  let RHS : ideal (monoid_algebra k G) :=
  { carrier := {p | ∀ (m : G), m ∈ p.support → ∃ m' ∈ s, ∃ d, m = d * m'},
    add_mem' := λ x y hx hy m hm, by classical;
      exact (finset.mem_union.1 $ finsupp.support_add hm).elim (hx m) (hy m),
    zero_mem' := λ m hm, by cases hm,
    smul_mem' := λ x y hy m hm, begin
      replace hm := finset.mem_bUnion.mp (finsupp.support_sum hm),
      obtain ⟨xm, hxm, hm⟩ := hm,
      replace hm := finset.mem_bUnion.mp (finsupp.support_sum hm),
      obtain ⟨ym, hym, hm⟩ := hm,
      replace hm := finset.mem_singleton.mp (finsupp.support_single_subset hm),
      obtain rfl := hm,
      refine (hy _ hym).imp (λ sm, Exists.imp $ λ hsm, _),
      rintros ⟨d, rfl⟩,
      exact ⟨xm * d, (mul_assoc _ _ _).symm⟩,
    end },
  change _ ↔ x ∈ RHS,
  split,
  { revert x,
    refine ideal.span_le.2 _,
    rintro _ ⟨i, hi, rfl⟩ m hm,
    refine ⟨_, hi, 1, _⟩,
    obtain rfl := finset.mem_singleton.mp (finsupp.support_single_subset hm),
    exact (one_mul _).symm },
  { intros hx,
    rw ←finsupp.sum_single x,
    apply ideal.sum_mem _ (λ i hi, _),
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi,
    convert ideal.mul_mem_left _ (id $ finsupp.single d2 $ (x (d2 * d)) : monoid_algebra k G) _,
    swap 3,
    refine ideal.subset_span ⟨_, hd, rfl⟩,
    rw [id.def, monoid_algebra.of_apply, monoid_algebra.single_mul_single, mul_one] },
end

/-- If `x` belongs to the ideal generated by generators in `s`, then every element of the support of
`x` factors additively through an element of `s`.
-/
lemma add_monoid_algebra.mem_ideal_span_of'_image
  [add_monoid A] [semiring k] {s : set A} {x : add_monoid_algebra k A} :
  x ∈ ideal.span (add_monoid_algebra.of' k A '' s) ↔ ∀ m ∈ x.support, ∃ m' ∈ s, ∃ d, m = d + m' :=
@monoid_algebra.mem_ideal_span_of_image k (multiplicative A) _ _ _ _
