/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra.basic
import data.finsupp.order

/-!
# Division of `add_monoid_algebra` by monomials

## Main definitions

* `add_monoid_algebra.div_of g x`: divides `x` by the monomial `add_monoid_algebra.of k G g`
* `add_monoid_algebra.mod_of g x`: the remainder upon dividing `x` by the monomial
  `add_monoid_algebra.of k G g`.

## Main results

* `add_monoid_algebra.div_of_add_mod_of`, `add_monoid_algebra.mod_of_add_div_of`: `div_of` and
  `mod_of` are well-behaved as quotient and remainder operators.

## Implementation notes

This file is most important for when `G = ℕ` (polynomials) or `G = σ →₀ ℕ` (multivariate
polynomials). So as to generalize to both, we require
```lean
[canonically_ordered_add_monoid G] [has_sub G] [has_ordered_sub G] [contravariant_class G G (+) (≤)]
```

-/


variables {k G : Type*} [semiring k]

namespace add_monoid_algebra

section
variables [canonically_ordered_add_monoid G] [has_sub G] [has_ordered_sub G]
  [contravariant_class G G (+) (≤)]

/-- Divide by `of' k G g`, discarding terms not divisible by this. -/
noncomputable def div_of (g : G) : add_monoid_algebra k G →+ add_monoid_algebra k G :=
@finsupp.comap_domain.add_monoid_hom _ _ _ _ ((+) g)
  (by letI := canonically_ordered_add_monoid.to_add_cancel_comm_monoid G;
    exact add_right_injective g)

@[simp] lemma div_of_apply (g : G) (x : add_monoid_algebra k G) (g' : G) :
  div_of g x g' = x (g + g') := rfl

@[simp] lemma support_div_of (g : G) (x : add_monoid_algebra k G)  :
  (div_of g x).support = x.support.preimage ((+) g)
    (function.injective.inj_on
      (by letI := canonically_ordered_add_monoid.to_add_cancel_comm_monoid G;
        exact add_right_injective g) _) := rfl

lemma div_of_zero (x : add_monoid_algebra k G) : div_of 0 x = x :=
by { ext, simp only [add_monoid_algebra.div_of_apply, zero_add] }

lemma div_of_add (x : add_monoid_algebra k G) (a b : G) :
  div_of (a + b) x = div_of b (div_of a x) :=
by { ext, simp only [add_monoid_algebra.div_of_apply, add_assoc] }

@[simp] lemma div_of_of'_mul (a : G) (x : add_monoid_algebra k G) :
  div_of a (of' k G a * x) = x :=
begin
  letI := canonically_ordered_add_monoid.to_add_cancel_comm_monoid G,
  ext b,
  rw [add_monoid_algebra.div_of_apply, of'_apply, single_mul_apply_aux, one_mul],
  intro c,
  exact add_right_inj _,
end

@[simp] lemma div_of_mul_of' (a : G) (x : add_monoid_algebra k G) :
  div_of a (x * of' k G a) = x :=
begin
  letI := canonically_ordered_add_monoid.to_add_cancel_comm_monoid G,
  ext b,
  rw [add_monoid_algebra.div_of_apply, of'_apply, mul_single_apply_aux, mul_one],
  intro c,
  rw add_comm,
  exact add_right_inj _,
end

@[simp] lemma div_of_of' (a : G) : div_of a (of' k G a) = 1 :=
by simpa only [one_mul] using div_of_mul_of' a (1 : add_monoid_algebra k G)

/-- The remainder upon division by `of' k G g`. -/
noncomputable def mod_of (g : G) (x : add_monoid_algebra k G) : add_monoid_algebra k G :=
x.filter (λ g', ¬g ≤ g')

@[simp] lemma mod_of_apply_of_not_le {g : G} (x : add_monoid_algebra k G) {g' : G} (h : ¬g ≤ g') :
  mod_of g x g' = x g' :=
finsupp.filter_apply_pos _ _ h

@[simp] lemma mod_of_apply_of_le {g : G} (x : add_monoid_algebra k G) {g' : G} (h : g ≤ g') :
  mod_of g x g' = 0 :=
finsupp.filter_apply_neg _ _ (not_not_intro h)

lemma single_mul_apply_of_not_le (r : k) {g g' : G} (x : add_monoid_algebra k G) (h : ¬(g ≤ g')):
  (finsupp.single g r * x : add_monoid_algebra k G) g' = 0 :=
begin
  classical,
  rw [mul_apply, finsupp.sum_single_index],
  swap,
  { simp_rw [finsupp.sum, zero_mul, if_t_t, finset.sum_const_zero] },
  { apply finset.sum_eq_zero,
    simp_rw ite_eq_right_iff,
    rintros g'' hg'' rfl,
    exfalso,
    apply h,
    apply le_add_of_le_of_nonneg le_rfl (zero_le g'') }
end

lemma mul_single_apply_of_not_le (r : k) {g g' : G} (x : add_monoid_algebra k G) (h : ¬(g ≤ g')):
  (x * finsupp.single g r : add_monoid_algebra k G) g' = 0 :=
begin
  classical,
  rw [mul_apply, finsupp.sum_comm, finsupp.sum_single_index],
  swap,
  { simp_rw [finsupp.sum, mul_zero, if_t_t, finset.sum_const_zero] },
  { apply finset.sum_eq_zero,
    simp_rw ite_eq_right_iff,
    rintros g'' hg'' rfl,
    exfalso,
    apply h,
    apply le_add_of_nonneg_of_le (zero_le g'') le_rfl }
end

@[simp] lemma mod_of_of'_mul (g : G) (x : add_monoid_algebra k G) :
  mod_of g (of' k G g * x) = 0 :=
begin
  ext g',
  rw finsupp.zero_apply,
  by_cases h: g ≤ g',
  { rw [mod_of_apply_of_le _ h], },
  { rw [mod_of_apply_of_not_le _ h, of'_apply, single_mul_apply_of_not_le _ _ h] },
end

@[simp] lemma mod_of_mul_of' (g : G) (x : add_monoid_algebra k G):
  mod_of g (x * of' k G g) = 0 :=
begin
  ext g',
  rw finsupp.zero_apply,
  by_cases h: g ≤ g',
  { rw [mod_of_apply_of_le _ h], },
  { rw [mod_of_apply_of_not_le _ h, of'_apply, mul_single_apply_of_not_le _ _ h] },
end

@[simp] lemma mod_of_of' (g : G) : mod_of g (of' k G g) = 0 :=
by simpa only [one_mul] using mod_of_mul_of' g (1 : add_monoid_algebra k G)

lemma div_of_add_mod_of (x : add_monoid_algebra k G) (g : G) :
  of' k G g * div_of g x + mod_of g x = x :=
begin
  letI := canonically_ordered_add_monoid.to_add_cancel_comm_monoid G,
  ext g',
  simp_rw [finsupp.add_apply],
  by_cases h : g ≤ g',
  swap,
  { rw [mod_of_apply_of_not_le _ h, of'_apply, single_mul_apply_of_not_le _ _ h, zero_add] },
  { rw [mod_of_apply_of_le _ h, add_zero],
    obtain ⟨dg, rfl⟩ := exists_add_of_le h,
    rw [of'_apply, single_mul_apply_aux _ _ _ _ dg, one_mul, div_of_apply],
    intro a,
    exact add_right_inj _ }
end

lemma mod_of_add_div_of (x : add_monoid_algebra k G) (g : G) :
  by haveI := canonically_ordered_add_monoid.to_add_cancel_comm_monoid G; exact
  mod_of g x + of' k G g * div_of g x = x :=
by rw [add_comm, div_of_add_mod_of]

end

end add_monoid_algebra
