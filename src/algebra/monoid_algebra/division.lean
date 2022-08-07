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

-/


variables {k G : Type*} [semiring k]

namespace add_monoid_algebra

section
variables [add_cancel_monoid G]

/-- Divide by `of' k G g`, discarding terms not divisible by this. -/
noncomputable def div_of (g : G) : add_monoid_algebra k G →+ add_monoid_algebra k G :=
finsupp.comap_domain.add_monoid_hom (add_right_injective g)

@[simp] lemma div_of_apply (g : G) (x : add_monoid_algebra k G) (g' : G) :
  div_of g x g' = x (g + g') := rfl

@[simp] lemma support_div_of (g : G) (x : add_monoid_algebra k G)  :
  (div_of g x).support = x.support.preimage _ ((add_right_injective g).inj_on _) := rfl

lemma div_of_0 (x : add_monoid_algebra k G) : div_of 0 x = x :=
by { ext, simp only [add_monoid_algebra.div_of_apply, zero_add] }

lemma div_of_add (x : add_monoid_algebra k G) (a b : G) :
  div_of (a + b) x = div_of b (div_of a x) :=
by { ext, simp only [add_monoid_algebra.div_of_apply, add_assoc] }

end

section
variables [partial_order G]

/-- The remainder upon division by `of' k G g`. -/
noncomputable def mod_of (g : G) (x : add_monoid_algebra k G) : add_monoid_algebra k G :=
x.filter (λ g', ¬g ≤ g')

@[simp] lemma mod_of_apply_of_not_le {g : G} (x : add_monoid_algebra k G) {g' : G} (h : ¬g ≤ g') :
  mod_of g x g' = x g' :=
finsupp.filter_apply_pos _ _ h

@[simp] lemma mod_of_apply_of_le {g : G} (x : add_monoid_algebra k G) {g' : G} (h : g ≤ g') :
  mod_of g x g' = 0 :=
finsupp.filter_apply_neg _ _ (not_not_intro h)

end

section
variables (G) [canonically_ordered_add_monoid G] [has_sub G] [has_ordered_sub G]
  [contravariant_class G G (+) (≤)]

/-- TODO: move me -/
def canonically_ordered_add_monoid.to_add_cancel_monoid :
  add_cancel_monoid G :=
{ add_left_cancel := λ a b c h, begin
    have := congr_arg (λ x, x - a) h,
    dsimp at this,
    rwa [add_tsub_cancel_left, add_tsub_cancel_left] at this,
  end,
  add_right_cancel := λ a b c h, begin
    have := congr_arg (λ x, x - b) h,
    dsimp at this,
    rwa [add_tsub_cancel_right, add_tsub_cancel_right] at this,
  end,
  ..(by apply_instance : add_monoid G) }

lemma div_of_add_mod_of (x : add_monoid_algebra k G) (g : G) :
  by haveI := canonically_ordered_add_monoid.to_add_cancel_monoid G; exact
  of' k G g * div_of g x + mod_of g x = x :=
begin
  letI := canonically_ordered_add_monoid.to_add_cancel_monoid G,
  ext g',
  simp_rw [finsupp.add_apply],
  by_cases h : g ≤ g',
  swap,
  { classical,
    rw [mod_of_apply_of_not_le _ h, of'_apply, mul_apply, finsupp.sum_single_index],
    swap,
    { simp_rw [finsupp.sum, div_of_apply, zero_mul, if_t_t, finset.sum_const_zero] },
    { simp_rw [finsupp.sum, div_of_apply, support_div_of, one_mul],
      convert zero_add _,
      apply finset.sum_eq_zero,
      simp_rw ite_eq_right_iff,
      rintros g'' hg'' rfl,
      exfalso,
      apply h,
      apply le_add_of_le_of_nonneg le_rfl (zero_le g'') } },
  { rw [mod_of_apply_of_le _ h, add_zero],
    obtain ⟨dg, rfl⟩ := exists_add_of_le h,
    rw [of'_apply, single_mul_apply_aux _ _ _ _ dg, one_mul, div_of_apply],
    intro a,
    exact add_right_inj _ }
end

lemma mod_of_add_div_of (x : add_monoid_algebra k G) (g : G) :
  by haveI := canonically_ordered_add_monoid.to_add_cancel_monoid G; exact
  mod_of g x + of' k G g * div_of g x = x :=
by rw [add_comm, div_of_add_mod_of]

end

end add_monoid_algebra
