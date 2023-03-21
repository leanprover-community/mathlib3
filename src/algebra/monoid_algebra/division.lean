/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra.basic
import data.finsupp.order

/-!
# Division of `add_monoid_algebra` by monomials

This file is most important for when `G = ℕ` (polynomials) or `G = σ →₀ ℕ` (multivariate
polynomials).

In order to apply in maximal generality (such as for `laurent_polynomial`s), this uses
`∃ d, g' = g + d` in many places instead of `g ≤ g'`.

## Main definitions

* `add_monoid_algebra.div_of g x`: divides `x` by the monomial `add_monoid_algebra.of k G g`
* `add_monoid_algebra.mod_of g x`: the remainder upon dividing `x` by the monomial
  `add_monoid_algebra.of k G g`.

## Main results

* `add_monoid_algebra.div_of_add_mod_of`, `add_monoid_algebra.mod_of_add_div_of`: `div_of` and
  `mod_of` are well-behaved as quotient and remainder operators.

## Implementation notes

`∃ d, g' = g + d` is used as opposed to some other permutation up to commutativity in order to match
the definition of `semigroup_has_dvd`. The results in this file could be duplicated for
`monoid_algebra` by using `g ∣ g'`, but this can't be done automatically, and in any case is not
likely to be very useful.

-/


variables {k G : Type*} [semiring k]

namespace add_monoid_algebra

section
variables [add_cancel_comm_monoid G]

/-- Divide by `of' k G g`, discarding terms not divisible by this. -/
noncomputable def div_of (g : G) : add_monoid_algebra k G →+ add_monoid_algebra k G :=
@finsupp.comap_domain.add_monoid_hom _ _ _ _ ((+) g)
  (add_right_injective g)

@[simp] lemma div_of_apply (g : G) (x : add_monoid_algebra k G) (g' : G) :
  div_of g x g' = x (g + g') := rfl

@[simp] lemma support_div_of (g : G) (x : add_monoid_algebra k G)  :
  (div_of g x).support = x.support.preimage ((+) g)
    (function.injective.inj_on
      (add_right_injective g) _) := rfl

lemma div_of_zero (x : add_monoid_algebra k G) : div_of 0 x = x :=
by { ext, simp only [add_monoid_algebra.div_of_apply, zero_add] }

lemma div_of_add (x : add_monoid_algebra k G) (a b : G) :
  div_of (a + b) x = div_of b (div_of a x) :=
by { ext, simp only [add_monoid_algebra.div_of_apply, add_assoc] }

lemma div_of_of'_mul (a : G) (x : add_monoid_algebra k G) :
  div_of a (of' k G a * x) = x :=
begin
  ext b,
  rw [add_monoid_algebra.div_of_apply, of'_apply, single_mul_apply_aux, one_mul],
  intro c,
  exact add_right_inj _,
end

lemma div_of_mul_of' (a : G) (x : add_monoid_algebra k G) :
  div_of a (x * of' k G a) = x :=
begin
  ext b,
  rw [add_monoid_algebra.div_of_apply, of'_apply, mul_single_apply_aux, mul_one],
  intro c,
  rw add_comm,
  exact add_right_inj _,
end

lemma div_of_of' (a : G) : div_of a (of' k G a) = 1 :=
by simpa only [one_mul] using div_of_mul_of' a (1 : add_monoid_algebra k G)

/-- The remainder upon division by `of' k G g`. -/
noncomputable def mod_of (g : G) (x : add_monoid_algebra k G) : add_monoid_algebra k G :=
x.filter (λ g₁, ¬∃ g₂, g₁ = g + g₂)

@[simp] lemma mod_of_apply_of_not_exists_add {g : G} (x : add_monoid_algebra k G) {g' : G}
  (h : ¬∃ d, g' = g + d):
  mod_of g x g' = x g' :=
finsupp.filter_apply_pos _ _ h

@[simp] lemma mod_of_apply_of_exists_add {g : G} (x : add_monoid_algebra k G) {g' : G}
  (h : ∃ d, g' = g + d):
  mod_of g x g' = 0 :=
finsupp.filter_apply_neg _ _ $ by rwa [not_not]

@[simp] lemma mod_of_apply_add {g : G} (x : add_monoid_algebra k G) (d : G) :
  mod_of g x (d + g) = 0 :=
mod_of_apply_of_exists_add _ ⟨_, add_comm _ _⟩

@[simp] lemma mod_of_apply_add' {g : G} (x : add_monoid_algebra k G) (d : G) :
  mod_of g x (g + d) = 0 :=
mod_of_apply_of_exists_add _ ⟨_, rfl⟩

lemma mod_of_of'_mul (g : G) (x : add_monoid_algebra k G) :
  mod_of g (of' k G g * x) = 0 :=
begin
  ext g',
  rw finsupp.zero_apply,
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d),
  { rw mod_of_apply_add' },
  { rw [mod_of_apply_of_not_exists_add _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h] },
end

lemma mod_of_mul_of' (g : G) (x : add_monoid_algebra k G):
  mod_of g (x * of' k G g) = 0 :=
begin
  ext g',
  rw finsupp.zero_apply,
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d),
  { rw mod_of_apply_add' },
  { rw [mod_of_apply_of_not_exists_add _ h, of'_apply, mul_single_apply_of_not_exists_add],
    simpa only [add_comm] using h },
end

lemma mod_of_of' (g : G) : mod_of g (of' k G g) = 0 :=
by simpa only [one_mul] using mod_of_mul_of' g (1 : add_monoid_algebra k G)

lemma div_of_add_mod_of (x : add_monoid_algebra k G) (g : G) :
  of' k G g * div_of g x + mod_of g x = x :=
begin
  ext g',
  simp_rw [finsupp.add_apply],
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d),
  swap,
  { rw [mod_of_apply_of_not_exists_add _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h,
      zero_add] },
  { rw [mod_of_apply_add', add_zero],
    rw [of'_apply, single_mul_apply_aux _ _ _, one_mul, div_of_apply],
    intro a,
    exact add_right_inj _ }
end

lemma mod_of_add_div_of (x : add_monoid_algebra k G) (g : G) :
  mod_of g x + of' k G g * div_of g x = x :=
by rw [add_comm, div_of_add_mod_of]

end

end add_monoid_algebra
