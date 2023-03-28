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

* `add_monoid_algebra.div_of x g`: divides `x` by the monomial `add_monoid_algebra.of k G g`
* `add_monoid_algebra.mod_of x g`: the remainder upon dividing `x` by the monomial
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
noncomputable def div_of (x : add_monoid_algebra k G) (g : G) : add_monoid_algebra k G :=
-- note: comapping by `+ g` has the effect of subtracting `g` from every element in the support, and
-- discarding the elements of the support from which `g` can't be subtracted. If `G` is an additive
-- group, such as `ℤ` when used for `laurent_polynomial`, then no discarding occurs.
@finsupp.comap_domain.add_monoid_hom _ _ _ _ ((+) g)
  (add_right_injective g) x

local infix ` /ᵒᶠ `:70 := div_of

@[simp] lemma div_of_apply (g : G) (x : add_monoid_algebra k G) (g' : G) :
  (x /ᵒᶠ g) g' = x (g + g') := rfl

@[simp] lemma support_div_of (g : G) (x : add_monoid_algebra k G)  :
  (x /ᵒᶠ g).support = x.support.preimage ((+) g)
    (function.injective.inj_on
      (add_right_injective g) _) := rfl

@[simp] lemma zero_div_of (g : G) : (0 : add_monoid_algebra k G) /ᵒᶠ g = 0 :=
map_zero _

@[simp] lemma div_of_zero (x : add_monoid_algebra k G) : x /ᵒᶠ 0 = x :=
by { ext, simp only [add_monoid_algebra.div_of_apply, zero_add] }

lemma add_div_of (x y : add_monoid_algebra k G) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g :=
map_add _ _ _

lemma div_of_add (x : add_monoid_algebra k G) (a b : G) :
  x /ᵒᶠ (a + b) = (x /ᵒᶠ a) /ᵒᶠ b :=
by { ext, simp only [add_monoid_algebra.div_of_apply, add_assoc] }

/-- A bundled version of `add_monoid_algebra.div_of`. -/
@[simps]
noncomputable def div_of_hom : multiplicative G →* add_monoid.End (add_monoid_algebra k G) :=
{ to_fun := λ g,
  { to_fun := λ x, div_of x g.to_add,
    map_zero' := zero_div_of _,
    map_add' := λ x y, add_div_of x y g.to_add },
  map_one' := add_monoid_hom.ext div_of_zero,
  map_mul' := λ g₁ g₂, add_monoid_hom.ext $ λ x,
    (congr_arg _ (add_comm g₁.to_add g₂.to_add)).trans  (div_of_add _ _ _) }

lemma of'_mul_div_of (a : G) (x : add_monoid_algebra k G) :
  (of' k G a * x) /ᵒᶠ a = x :=
begin
  ext b,
  rw [add_monoid_algebra.div_of_apply, of'_apply, single_mul_apply_aux, one_mul],
  intro c,
  exact add_right_inj _,
end

lemma mul_of'_div_of (x : add_monoid_algebra k G) (a : G) :
  (x * of' k G a) /ᵒᶠ a = x :=
begin
  ext b,
  rw [add_monoid_algebra.div_of_apply, of'_apply, mul_single_apply_aux, mul_one],
  intro c,
  rw add_comm,
  exact add_right_inj _,
end

lemma of'_div_of (a : G) : (of' k G a) /ᵒᶠ a = 1 :=
by simpa only [one_mul] using mul_of'_div_of (1 : add_monoid_algebra k G) a

/-- The remainder upon division by `of' k G g`. -/
noncomputable def mod_of (x : add_monoid_algebra k G) (g : G) : add_monoid_algebra k G :=
x.filter (λ g₁, ¬∃ g₂, g₁ = g + g₂)

local infix ` %ᵒᶠ `:70 := mod_of

@[simp] lemma mod_of_apply_of_not_exists_add (x : add_monoid_algebra k G) (g : G) (g' : G)
  (h : ¬∃ d, g' = g + d) :
  (x %ᵒᶠ g) g' = x g' :=
finsupp.filter_apply_pos _ _ h

@[simp] lemma mod_of_apply_of_exists_add (x : add_monoid_algebra k G) (g : G) (g' : G)
  (h : ∃ d, g' = g + d) :
  (x %ᵒᶠ g) g' = 0 :=
finsupp.filter_apply_neg _ _ $ by rwa [not_not]

@[simp] lemma mod_of_apply_add_self (x : add_monoid_algebra k G) (g : G) (d : G) :
  (x %ᵒᶠ g) (d + g) = 0 :=
mod_of_apply_of_exists_add _ _ _ ⟨_, add_comm _ _⟩

@[simp] lemma mod_of_apply_self_add (x : add_monoid_algebra k G) (g : G) (d : G) :
  (x %ᵒᶠ g) (g + d) = 0 :=
mod_of_apply_of_exists_add _ _ _ ⟨_, rfl⟩

lemma of'_mul_mod_of (g : G) (x : add_monoid_algebra k G) :
  (of' k G g * x) %ᵒᶠ g = 0 :=
begin
  ext g',
  rw finsupp.zero_apply,
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d),
  { rw mod_of_apply_self_add },
  { rw [mod_of_apply_of_not_exists_add _ _ _ h, of'_apply,
      single_mul_apply_of_not_exists_add _ _ h] },
end

lemma mul_of'_mod_of (x : add_monoid_algebra k G) (g : G) :
  (x * of' k G g) %ᵒᶠ g = 0 :=
begin
  ext g',
  rw finsupp.zero_apply,
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d),
  { rw mod_of_apply_self_add },
  { rw [mod_of_apply_of_not_exists_add _ _ _ h, of'_apply, mul_single_apply_of_not_exists_add],
    simpa only [add_comm] using h },
end

lemma of'_mod_of (g : G) : of' k G g %ᵒᶠ g = 0 :=
by simpa only [one_mul] using mul_of'_mod_of (1 : add_monoid_algebra k G) g

lemma div_of_add_mod_of (x : add_monoid_algebra k G) (g : G) :
  of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x :=
begin
  ext g',
  simp_rw [finsupp.add_apply],
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d),
  swap,
  { rw [mod_of_apply_of_not_exists_add _ _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h,
      zero_add] },
  { rw [mod_of_apply_self_add, add_zero],
    rw [of'_apply, single_mul_apply_aux _ _ _, one_mul, div_of_apply],
    intro a,
    exact add_right_inj _ }
end

lemma mod_of_add_div_of (x : add_monoid_algebra k G) (g : G) :
  x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x :=
by rw [add_comm, div_of_add_mod_of]

lemma of'_dvd_iff_mod_of_eq_zero {x : add_monoid_algebra k G} {g : G} :
  of' k G g ∣ x ↔ x %ᵒᶠ g = 0 :=
begin
  split,
  { rintro ⟨x, rfl⟩,
    rw of'_mul_mod_of },
  { intro h,
    rw [←div_of_add_mod_of x g, h, add_zero],
    exact dvd_mul_right _ _ },
end

end

end add_monoid_algebra
