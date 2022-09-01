/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import algebra.order.field

/-!
# Absolute values

This file defines a bundled type of absolute values `absolute_value R S`.

## Main definitions

 * `absolute_value R S` is the type of absolute values on `R` mapping to `S`.
 * `absolute_value.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
 * `absolute_value.to_monoid_with_zero_hom`: absolute values mapping to a
   linear ordered field preserve `0`, `*` and `1`

## Implementation details

`absolute_value` has two instances of `monoid_with_zero_hom_class`; this is due to the fact that
there is no `cancel_semiring` structure.

-/

/-- `absolute_value R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle equality. -/
structure absolute_value (R S : Type*) [semiring R] [ordered_semiring S]
  extends R →ₙ* S :=
(nonneg' : ∀ x, 0 ≤ to_fun x)
(eq_zero' : ∀ x, to_fun x = 0 ↔ x = 0)
(add_le' : ∀ x y, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace absolute_value

attribute [nolint doc_blame] absolute_value.to_mul_hom

section ordered_semiring

section semiring

variables {R S : Type*} [semiring R] [ordered_semiring S] (abv : absolute_value R S)

instance fun_like : fun_like (absolute_value R S) R (λ _, S) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' } }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (absolute_value R S) (λ f, R → S) := fun_like.has_coe_to_fun

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (f : absolute_value R S) : R → S := coe_fn f

initialize_simps_projections absolute_value (to_mul_hom_to_fun → apply, -to_mul_hom)

instance mul_hom_class : mul_hom_class (absolute_value R S) R S :=
{ map_mul := λ f, f.map_mul',
  ..absolute_value.fun_like }

instance zero_hom_class : zero_hom_class (absolute_value R S) R S :=
{ map_zero := λ f, (f.eq_zero' 0).mpr rfl,
  ..absolute_value.fun_like }

@[simp] lemma coe_to_mul_hom : ⇑abv.to_mul_hom = abv := rfl

protected theorem nonneg (x : R) : 0 ≤ abv x := abv.nonneg' x
@[simp] protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 := abv.eq_zero' x
protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y := abv.add_le' x y

protected theorem pos {x : R} (hx : x ≠ 0) : 0 < abv x :=
(abv.nonneg x).lt_of_ne' $ mt abv.eq_zero.mp hx

@[simp] protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
⟨λ h₁, mt abv.eq_zero.mpr h₁.ne', abv.pos⟩

protected theorem ne_zero {x : R} (hx : x ≠ 0) : abv x ≠ 0 := (abv.pos hx).ne'

theorem map_one_of_is_regular (h : is_left_regular (abv 1)) : abv 1 = 1 :=
h $ by simp [←map_mul]

end semiring

section ring

variables {R S : Type*} [ring R] [ordered_semiring S] (abv : absolute_value R S)

protected lemma sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) :=
by simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)

@[simp] lemma map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
abv.eq_zero.trans sub_eq_zero

end ring

end ordered_semiring

section ordered_ring

section semiring

section is_domain

-- all of these are true for `no_zero_divisors S`; but it doesn't work smoothly with the
-- `is_domain`/`cancel_monoid_with_zero` API
variables {R S : Type*} [semiring R] [ordered_ring S] (abv : absolute_value R S)
variables [is_domain S] [nontrivial R]

-- this is the best possible; the ring `ℤ[X] / (X ^ 2 - X)` with the lexicographic order
-- allows an absolute value with `f 1 = X`.
instance : monoid_with_zero_hom_class (absolute_value R S) R S :=
{ map_one := λ f, f.map_one_of_is_regular $ (is_regular_of_ne_zero $ f.ne_zero one_ne_zero).left,
  ..absolute_value.zero_hom_class,
  ..absolute_value.mul_hom_class }

end is_domain

end semiring

section ring

variables {R S : Type*} [ring R] [ordered_ring S] (abv : absolute_value R S)

protected lemma le_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
sub_le_iff_le_add.2 $ by simpa using abv.add_le (a - b) b

end ring

end ordered_ring

section ordered_comm_ring

variables {R S : Type*} [ring R] [ordered_comm_ring S] (abv : absolute_value R S)
variables [no_zero_divisors S]

@[simp] protected theorem map_neg (a : R) : abv (-a) = abv a :=
begin
  rcases eq_or_ne a 0 with rfl | ha, { simp },
  refine (mul_self_eq_mul_self_iff.mp (by rw [← map_mul, neg_mul_neg, map_mul])).resolve_right _,
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'
end

protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) :=
by rw [← neg_sub, abv.map_neg]

end ordered_comm_ring

section linear_ordered_ring

variables {R S : Type*} [semiring R] [linear_ordered_ring S] (abv : absolute_value R S)

/-- `absolute_value.abs` is `abs` as a bundled `absolute_value`. -/
@[simps] protected def abs : absolute_value S S :=
{ to_fun := abs,
  nonneg' := abs_nonneg,
  eq_zero' := λ _, abs_eq_zero,
  add_le' := abs_add,
  map_mul' := abs_mul }

instance : inhabited (absolute_value S S) := ⟨absolute_value.abs⟩

end linear_ordered_ring

section linear_ordered_comm_ring

variables {R S : Type*} [ring R] [linear_ordered_comm_ring S] (abv : absolute_value R S)

lemma abs_abv_sub_le_abv_sub (a b : R) :
  abs (abv a - abv b) ≤ abv (a - b) :=
abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw abv.map_sub; apply abv.le_sub⟩

end linear_ordered_comm_ring

section linear_ordered_semifield

section semiring

variables {R S : Type*} [semiring R] [linear_ordered_semifield S] (abv : absolute_value R S)

-- this is needed as there is no common ancestor of `linear_ordered_semifield` and an integral
-- domain; the needed typeclass would be something akin to a `cancel_semiring`. Allows absolute
-- values on types such as `ℝ≥0` to have sensible coercions.
instance monoid_with_zero_hom_class' [nontrivial R] :
  monoid_with_zero_hom_class (absolute_value R S) R S :=
{ map_one := λ f, f.map_one_of_is_regular $ (is_regular_of_ne_zero $ f.ne_zero one_ne_zero).left,
  ..absolute_value.mul_hom_class,
  ..absolute_value.zero_hom_class }

end semiring

section division_semiring

variables {R S : Type*} [division_semiring R] [linear_ordered_semifield S]
          (abv : absolute_value R S)

protected theorem map_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ := map_inv₀ abv a
protected theorem map_div (a b : R) : abv (a / b) = abv a / abv b := map_div₀ abv a b

end division_semiring

end linear_ordered_semifield

section linear_ordered_field

variables {R S : Type*} [semiring R] [nontrivial R] [linear_ordered_field S]

-- ensure that the two `monoid_with_zero_hom_class` instances are defeq.
example : @absolute_value.monoid_with_zero_hom_class R S _ _ _ _ =
          absolute_value.monoid_with_zero_hom_class' :=
rfl

end linear_ordered_field

end absolute_value
