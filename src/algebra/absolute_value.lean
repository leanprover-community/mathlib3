/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import algebra.ordered_field

/-!
# Absolute values

This file defines a bundled type of absolute values `absolute_value R S`.

## Main definitions

 * `absolute_value R S` is the type of absolute values on `R` mapping to `S`.
 * `absolute_value.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
 * `absolute_value.to_monoid_with_zero_hom`: absolute values mapping to a
   linear ordered field preserve `0`, `*` and `1`
-/

set_option old_structure_cmd true

/-- `absolute_value R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle equality. -/
structure absolute_value (R S : Type*) [semiring R] [ordered_semiring S]
  extends mul_hom R S :=
(nonneg' : ∀ x, 0 ≤ to_fun x)
(eq_zero' : ∀ x, to_fun x = 0 ↔ x = 0)
(add_le' : ∀ x y, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace absolute_value

attribute [nolint doc_blame] absolute_value.to_mul_hom

initialize_simps_projections absolute_value (to_fun → apply)

section ordered_semiring

variables {R S : Type*} [semiring R] [ordered_semiring S] (abv : absolute_value R S)

instance : has_coe_to_fun (absolute_value R S) := ⟨λ f, R → S, λ f, f.to_fun⟩

@[simp] lemma coe_to_mul_hom : ⇑abv.to_mul_hom = abv := rfl

protected theorem nonneg (x : R) : 0 ≤ abv x := abv.nonneg' x
@[simp] protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 := abv.eq_zero' x
protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y := abv.add_le' x y
@[simp] protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y := abv.map_mul' x y

protected theorem pos {x : R} (hx : x ≠ 0) : 0 < abv x :=
lt_of_le_of_ne (abv.nonneg x) (ne.symm $ mt abv.eq_zero.mp hx)

@[simp] protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
⟨λ h₁, mt abv.eq_zero.mpr h₁.ne', abv.pos⟩

protected theorem ne_zero {x : R} (hx : x ≠ 0) : abv x ≠ 0 := (abv.pos hx).ne'

@[simp] protected theorem map_zero : abv 0 = 0 := abv.eq_zero.2 rfl

end ordered_semiring

section ordered_ring

variables {R S : Type*} [ring R] [ordered_ring S] (abv : absolute_value R S)

protected lemma sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) :=
by simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)

protected lemma le_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
sub_le_iff_le_add.2 $ by simpa using abv.add_le (a - b) b

end ordered_ring

section linear_ordered_ring

variables {R S : Type*} [semiring R] [linear_ordered_ring S] (abv : absolute_value R S)

/-- `absolute_value.abs` is `abs` as a bundled `absolute_value`. -/
@[simps]
protected def abs : absolute_value S S :=
{ to_fun := abs,
  nonneg' := abs_nonneg,
  eq_zero' := λ _, abs_eq_zero,
  add_le' := abs_add,
  map_mul' := abs_mul }

instance : inhabited (absolute_value S S) := ⟨absolute_value.abs⟩

end linear_ordered_ring

section linear_ordered_field

section semiring

variables {R S : Type*} [semiring R] [linear_ordered_field S] (abv : absolute_value R S)

variables [nontrivial R]

@[simp] protected theorem map_one : abv 1 = 1 :=
(mul_right_inj' $ mt abv.eq_zero.1 one_ne_zero).1 $
by rw [← abv.map_mul, mul_one, mul_one]

/-- Absolute values from a nontrivial `R` to a linear ordered field preserve `*`, `0` and `1`. -/
def to_monoid_with_zero_hom : monoid_with_zero_hom R S :=
{ to_fun := abv,
  map_zero' := abv.map_zero,
  map_one' := abv.map_one,
  .. abv }

@[simp] lemma coe_to_monoid_with_zero_hom : ⇑abv.to_monoid_with_zero_hom = abv := rfl

/-- Absolute values from a nontrivial `R` to a linear ordered field preserve `*` and `1`. -/
def to_monoid_hom : monoid_hom R S :=
{ to_fun := abv,
  map_one' := abv.map_one,
  .. abv }

@[simp] lemma coe_to_monoid_hom : ⇑abv.to_monoid_hom = abv := rfl

@[simp] protected lemma map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
abv.to_monoid_hom.map_pow a n

end semiring

section ring

variables {R S : Type*} [ring R] [linear_ordered_field S] (abv : absolute_value R S)

@[simp] protected theorem map_neg (a : R) : abv (-a) = abv a :=
by rw [← mul_self_inj_of_nonneg (abv.nonneg _) (abv.nonneg _),
       ← abv.map_mul]; simp

protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) :=
by rw [← neg_sub, abv.map_neg]

lemma abs_abv_sub_le_abv_sub (a b : R) :
  abs (abv a - abv b) ≤ abv (a - b) :=
abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw abv.map_sub; apply abv.le_sub⟩

end ring

section field

variables {R S : Type*} [field R] [linear_ordered_field S] (abv : absolute_value R S)

@[simp] protected theorem map_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
abv.to_monoid_with_zero_hom.map_inv' a

@[simp] protected theorem map_div (a b : R) : abv (a / b) = abv a / abv b :=
abv.to_monoid_with_zero_hom.map_div a b

end field

end linear_ordered_field

end absolute_value
