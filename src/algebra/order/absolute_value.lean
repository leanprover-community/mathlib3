/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import algebra.group_with_zero.units.lemmas
import algebra.order.field.defs
import algebra.order.hom.basic
import algebra.order.ring.abs
import algebra.ring.commute
import algebra.ring.regular

/-!
# Absolute values

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a bundled type of absolute values `absolute_value R S`.

## Main definitions

 * `absolute_value R S` is the type of absolute values on `R` mapping to `S`.
 * `absolute_value.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
 * `absolute_value.to_monoid_with_zero_hom`: absolute values mapping to a
   linear ordered field preserve `0`, `*` and `1`
 * `is_absolute_value`: a type class stating that `f : β → α` satisfies the axioms of an abs val
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

instance zero_hom_class : zero_hom_class (absolute_value R S) R S :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_zero := λ f, (f.eq_zero' _).2 rfl }

instance mul_hom_class : mul_hom_class (absolute_value R S) R S :=
{ map_mul := λ f, f.map_mul'
  ..absolute_value.zero_hom_class }

instance nonneg_hom_class : nonneg_hom_class (absolute_value R S) R S :=
{ map_nonneg := λ f, f.nonneg',
  ..absolute_value.zero_hom_class }

instance subadditive_hom_class : subadditive_hom_class (absolute_value R S) R S :=
{ map_add_le_add := λ f, f.add_le',
  ..absolute_value.zero_hom_class }

@[simp] lemma coe_mk (f : R →ₙ* S) {h₁ h₂ h₃} : ((absolute_value.mk f h₁ h₂ h₃) : R → S) = f := rfl

@[ext] lemma ext ⦃f g : absolute_value R S⦄ : (∀ x, f x = g x) → f = g := fun_like.ext _ _

/-- See Note [custom simps projection]. -/
def simps.apply (f : absolute_value R S) : R → S := f

initialize_simps_projections absolute_value (to_mul_hom_to_fun → apply)

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (absolute_value R S) (λ f, R → S) := fun_like.has_coe_to_fun

@[simp] lemma coe_to_mul_hom : ⇑abv.to_mul_hom = abv := rfl

protected theorem nonneg (x : R) : 0 ≤ abv x := abv.nonneg' x
@[simp] protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 := abv.eq_zero' x
protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y := abv.add_le' x y
@[simp] protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y := abv.map_mul' x y

protected theorem ne_zero_iff {x : R} : abv x ≠ 0 ↔ x ≠ 0 := abv.eq_zero.not

protected theorem pos {x : R} (hx : x ≠ 0) : 0 < abv x :=
lt_of_le_of_ne (abv.nonneg x) (ne.symm $ mt abv.eq_zero.mp hx)

@[simp] protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
⟨λ h₁, mt abv.eq_zero.mpr h₁.ne', abv.pos⟩

protected theorem ne_zero {x : R} (hx : x ≠ 0) : abv x ≠ 0 := (abv.pos hx).ne'

theorem map_one_of_is_regular (h : is_left_regular (abv 1)) : abv 1 = 1 :=
h $ by simp [←abv.map_mul]

@[simp] protected theorem map_zero : abv 0 = 0 := abv.eq_zero.2 rfl

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

@[simp] protected theorem map_one : abv 1 = 1 :=
abv.map_one_of_is_regular ((is_regular_of_ne_zero $ abv.ne_zero one_ne_zero).left)

instance : monoid_with_zero_hom_class (absolute_value R S) R S :=
{ map_zero := λ f, f.map_zero,
  map_one := λ f, f.map_one,
  ..absolute_value.mul_hom_class }

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*`, `0` and `1`. -/
def to_monoid_with_zero_hom : R →*₀ S := abv

@[simp] lemma coe_to_monoid_with_zero_hom : ⇑abv.to_monoid_with_zero_hom = abv := rfl

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*` and `1`. -/
def to_monoid_hom : R →* S := abv

@[simp] lemma coe_to_monoid_hom : ⇑abv.to_monoid_hom = abv := rfl

@[simp] protected lemma map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
abv.to_monoid_hom.map_pow a n

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
  by_cases ha : a = 0, { simp [ha] },
  refine (mul_self_eq_mul_self_iff.mp
    (by rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right _,
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'
end

protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) :=
by rw [← neg_sub, abv.map_neg]

end ordered_comm_ring

instance {R S : Type*} [ring R] [ordered_comm_ring S] [nontrivial R] [is_domain S] :
  mul_ring_norm_class (absolute_value R S) R S :=
{ map_neg_eq_map := λ f, f.map_neg,
  eq_zero_of_map_eq_zero := λ f a, f.eq_zero.1,
  ..absolute_value.subadditive_hom_class, ..absolute_value.monoid_with_zero_hom_class }

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

section linear_ordered_comm_ring

variables {R S : Type*} [ring R] [linear_ordered_comm_ring S] (abv : absolute_value R S)

lemma abs_abv_sub_le_abv_sub (a b : R) :
  abs (abv a - abv b) ≤ abv (a - b) :=
abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw abv.map_sub; apply abv.le_sub⟩

end linear_ordered_comm_ring

end absolute_value

/-- A function `f` is an absolute value if it is nonnegative, zero only at 0, additive, and
multiplicative.

See also the type `absolute_value` which represents a bundled version of absolute values.
-/
class is_absolute_value {S} [ordered_semiring S]
  {R} [semiring R] (f : R → S) : Prop :=
(abv_nonneg [] : ∀ x, 0 ≤ f x)
(abv_eq_zero [] : ∀ {x}, f x = 0 ↔ x = 0)
(abv_add [] : ∀ x y, f (x + y) ≤ f x + f y)
(abv_mul [] : ∀ x y, f (x * y) = f x * f y)

namespace is_absolute_value

section ordered_semiring

variables {S : Type*} [ordered_semiring S]
variables {R : Type*} [semiring R] (abv : R → S) [is_absolute_value abv]

/-- A bundled absolute value is an absolute value. -/
instance _root_.absolute_value.is_absolute_value
  (abv : absolute_value R S) : is_absolute_value abv :=
{ abv_nonneg := abv.nonneg,
  abv_eq_zero := λ _, abv.eq_zero,
  abv_add := abv.add_le,
  abv_mul := abv.map_mul }

/-- Convert an unbundled `is_absolute_value` to a bundled `absolute_value`. -/
@[simps]
def to_absolute_value : absolute_value R S :=
{ to_fun := abv,
  add_le' := abv_add abv,
  eq_zero' := λ _, abv_eq_zero abv,
  nonneg' := abv_nonneg abv,
  map_mul' := abv_mul abv }

theorem abv_zero : abv 0 = 0 := (to_absolute_value abv).map_zero

theorem abv_pos {a : R} : 0 < abv a ↔ a ≠ 0 := (to_absolute_value abv).pos_iff

end ordered_semiring

section linear_ordered_ring

variables {S : Type*} [linear_ordered_ring S]

instance abs_is_absolute_value : is_absolute_value (abs : S → S) :=
  absolute_value.abs.is_absolute_value

end linear_ordered_ring

section ordered_ring

variables {S : Type*} [ordered_ring S]

section semiring

variables {R : Type*} [semiring R] (abv : R → S) [is_absolute_value abv]

variables [is_domain S]

theorem abv_one [nontrivial R] : abv 1 = 1 := (to_absolute_value abv).map_one

/-- `abv` as a `monoid_with_zero_hom`. -/
def abv_hom [nontrivial R] : R →*₀ S := (to_absolute_value abv).to_monoid_with_zero_hom

lemma abv_pow [nontrivial R] (abv : R → S) [is_absolute_value abv]
  (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
(to_absolute_value abv).map_pow a n

end semiring

section ring

variables {R : Type*} [ring R] (abv : R → S) [is_absolute_value abv]

lemma abv_sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) :=
by simpa [sub_eq_add_neg, add_assoc] using abv_add abv (a - b) (b - c)

lemma sub_abv_le_abv_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
(to_absolute_value abv).le_sub a b

end ring

end ordered_ring

section ordered_comm_ring

variables {S : Type*} [ordered_comm_ring S]

section ring

variables {R : Type*} [ring R] (abv : R → S) [is_absolute_value abv]

variables [no_zero_divisors S]

theorem abv_neg (a : R) : abv (-a) = abv a :=
(to_absolute_value abv).map_neg a

theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) :=
(to_absolute_value abv).map_sub a b

end ring

end ordered_comm_ring

section linear_ordered_comm_ring

variables {S : Type*} [linear_ordered_comm_ring S]

section ring

variables {R : Type*} [ring R] (abv : R → S) [is_absolute_value abv]

lemma abs_abv_sub_le_abv_sub (a b : R) :
  abs (abv a - abv b) ≤ abv (a - b) :=
(to_absolute_value abv).abs_abv_sub_le_abv_sub a b

end ring

end linear_ordered_comm_ring

section linear_ordered_field

variables {S : Type*} [linear_ordered_semifield S]

section semiring

variables {R : Type*} [semiring R] [nontrivial R] (abv : R → S) [is_absolute_value abv]

lemma abv_one' : abv 1 = 1 :=
(to_absolute_value abv).map_one_of_is_regular
  $ (is_regular_of_ne_zero $ (to_absolute_value abv).ne_zero one_ne_zero).left

/-- An absolute value as a monoid with zero homomorphism, assuming the target is a semifield. -/
def abv_hom' : R →*₀ S := ⟨abv, abv_zero abv, abv_one' abv, abv_mul abv⟩

end semiring

section division_semiring

variables {R : Type*} [division_semiring R] (abv : R → S) [is_absolute_value abv]

theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ := map_inv₀ (abv_hom' abv) a
theorem abv_div (a b : R) : abv (a / b) = abv a / abv b := map_div₀ (abv_hom' abv) a b

end division_semiring

end linear_ordered_field

end is_absolute_value
