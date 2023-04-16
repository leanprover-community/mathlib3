/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.group_power.order

/-!
# Algebraic order homomorphism classes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

Basic typeclasses
* `nonneg_hom_class`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `subadditive_hom_class`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `submultiplicative_hom_class`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `mul_le_add_hom_class`: `∀ f a b, f (a * b) ≤ f a + f b`
* `nonarchimedean_hom_class`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

Group norms
* `add_group_seminorm_class`: Homs are nonnegative, subadditive, even and preserve zero.
* `group_seminorm_class`: Homs are nonnegative, respect `f (a * b) ≤ f a + f b`, `f a⁻¹ = f a` and
  preserve zero.
* `add_group_norm_class`: Homs are seminorms such that `f x = 0 → x = 0` for all `x`.
* `group_norm_class`: Homs are seminorms such that `f x = 0 → x = 1` for all `x`.

Ring norms
* `ring_seminorm_class`: Homs are submultiplicative group norms.
* `ring_norm_class`: Homs are ring seminorms that are also additive group norms.
* `mul_ring_seminorm_class`: Homs are ring seminorms that are multiplicative.
* `mul_ring_norm_class`: Homs are ring norms that are multiplicative.

## Notes

Typeclasses for seminorms are defined here while types of seminorms are defined in
`analysis.normed.group.seminorm` and `analysis.normed.ring.seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/

/--
Diamond inheritance cannot depend on `out_param`s in the following circumstances:
 * there are three classes `top`, `middle`, `bottom`
 * all of these classes have a parameter `(α : out_param _)`
 * all of these classes have an instance parameter `[root α]` that depends on this `out_param`
 * the `root` class has two child classes: `left` and `right`, these are siblings in the hierarchy
 * the instance `bottom.to_middle` takes a `[left α]` parameter
 * the instance `middle.to_top` takes a `[right α]` parameter
 * there is a `leaf` class that inherits from both `left` and `right`.
In that case, given instances `bottom α` and `leaf α`, Lean cannot synthesize a `top α` instance,
even though the hypotheses of the instances `bottom.to_middle` and `middle.to_top` are satisfied.

There are two workarounds:
* You could replace the bundled inheritance implemented by the instance `middle.to_top` with
  unbundled inheritance implemented by adding a `[top α]` parameter to the `middle` class. This is
  the preferred option since it is also more compatible with Lean 4, at the cost of being more work
  to implement and more verbose to use.
* You could weaken the `bottom.to_middle` instance by making it depend on a subclass of
  `middle.to_top`'s parameter, in this example replacing `[left α]` with `[leaf α]`.
-/
library_note "out-param inheritance"

set_option old_structure_cmd true

open function

variables {ι F α β γ δ : Type*}

/-! ### Basics -/

/-- `nonneg_hom_class F α β` states that `F` is a type of nonnegative morphisms. -/
class nonneg_hom_class (F : Type*) (α β : out_param $ Type*) [has_zero β] [has_le β]
  extends fun_like F α (λ _, β) :=
(map_nonneg (f : F) : ∀ a, 0 ≤ f a)

/-- `subadditive_hom_class F α β` states that `F` is a type of subadditive morphisms. -/
class subadditive_hom_class (F : Type*) (α β : out_param $ Type*) [has_add α] [has_add β] [has_le β]
  extends fun_like F α (λ _, β) :=
(map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b)

/-- `submultiplicative_hom_class F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive subadditive_hom_class]
class submultiplicative_hom_class (F : Type*) (α β : out_param $ Type*) [has_mul α] [has_mul β]
  [has_le β] extends fun_like F α (λ _, β) :=
(map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b)

/-- `mul_le_add_hom_class F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive subadditive_hom_class]
class mul_le_add_hom_class (F : Type*) (α β : out_param $ Type*) [has_mul α] [has_add β] [has_le β]
  extends fun_like F α (λ _, β) :=
(map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b)

/-- `nonarchimedean_hom_class F α β` states that `F` is a type of non-archimedean morphisms. -/
class nonarchimedean_hom_class (F : Type*) (α β : out_param $ Type*) [has_add α] [linear_order β]
  extends fun_like F α (λ _, β) :=
(map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b))

export nonneg_hom_class (map_nonneg)
export subadditive_hom_class (map_add_le_add)
export submultiplicative_hom_class (map_mul_le_mul)
export mul_le_add_hom_class (map_mul_le_add)
export nonarchimedean_hom_class (map_add_le_max)

attribute [simp] map_nonneg

@[to_additive] lemma le_map_mul_map_div [group α] [comm_semigroup β] [has_le β]
  [submultiplicative_hom_class F α β] (f : F) (a b : α) : f a ≤ f b * f (a / b) :=
by simpa only [mul_comm, div_mul_cancel'] using map_mul_le_mul f (a / b) b

@[to_additive] lemma le_map_add_map_div [group α] [add_comm_semigroup β] [has_le β]
  [mul_le_add_hom_class F α β] (f : F) (a b : α) : f a ≤ f b + f (a / b) :=
by simpa only [add_comm, div_mul_cancel'] using map_mul_le_add f (a / b) b

@[to_additive]
lemma le_map_div_mul_map_div [group α] [comm_semigroup β] [has_le β]
  [submultiplicative_hom_class F α β] (f : F) (a b c: α) : f (a / c) ≤ f (a / b) * f (b / c) :=
by simpa only [div_mul_div_cancel'] using map_mul_le_mul f (a / b) (b / c)

@[to_additive]
lemma le_map_div_add_map_div [group α] [add_comm_semigroup β] [has_le β]
  [mul_le_add_hom_class F α β] (f : F) (a b c: α) : f (a / c) ≤ f (a / b) + f (b / c) :=
by simpa only [div_mul_div_cancel'] using map_mul_le_add f (a / b) (b / c)

/-! ### Group (semi)norms -/

/-- `add_group_seminorm_class F α` states that `F` is a type of `β`-valued seminorms on the additive
group `α`.

You should extend this class when you extend `add_group_seminorm`. -/
class add_group_seminorm_class (F : Type*) (α β : out_param $ Type*) [add_group α]
  [ordered_add_comm_monoid β] extends subadditive_hom_class F α β :=
(map_zero (f : F) : f 0 = 0)
(map_neg_eq_map (f : F) (a : α) : f (-a) = f a)

/-- `group_seminorm_class F α` states that `F` is a type of `β`-valued seminorms on the group `α`.

You should extend this class when you extend `group_seminorm`. -/
@[to_additive]
class group_seminorm_class (F : Type*) (α β : out_param $ Type*) [group α]
  [ordered_add_comm_monoid β] extends mul_le_add_hom_class F α β :=
(map_one_eq_zero (f : F) : f 1 = 0)
(map_inv_eq_map (f : F) (a : α) : f a⁻¹ = f a)

/-- `add_group_norm_class F α` states that `F` is a type of `β`-valued norms on the additive group
`α`.

You should extend this class when you extend `add_group_norm`. -/
class add_group_norm_class (F : Type*) (α β : out_param $ Type*) [add_group α]
  [ordered_add_comm_monoid β] extends add_group_seminorm_class F α β :=
(eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0)

/-- `group_norm_class F α` states that `F` is a type of `β`-valued norms on the group `α`.

You should extend this class when you extend `group_norm`. -/
@[to_additive]
class group_norm_class (F : Type*) (α β : out_param $ Type*) [group α] [ordered_add_comm_monoid β]
  extends group_seminorm_class F α β :=
(eq_one_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 1)

export add_group_seminorm_class    (map_neg_eq_map)
export group_seminorm_class        (map_one_eq_zero map_inv_eq_map)
export add_group_norm_class        (eq_zero_of_map_eq_zero)
export group_norm_class            (eq_one_of_map_eq_zero)

attribute [simp, to_additive map_zero] map_one_eq_zero
attribute [simp] map_neg_eq_map
attribute [simp, to_additive] map_inv_eq_map
attribute [to_additive] group_seminorm_class.to_mul_le_add_hom_class
attribute [to_additive] group_norm_class.to_group_seminorm_class

@[priority 100] -- See note [lower instance priority]
instance add_group_seminorm_class.to_zero_hom_class [add_group α] [ordered_add_comm_monoid β]
  [add_group_seminorm_class F α β] :
  zero_hom_class F α β :=
{ ..‹add_group_seminorm_class F α β› }

section group_seminorm_class
variables [group α] [ordered_add_comm_monoid β] [group_seminorm_class F α β] (f : F) (x y : α)
include α β

@[to_additive] lemma map_div_le_add : f (x / y) ≤ f x + f y :=
by { rw [div_eq_mul_inv, ←map_inv_eq_map f y], exact map_mul_le_add _ _ _ }

@[to_additive] lemma map_div_rev : f (x / y) = f (y / x) := by rw [←inv_div, map_inv_eq_map]

@[to_additive] lemma le_map_add_map_div' : f x ≤ f y + f (y / x) :=
by simpa only [add_comm, map_div_rev, div_mul_cancel'] using map_mul_le_add f (x / y) y

end group_seminorm_class

example [ordered_add_comm_group β] : ordered_add_comm_monoid β := infer_instance

@[to_additive] lemma abs_sub_map_le_div [group α] [linear_ordered_add_comm_group β]
  [group_seminorm_class F α β] (f : F) (x y : α) : |f x - f y| ≤ f (x / y) :=
begin
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add'],
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩
end

@[to_additive, priority 100] -- See note [lower instance priority]
instance group_seminorm_class.to_nonneg_hom_class [group α] [linear_ordered_add_comm_monoid β]
  [group_seminorm_class F α β] :
  nonneg_hom_class F α β :=
{ map_nonneg := λ f a, (nsmul_nonneg_iff two_ne_zero).1 $
    by { rw [two_nsmul, ←map_one_eq_zero f, ←div_self' a], exact map_div_le_add _ _ _ },
  ..‹group_seminorm_class F α β› }

section group_norm_class
variables [group α] [ordered_add_comm_monoid β] [group_norm_class F α β] (f : F) {x : α}
include α β

@[simp, to_additive] lemma map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
⟨eq_one_of_map_eq_zero _, by { rintro rfl, exact map_one_eq_zero _ }⟩

@[to_additive] lemma map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 := (map_eq_zero_iff_eq_one _).not

end group_norm_class

@[to_additive] lemma map_pos_of_ne_one [group α] [linear_ordered_add_comm_monoid β]
  [group_norm_class F α β] (f : F) {x : α} (hx : x ≠ 1) : 0 < f x :=
(map_nonneg _ _).lt_of_ne $ ((map_ne_zero_iff_ne_one _).2 hx).symm

/-! ### Ring (semi)norms -/

/-- `ring_seminorm_class F α` states that `F` is a type of `β`-valued seminorms on the ring `α`.

You should extend this class when you extend `ring_seminorm`. -/
class ring_seminorm_class (F : Type*) (α β : out_param $ Type*) [non_unital_non_assoc_ring α]
  [ordered_semiring β] extends add_group_seminorm_class F α β, submultiplicative_hom_class F α β

/-- `ring_norm_class F α` states that `F` is a type of `β`-valued norms on the ring `α`.

You should extend this class when you extend `ring_norm`. -/
class ring_norm_class (F : Type*) (α β : out_param $ Type*) [non_unital_non_assoc_ring α]
  [ordered_semiring β] extends ring_seminorm_class F α β, add_group_norm_class F α β

/-- `mul_ring_seminorm_class F α` states that `F` is a type of `β`-valued multiplicative seminorms
on the ring `α`.

You should extend this class when you extend `mul_ring_seminorm`. -/
class mul_ring_seminorm_class (F : Type*) (α β : out_param $ Type*) [non_assoc_ring α]
  [ordered_semiring β] extends add_group_seminorm_class F α β, monoid_with_zero_hom_class F α β

/-- `mul_ring_norm_class F α` states that `F` is a type of `β`-valued multiplicative norms on the
ring `α`.

You should extend this class when you extend `mul_ring_norm`. -/
class mul_ring_norm_class (F : Type*) (α β : out_param $ Type*) [non_assoc_ring α]
  [ordered_semiring β] extends mul_ring_seminorm_class F α β, add_group_norm_class F α β

-- See note [out-param inheritance]
@[priority 100] -- See note [lower instance priority]
instance ring_seminorm_class.to_nonneg_hom_class [non_unital_non_assoc_ring α]
  [linear_ordered_semiring β] [ring_seminorm_class F α β] : nonneg_hom_class F α β :=
add_group_seminorm_class.to_nonneg_hom_class

@[priority 100] -- See note [lower instance priority]
instance mul_ring_seminorm_class.to_ring_seminorm_class [non_assoc_ring α] [ordered_semiring β]
  [mul_ring_seminorm_class F α β] : ring_seminorm_class F α β :=
{ map_mul_le_mul := λ f a b, (map_mul _ _ _).le,
  ..‹mul_ring_seminorm_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance mul_ring_norm_class.to_ring_norm_class [non_assoc_ring α] [ordered_semiring β]
  [mul_ring_norm_class F α β] : ring_norm_class F α β :=
{ ..‹mul_ring_norm_class F α β›, ..mul_ring_seminorm_class.to_ring_seminorm_class }
