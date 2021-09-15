/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import data.pi
import data.set.function
import tactic.pi_instances
import algebra.group.hom_instances

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

@[to_additive]
instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

instance semigroup_with_zero [∀ i, semigroup_with_zero $ f i] :
  semigroup_with_zero (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance mul_one_class [∀ i, mul_one_class $ f i] : mul_one_class (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, npow n (x i) };
tactic.pi_instance_derive_field

@[simp]
lemma pow_apply [∀ i, monoid $ f i] (n : ℕ) : (x^n) i = (x i)^n :=
begin
  induction n with n ih,
  { simp, },
  { simp [pow_succ, ih], },
end

@[to_additive]
instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, npow n (x i) };
tactic.pi_instance_derive_field

@[to_additive]
instance div_inv_monoid [∀ i, div_inv_monoid $ f i] :
  div_inv_monoid (Π i : I, f i) :=
{ div_eq_mul_inv := λ x y, funext (λ i, div_eq_mul_inv (x i) (y i)),
  .. pi.monoid, .. pi.has_div, .. pi.has_inv }

@[to_additive]
instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := λ n x i, npow n (x i), gpow := λ n x i, gpow n (x i) }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_group [∀ i, comm_group $ f i] : comm_group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := λ n x i, npow n (x i), gpow := λ n x i, gpow n (x i) }; tactic.pi_instance_derive_field

@[to_additive add_left_cancel_semigroup]
instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] :
  left_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_right_cancel_semigroup]
instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] :
  right_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_left_cancel_monoid]
instance left_cancel_monoid [∀ i, left_cancel_monoid $ f i] :
  left_cancel_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, npow n (x i) };
tactic.pi_instance_derive_field

@[to_additive add_right_cancel_monoid]
instance right_cancel_monoid [∀ i, right_cancel_monoid $ f i] :
  right_cancel_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, npow n (x i), .. };
tactic.pi_instance_derive_field

@[to_additive add_cancel_monoid]
instance cancel_monoid [∀ i, cancel_monoid $ f i] :
  cancel_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, npow n (x i) };
tactic.pi_instance_derive_field

@[to_additive add_cancel_comm_monoid]
instance cancel_comm_monoid [∀ i, cancel_comm_monoid $ f i] :
  cancel_comm_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, npow n (x i) };
tactic.pi_instance_derive_field

instance mul_zero_class [∀ i, mul_zero_class $ f i] :
  mul_zero_class (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

instance mul_zero_one_class [∀ i, mul_zero_one_class $ f i] :
  mul_zero_one_class (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*), .. };
  tactic.pi_instance_derive_field

instance monoid_with_zero [∀ i, monoid_with_zero $ f i] :
  monoid_with_zero (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*),
  npow := λ n x i, npow n (x i) }; tactic.pi_instance_derive_field

instance comm_monoid_with_zero [∀ i, comm_monoid_with_zero $ f i] :
  comm_monoid_with_zero (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*),
  npow := λ n x i, npow n (x i) }; tactic.pi_instance_derive_field

section instance_lemmas
open function

variables {α β γ : Type*}

@[simp, to_additive] lemma const_one [has_one β] : const α (1 : β) = 1 := rfl

@[simp, to_additive] lemma comp_one [has_one β] {f : β → γ} : f ∘ 1 = const α (f 1) := rfl

@[simp, to_additive] lemma one_comp [has_one γ] {f : α → β} : (1 : β → γ) ∘ f = 1 := rfl

end instance_lemmas

end pi

section monoid_hom

variables (f) [Π i, mul_one_class (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `function.eval i` as a `monoid_hom`. -/
@[to_additive "Evaluation of functions into an indexed collection of additive monoids at a
point is an additive monoid homomorphism.
This is `function.eval i` as an `add_monoid_hom`.", simps]
def pi.eval_monoid_hom (i : I) : (Π i, f i) →* f i :=
{ to_fun := λ g, g i,
  map_one' := pi.one_apply i,
  map_mul' := λ x y, pi.mul_apply _ _ i, }

/-- `function.const` as a `monoid_hom`. -/
@[to_additive "`function.const` as an `add_monoid_hom`.", simps]
def pi.const_monoid_hom (α β : Type*) [mul_one_class β] : β →* (α → β) :=
{ to_fun := function.const α,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

/-- Coercion of a `monoid_hom` into a function is itself a `monoid_hom`.

See also `monoid_hom.eval`. -/
@[to_additive "Coercion of an `add_monoid_hom` into a function is itself a `add_monoid_hom`.

See also `add_monoid_hom.eval`. ", simps]
def monoid_hom.coe_fn (α β : Type*) [mul_one_class α] [comm_monoid β] : (α →* β) →* (α → β) :=
{ to_fun := λ g, g,
  map_one' := rfl,
  map_mul' := λ x y, rfl, }

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive "Additive monoid homomorphism between the function spaces `I → α` and `I → β`,
induced by an additive monoid homomorphism `f` between `α` and `β`", simps]
protected def monoid_hom.comp_left {α β : Type*} [mul_one_class α] [mul_one_class β] (f : α →* β)
  (I : Type*) :
  (I → α) →* (I → β) :=
{ to_fun := λ h, f ∘ h,
  map_one' := by ext; simp,
  map_mul' := λ _ _, by ext; simp }

end monoid_hom

section single
variables [decidable_eq I]
open pi

variables (f)

/-- The zero-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `zero_hom` version of `pi.single`. -/
@[simps] def zero_hom.single [Π i, has_zero $ f i] (i : I) : zero_hom (f i) (Π i, f i) :=
{ to_fun := single i,
  map_zero' := single_zero i }

/-- The additive monoid homomorphism including a single additive monoid
into a dependent family of additive monoids, as functions supported at a point.

This is the `add_monoid_hom` version of `pi.single`. -/
@[simps] def add_monoid_hom.single [Π i, add_zero_class $ f i] (i : I) : f i →+ Π i, f i :=
{ to_fun := single i,
  map_add' := single_op₂ (λ _, (+)) (λ _, zero_add _) _,
  .. (zero_hom.single f i) }

/-- The multiplicative homomorphism including a single `mul_zero_class`
into a dependent family of `mul_zero_class`es, as functions supported at a point.

This is the `mul_hom` version of `pi.single`. -/
@[simps] def mul_hom.single [Π i, mul_zero_class $ f i] (i : I) : mul_hom (f i) (Π i, f i) :=
{ to_fun := single i,
  map_mul' := single_op₂ (λ _, (*)) (λ _, zero_mul _) _, }

variables {f}

lemma pi.single_add [Π i, add_zero_class $ f i] (i : I) (x y : f i) :
  single i (x + y) = single i x + single i y :=
(add_monoid_hom.single f i).map_add x y

lemma pi.single_neg [Π i, add_group $ f i] (i : I) (x : f i) :
  single i (-x) = -single i x :=
(add_monoid_hom.single f i).map_neg x

lemma pi.single_sub [Π i, add_group $ f i] (i : I) (x y : f i) :
  single i (x - y) = single i x - single i y :=
(add_monoid_hom.single f i).map_sub x y

lemma pi.single_mul [Π i, mul_zero_class $ f i] (i : I) (x y : f i) :
  single i (x * y) = single i x * single i y :=
(mul_hom.single f i).map_mul x y

end single

section piecewise

@[to_additive]
lemma set.piecewise_mul [Π i, has_mul (f i)] (s : set I) [Π i, decidable (i ∈ s)]
  (f₁ f₂ g₁ g₂ : Π i, f i) :
  s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
s.piecewise_op₂ _ _ _ _ (λ _, (*))

@[to_additive]
lemma pi.piecewise_inv [Π i, has_inv (f i)] (s : set I) [Π i, decidable (i ∈ s)]
  (f₁ g₁ : Π i, f i) :
  s.piecewise (f₁⁻¹) (g₁⁻¹) = (s.piecewise f₁ g₁)⁻¹ :=
s.piecewise_op f₁ g₁ (λ _ x, x⁻¹)

@[to_additive]
lemma pi.piecewise_div [Π i, has_div (f i)] (s : set I) [Π i, decidable (i ∈ s)]
  (f₁ f₂ g₁ g₂ : Π i, f i) :
  s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
s.piecewise_op₂ _ _ _ _ (λ _, (/))

end piecewise

section extend

variables {ι : Type u} {η : Type v} (R : Type w) (s : ι → η)

/-- `function.extend s f 1` as a bundled hom. -/
@[to_additive function.extend_by_zero.hom "`function.extend s f 0` as a bundled hom.", simps]
noncomputable def function.extend_by_one.hom [mul_one_class R] : (ι → R) →* (η → R) :=
{ to_fun := λ f, function.extend s f 1,
  map_one' := function.extend_one s,
  map_mul' := λ f g, by { simpa using function.extend_mul s f g 1 1 } }

end extend
