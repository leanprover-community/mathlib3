/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import logic.pairwise
import algebra.hom.group_instances
import data.pi.algebra
import data.set.function
import tactic.pi_instances

/-!
# Pi instances for groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

universes u v w
variables {ι α : Type*}
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

@[to_additive]
lemma set.preimage_one {α β : Type*} [has_one β] (s : set β) [decidable ((1 : β) ∈ s)] :
  (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then set.univ else ∅ :=
set.preimage_const 1 s

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
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, (x i) ^ n };
tactic.pi_instance_derive_field

@[to_additive]
instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive pi.sub_neg_monoid]
instance [Π i, div_inv_monoid $ f i] : div_inv_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := λ z x i, (x i) ^ z }; tactic.pi_instance_derive_field

@[to_additive]
instance [Π i, has_involutive_inv $ f i] : has_involutive_inv (Π i, f i) :=
by refine_struct { inv := has_inv.inv }; tactic.pi_instance_derive_field

@[to_additive pi.subtraction_monoid]
instance [Π i, division_monoid $ f i] : division_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := λ z x i, (x i) ^ z }; tactic.pi_instance_derive_field

@[to_additive pi.subtraction_comm_monoid]
instance [Π i, division_comm_monoid $ f i] : division_comm_monoid (Π i, f i) :=
{ ..pi.division_monoid, ..pi.comm_semigroup }

@[to_additive]
instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := div_inv_monoid.zpow }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_group [∀ i, comm_group $ f i] : comm_group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := div_inv_monoid.zpow }; tactic.pi_instance_derive_field

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
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive add_right_cancel_monoid]
instance right_cancel_monoid [∀ i, right_cancel_monoid $ f i] :
  right_cancel_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow, .. };
tactic.pi_instance_derive_field

@[to_additive add_cancel_monoid]
instance cancel_monoid [∀ i, cancel_monoid $ f i] :
  cancel_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive add_cancel_comm_monoid]
instance cancel_comm_monoid [∀ i, cancel_comm_monoid $ f i] :
  cancel_comm_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
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
  npow := monoid.npow }; tactic.pi_instance_derive_field

instance comm_monoid_with_zero [∀ i, comm_monoid_with_zero $ f i] :
  comm_monoid_with_zero (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*),
  npow := monoid.npow }; tactic.pi_instance_derive_field

end pi

namespace mul_hom

@[to_additive] lemma coe_mul {M N} {mM : has_mul M} {mN : comm_semigroup N}
  (f g : M →ₙ* N) :
  (f * g : M → N) = λ x, f x * g x := rfl

end mul_hom

section mul_hom

/-- A family of mul_hom `f a : γ →ₙ* β a` defines a mul_hom `pi.mul_hom f : γ →ₙ* Π a, β a`
given by `pi.mul_hom f x b = f b x`. -/
@[to_additive "A family of add_hom `f a : γ → β a` defines a add_hom `pi.add_hom
f : γ → Π a, β a` given by `pi.add_hom f x b = f b x`.", simps]
def pi.mul_hom {γ : Type w} [Π i, has_mul (f i)] [has_mul γ]
  (g : Π i, γ →ₙ* f i) : γ →ₙ* Π i, f i :=
{ to_fun := λ x i, g i x,
  map_mul' := λ x y, funext $ λ i, (g i).map_mul x y, }

@[to_additive]
lemma pi.mul_hom_injective {γ : Type w} [nonempty I]
  [Π i, has_mul (f i)] [has_mul γ] (g : Π i, γ →ₙ* f i)
  (hg : ∀ i, function.injective (g i)) : function.injective (pi.mul_hom g) :=
λ x y h, let ⟨i⟩ := ‹nonempty I› in hg i ((function.funext_iff.mp h : _) i)

/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`pi.monoid_mul_hom f : γ →* Π a, β a` given by `pi.monoid_mul_hom f x b = f b x`. -/
@[to_additive "A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid
homomorphism `pi.add_monoid_hom f : γ →+ Π a, β a` given by `pi.add_monoid_hom f x b
= f b x`.", simps]
def pi.monoid_hom {γ : Type w} [Π i, mul_one_class (f i)] [mul_one_class γ]
  (g : Π i, γ →* f i) : γ →* Π i, f i :=
{ to_fun := λ x i, g i x,
  map_one' := funext $ λ i, (g i).map_one,
  .. pi.mul_hom (λ i, (g i).to_mul_hom) }

@[to_additive]
lemma pi.monoid_hom_injective {γ : Type w} [nonempty I]
  [Π i, mul_one_class (f i)] [mul_one_class γ] (g : Π i, γ →* f i)
  (hg : ∀ i, function.injective (g i)) : function.injective (pi.monoid_hom g) :=
pi.mul_hom_injective (λ i, (g i).to_mul_hom) hg

variables (f) [Π i, has_mul (f i)]

/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `function.eval i` as a `mul_hom`. -/
@[to_additive "Evaluation of functions into an indexed collection of additive semigroups at a
point is an additive semigroup homomorphism.
This is `function.eval i` as an `add_hom`.", simps]
def pi.eval_mul_hom (i : I) : (Π i, f i) →ₙ* f i :=
{ to_fun := λ g, g i,
  map_mul' := λ x y, pi.mul_apply _ _ i, }

/-- `function.const` as a `mul_hom`. -/
@[to_additive "`function.const` as an `add_hom`.", simps]
def pi.const_mul_hom (α β : Type*) [has_mul β] : β →ₙ* (α → β) :=
{ to_fun := function.const α,
  map_mul' := λ _ _, rfl }

/-- Coercion of a `mul_hom` into a function is itself a `mul_hom`.
See also `mul_hom.eval`. -/
@[to_additive "Coercion of an `add_hom` into a function is itself a `add_hom`.
See also `add_hom.eval`. ", simps]
def mul_hom.coe_fn (α β : Type*) [has_mul α] [comm_semigroup β] : (α →ₙ* β) →ₙ* (α → β) :=
{ to_fun := λ g, g,
  map_mul' := λ x y, rfl, }

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive "Additive semigroup homomorphism between the function spaces `I → α` and `I → β`,
induced by an additive semigroup homomorphism `f` between `α` and `β`", simps]
protected def mul_hom.comp_left {α β : Type*} [has_mul α] [has_mul β] (f : α →ₙ* β)
  (I : Type*) :
  (I → α) →ₙ* (I → β) :=
{ to_fun := λ h, f ∘ h,
  map_mul' := λ _ _, by ext; simp }

end mul_hom

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

/-- The one-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `one_hom` version of `pi.mul_single`. -/
@[to_additive zero_hom.single "The zero-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `zero_hom` version of `pi.single`."]
def one_hom.single [Π i, has_one $ f i] (i : I) : one_hom (f i) (Π i, f i) :=
{ to_fun := mul_single i,
  map_one' := mul_single_one i }

@[simp, to_additive]
lemma one_hom.single_apply [Π i, has_one $ f i] (i : I) (x : f i) :
  one_hom.single f i x = mul_single i x := rfl

/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `monoid_hom` version of `pi.mul_single`. -/
@[to_additive "The additive monoid homomorphism including a single additive
monoid into a dependent family of additive monoids, as functions supported at a point.

This is the `add_monoid_hom` version of `pi.single`."]
def monoid_hom.single [Π i, mul_one_class $ f i] (i : I) : f i →* Π i, f i :=
{ map_mul' := mul_single_op₂ (λ _, (*)) (λ _, one_mul _) _,
  .. (one_hom.single f i) }

@[simp, to_additive]
lemma monoid_hom.single_apply [Π i, mul_one_class $ f i] (i : I) (x : f i) :
  monoid_hom.single f i x = mul_single i x := rfl

/-- The multiplicative homomorphism including a single `mul_zero_class`
into a dependent family of `mul_zero_class`es, as functions supported at a point.

This is the `mul_hom` version of `pi.single`. -/
@[simps] def mul_hom.single [Π i, mul_zero_class $ f i] (i : I) : (f i) →ₙ* (Π i, f i) :=
{ to_fun := single i,
  map_mul' := pi.single_op₂ (λ _, (*)) (λ _, zero_mul _) _, }

variables {f}

@[to_additive]
lemma pi.mul_single_mul [Π i, mul_one_class $ f i] (i : I) (x y : f i) :
  mul_single i (x * y) = mul_single i x * mul_single i y :=
(monoid_hom.single f i).map_mul x y

@[to_additive]
lemma pi.mul_single_inv [Π i, group $ f i] (i : I) (x : f i) :
  mul_single i (x⁻¹) = (mul_single i x)⁻¹ :=
(monoid_hom.single f i).map_inv x

@[to_additive]
lemma pi.single_div [Π i, group $ f i] (i : I) (x y : f i) :
  mul_single i (x / y) = mul_single i x / mul_single i y :=
(monoid_hom.single f i).map_div x y

lemma pi.single_mul [Π i, mul_zero_class $ f i] (i : I) (x y : f i) :
  single i (x * y) = single i x * single i y :=
(mul_hom.single f i).map_mul x y

/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `commute.map` -/
@[to_additive "The injection into an additive pi group at different indices commutes.

For injections of commuting elements at the same index, see `add_commute.map`"]
lemma pi.mul_single_commute [Π i, mul_one_class $ f i] :
  pairwise (λ i j, ∀ (x : f i) (y : f j), commute (mul_single i x) (mul_single j y)) :=
begin
  intros i j hij x y, ext k,
  by_cases h1 : i = k, { subst h1, simp [hij], },
  by_cases h2 : j = k, { subst h2, simp [hij], },
  simp [h1,  h2],
end

/-- The injection into a pi group with the same values commutes. -/
@[to_additive "The injection into an additive pi group with the same values commutes."]
lemma pi.mul_single_apply_commute [Π i, mul_one_class $ f i] (x : Π i, f i) (i j : I) :
  commute (mul_single i (x i)) (mul_single j (x j)) :=
begin
  obtain rfl | hij := decidable.eq_or_ne i j,
  { refl },
  { exact pi.mul_single_commute hij _ _, },
end

@[to_additive update_eq_sub_add_single]
lemma pi.update_eq_div_mul_single [Π i, group $ f i] (g : Π (i : I), f i) (x : f i) :
  function.update g i x = g / mul_single i (g i) * mul_single i x :=
begin
  ext j,
  rcases eq_or_ne i j with rfl|h,
  { simp },
  { simp [function.update_noteq h.symm, h] }
end

@[to_additive pi.single_add_single_eq_single_add_single]
lemma pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single
  {M : Type*} [comm_monoid M] {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
  mul_single k u * mul_single l v = mul_single m u * mul_single n v ↔
  (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u * v = 1 ∧ k = l ∧ m = n) :=
begin
  refine ⟨λ h, _, _⟩,
  { have hk := congr_fun h k,
    have hl := congr_fun h l,
    have hm := (congr_fun h m).symm,
    have hn := (congr_fun h n).symm,
    simp only [mul_apply, mul_single_apply, if_pos rfl] at hk hl hm hn,
    rcases eq_or_ne k m with rfl | hkm,
    { refine or.inl ⟨rfl, not_ne_iff.mp (λ hln, (hv _).elim)⟩,
      rcases eq_or_ne k l with rfl | hkl,
      { rwa [if_neg hln.symm, if_neg hln.symm, one_mul, one_mul] at hn },
      { rwa [if_neg hkl.symm, if_neg hln, one_mul, one_mul] at hl } },
    { rcases eq_or_ne m n with rfl | hmn,
      { rcases eq_or_ne k l with rfl | hkl,
        { rw [if_neg hkm.symm, if_neg hkm.symm, one_mul, if_pos rfl] at hm,
          exact or.inr (or.inr ⟨hm, rfl, rfl⟩) },
        { simpa only [if_neg hkm, if_neg hkl, mul_one] using hk } },
      { rw [if_neg hkm.symm, if_neg hmn, one_mul, mul_one] at hm,
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hm.symm hu)).1,
        rw [if_neg hkm, if_neg hkm, one_mul, mul_one] at hk,
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hk.symm hu)).1,
        exact or.inr (or.inl ⟨hk.trans (if_pos rfl), rfl, rfl⟩) } } },
  { rintros (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl⟩),
    { refl },
    { apply mul_comm },
    { simp_rw [←pi.mul_single_mul, h, mul_single_one] } },
end

end single

namespace function

@[simp, to_additive]
lemma update_one [Π i, has_one (f i)] [decidable_eq I] (i : I) :
  update (1 : Π i, f i) i 1 = 1 :=
update_eq_self i 1

@[to_additive]
lemma update_mul [Π i, has_mul (f i)] [decidable_eq I]
  (f₁ f₂ : Π i, f i) (i : I) (x₁ : f i) (x₂ : f i) :
  update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
funext $ λ j, (apply_update₂ (λ i, (*)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
lemma update_inv [Π i, has_inv (f i)] [decidable_eq I]
  (f₁ : Π i, f i) (i : I) (x₁ : f i) :
  update (f₁⁻¹) i (x₁⁻¹) = (update f₁ i x₁)⁻¹ :=
funext $ λ j, (apply_update (λ i, has_inv.inv) f₁ i x₁ j).symm

@[to_additive]
lemma update_div [Π i, has_div (f i)] [decidable_eq I]
  (f₁ f₂ : Π i, f i) (i : I) (x₁ : f i) (x₂ : f i) :
  update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
funext $ λ j, (apply_update₂ (λ i, (/)) f₁ f₂ i x₁ x₂ j).symm

variables [has_one α] [nonempty ι] {a : α}

@[simp, to_additive] lemma const_eq_one : const ι a = 1 ↔ a = 1 := @const_inj _ _ _ _ 1
@[to_additive] lemma const_ne_one : const ι a ≠ 1 ↔ a ≠ 1 := const_eq_one.not

end function

section piecewise

@[to_additive]
lemma set.piecewise_mul [Π i, has_mul (f i)] (s : set I) [Π i, decidable (i ∈ s)]
  (f₁ f₂ g₁ g₂ : Π i, f i) :
  s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
s.piecewise_op₂ _ _ _ _ (λ _, (*))

@[to_additive]
lemma set.piecewise_inv [Π i, has_inv (f i)] (s : set I) [Π i, decidable (i ∈ s)]
  (f₁ g₁ : Π i, f i) :
  s.piecewise (f₁⁻¹) (g₁⁻¹) = (s.piecewise f₁ g₁)⁻¹ :=
s.piecewise_op f₁ g₁ (λ _ x, x⁻¹)

@[to_additive]
lemma set.piecewise_div [Π i, has_div (f i)] (s : set I) [Π i, decidable (i ∈ s)]
  (f₁ f₂ g₁ g₂ : Π i, f i) :
  s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
s.piecewise_op₂ _ _ _ _ (λ _, (/))

end piecewise

section extend

variables {η : Type v} (R : Type w) (s : ι → η)

/-- `function.extend s f 1` as a bundled hom. -/
@[to_additive function.extend_by_zero.hom "`function.extend s f 0` as a bundled hom.", simps]
noncomputable def function.extend_by_one.hom [mul_one_class R] : (ι → R) →* (η → R) :=
{ to_fun := λ f, function.extend s f 1,
  map_one' := function.extend_one s,
  map_mul' := λ f g, by { simpa using function.extend_mul s f g 1 1 } }

end extend
