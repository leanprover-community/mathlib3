/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.locally_constant.basic
import topology.continuous_function.algebra
import algebra.algebra.basic

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`add_group`, etc)
on the type of locally constant functions.

-/

namespace locally_constant

variables {X Y : Type*} [topological_space X]

@[to_additive] instance [has_one Y] : has_one (locally_constant X Y) :=
{ one := const X 1 }

@[simp, to_additive] lemma coe_one [has_one Y] : ⇑(1 : locally_constant X Y) = (1 : X → Y) := rfl

@[to_additive] lemma one_apply [has_one Y] (x : X) : (1 : locally_constant X Y) x = 1 := rfl

@[to_additive] instance [has_inv Y] : has_inv (locally_constant X Y) :=
{ inv := λ f, ⟨f⁻¹ , f.is_locally_constant.inv⟩ }

@[simp, to_additive] lemma coe_inv [has_inv Y] (f : locally_constant X Y) : ⇑(f⁻¹) = f⁻¹ := rfl

@[to_additive] lemma inv_apply [has_inv Y] (f : locally_constant X Y) (x : X) :
  f⁻¹ x = (f x)⁻¹ := rfl

@[to_additive] instance [has_mul Y] : has_mul (locally_constant X Y) :=
{ mul := λ f g, ⟨f * g, f.is_locally_constant.mul g.is_locally_constant⟩ }

@[simp, to_additive] lemma coe_mul [has_mul Y] (f g : locally_constant X Y) :
  ⇑(f * g) = f * g :=
rfl

@[to_additive] lemma mul_apply [has_mul Y] (f g : locally_constant X Y) (x : X) :
  (f * g) x = f x * g x := rfl

@[to_additive] instance [mul_one_class Y] : mul_one_class (locally_constant X Y) :=
{ one_mul := by { intros, ext, simp only [mul_apply, one_apply, one_mul] },
  mul_one := by { intros, ext, simp only [mul_apply, one_apply, mul_one] },
  .. locally_constant.has_one,
  .. locally_constant.has_mul }

/-- `coe_fn` is a `monoid_hom`. -/
@[to_additive "`coe_fn` is an `add_monoid_hom`.", simps]
def coe_fn_monoid_hom [mul_one_class Y] : locally_constant X Y →* (X → Y) :=
{ to_fun   := coe_fn,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive "The constant-function embedding, as an additive monoid hom.", simps]
def const_monoid_hom [mul_one_class Y] : Y →* locally_constant X Y :=
{ to_fun   := const X,
  map_one' := rfl,
  map_mul' := λ _ _, rfl, }

instance [mul_zero_class Y] : mul_zero_class (locally_constant X Y) :=
{ zero_mul := by { intros, ext, simp only [mul_apply, zero_apply, zero_mul] },
  mul_zero := by { intros, ext, simp only [mul_apply, zero_apply, mul_zero] },
  .. locally_constant.has_zero,
  .. locally_constant.has_mul }

instance [mul_zero_one_class Y] : mul_zero_one_class (locally_constant X Y) :=
{ .. locally_constant.mul_zero_class, .. locally_constant.mul_one_class }

@[to_additive] instance [has_div Y] : has_div (locally_constant X Y) :=
{ div := λ f g, ⟨f / g, f.is_locally_constant.div g.is_locally_constant⟩ }

@[to_additive] lemma coe_div [has_div Y] (f g : locally_constant X Y) :
  ⇑(f / g) = f / g := rfl

@[to_additive] lemma div_apply [has_div Y] (f g : locally_constant X Y) (x : X) :
  (f / g) x = f x / g x := rfl

@[to_additive] instance [semigroup Y] : semigroup (locally_constant X Y) :=
{ mul_assoc := by { intros, ext, simp only [mul_apply, mul_assoc] },
  .. locally_constant.has_mul }

instance [semigroup_with_zero Y] : semigroup_with_zero (locally_constant X Y) :=
{ .. locally_constant.mul_zero_class,
  .. locally_constant.semigroup }

@[to_additive] instance [comm_semigroup Y] : comm_semigroup (locally_constant X Y) :=
{ mul_comm := by { intros, ext, simp only [mul_apply, mul_comm] },
  .. locally_constant.semigroup }

@[to_additive] instance [monoid Y] : monoid (locally_constant X Y) :=
{ mul := (*),
  .. locally_constant.semigroup, .. locally_constant.mul_one_class }

@[to_additive] instance [comm_monoid Y] : comm_monoid (locally_constant X Y) :=
{ .. locally_constant.comm_semigroup, .. locally_constant.monoid }

@[to_additive] instance [group Y] : group (locally_constant X Y) :=
{ mul_left_inv := by { intros, ext, simp only [mul_apply, inv_apply, one_apply, mul_left_inv] },
  div_eq_mul_inv := by { intros, ext, simp only [mul_apply, inv_apply, div_apply, div_eq_mul_inv] },
  .. locally_constant.monoid, .. locally_constant.has_inv, .. locally_constant.has_div }

@[to_additive] instance [comm_group Y] : comm_group (locally_constant X Y) :=
{ .. locally_constant.comm_monoid, .. locally_constant.group }

instance [distrib Y] : distrib (locally_constant X Y) :=
{ left_distrib := by { intros, ext, simp only [mul_apply, add_apply, mul_add] },
  right_distrib := by { intros, ext, simp only [mul_apply, add_apply, add_mul] },
  .. locally_constant.has_add, .. locally_constant.has_mul }

instance [non_unital_non_assoc_semiring Y] : non_unital_non_assoc_semiring (locally_constant X Y) :=
{ .. locally_constant.add_comm_monoid, .. locally_constant.has_mul,
  .. locally_constant.distrib, .. locally_constant.mul_zero_class }

instance [non_unital_semiring Y] : non_unital_semiring (locally_constant X Y) :=
{ .. locally_constant.semigroup, .. locally_constant.non_unital_non_assoc_semiring }

instance [non_assoc_semiring Y] : non_assoc_semiring (locally_constant X Y) :=
{ .. locally_constant.mul_one_class, .. locally_constant.non_unital_non_assoc_semiring }

/-- The constant-function embedding, as a ring hom.  -/
@[simps] def const_ring_hom [non_assoc_semiring Y] : Y →+* locally_constant X Y :=
{ to_fun    := const X,
  .. const_monoid_hom,
  .. const_add_monoid_hom, }

instance [semiring Y] : semiring (locally_constant X Y) :=
{ .. locally_constant.add_comm_monoid, .. locally_constant.monoid,
  .. locally_constant.distrib, .. locally_constant.mul_zero_class }

instance [comm_semiring Y] : comm_semiring (locally_constant X Y) :=
{ .. locally_constant.semiring, .. locally_constant.comm_monoid }

instance [ring Y] : ring (locally_constant X Y) :=
{ .. locally_constant.semiring, .. locally_constant.add_comm_group }

instance [comm_ring Y] : comm_ring (locally_constant X Y) :=
{ .. locally_constant.comm_semiring, .. locally_constant.ring }

variables {R : Type*}

instance [has_scalar R Y] : has_scalar R (locally_constant X Y) :=
{ smul := λ r f,
  { to_fun := r • f,
    is_locally_constant := ((is_locally_constant f).comp ((•) r) : _), } }

@[simp] lemma coe_smul [has_scalar R Y] (r : R) (f : locally_constant X Y) : ⇑(r • f) = r • f := rfl

lemma smul_apply [has_scalar R Y] (r : R) (f : locally_constant X Y) (x : X) :
  (r • f) x = r • (f x) :=
rfl

instance [monoid R] [mul_action R Y] : mul_action R (locally_constant X Y) :=
function.injective.mul_action _ coe_injective (λ _ _, rfl)

instance [monoid R] [add_monoid Y] [distrib_mul_action R Y] :
  distrib_mul_action R (locally_constant X Y) :=
function.injective.distrib_mul_action coe_fn_add_monoid_hom coe_injective (λ _ _, rfl)

instance [semiring R] [add_comm_monoid Y] [module R Y] : module R (locally_constant X Y) :=
function.injective.module R coe_fn_add_monoid_hom coe_injective (λ _ _, rfl)

section algebra

variables [comm_semiring R] [semiring Y] [algebra R Y]

instance : algebra R (locally_constant X Y) :=
{ to_ring_hom := const_ring_hom.comp $ algebra_map R Y,
  commutes'   := by { intros, ext, exact algebra.commutes' _ _, },
  smul_def'   := by { intros, ext, exact algebra.smul_def' _ _, }, }

@[simp] lemma coe_algebra_map (r : R) :
  ⇑(algebra_map R (locally_constant X Y) r) = algebra_map R (X → Y) r :=
rfl

end algebra

end locally_constant
