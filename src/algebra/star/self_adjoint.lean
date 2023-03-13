/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.star.basic
import group_theory.subgroup.basic

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `self_adjoint R` (resp. `skew_adjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `is_star_normal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `star_module R₂ R`, then `self_adjoint R` has a natural
  `module (self_adjoint R₂) (self_adjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `module ℝ (self_adjoint R)`
  and not `module (self_adjoint ℂ) (self_adjoint R)`. We solve this issue by adding the typeclass
  `[has_trivial_star R₃]`, of which `ℝ` is an instance (registered in `data/real/basic`), and then
  add a `[module R₃ (self_adjoint R)]` instance whenever we have
  `[module R₃ R] [has_trivial_star R₃]`. (Another approach would have been to define
  `[star_invariant_scalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `is_skew_adjoint` to match `is_self_adjoint`.
* Define `λ z x, z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `conj_act` for groups), and then state the fact that `self_adjoint R` is
  invariant under it.

-/

variables {R A : Type*}

/-- An element is self-adjoint if it is equal to its star. -/
def is_self_adjoint [has_star R] (x : R) : Prop := star x = x

/-- An element of a star monoid is normal if it commutes with its adjoint. -/
class is_star_normal [has_mul R] [has_star R] (x : R) : Prop :=
(star_comm_self : commute (star x) x)

export is_star_normal (star_comm_self)

lemma star_comm_self' [has_mul R] [has_star R] (x : R) [is_star_normal x] :
  (star x) * x = x * star x :=
is_star_normal.star_comm_self

namespace is_self_adjoint

-- named to match `commute.all`
/-- All elements are self-adjoint when `star` is trivial. -/
lemma all [has_star R] [has_trivial_star R] (r : R) : is_self_adjoint r := star_trivial _

lemma star_eq [has_star R] {x : R} (hx : is_self_adjoint x) : star x = x := hx

lemma _root_.is_self_adjoint_iff [has_star R] {x : R} : is_self_adjoint x ↔ star x = x := iff.rfl

@[simp]
lemma star_iff [has_involutive_star R] {x : R} : is_self_adjoint (star x) ↔ is_self_adjoint x :=
by simpa only [is_self_adjoint, star_star] using eq_comm

@[simp]
lemma star_mul_self [semigroup R] [star_semigroup R] (x : R) : is_self_adjoint (star x * x) :=
by simp only [is_self_adjoint, star_mul, star_star]

@[simp]
lemma mul_star_self [semigroup R] [star_semigroup R] (x : R) : is_self_adjoint (x * star x) :=
by simpa only [star_star] using star_mul_self (star x)

/-- Functions in a `star_hom_class` preserve self-adjoint elements. -/
lemma star_hom_apply {F R S : Type*} [has_star R] [has_star S] [star_hom_class F R S]
  {x : R} (hx : is_self_adjoint x) (f : F) : is_self_adjoint (f x) :=
show star (f x) = f x, from map_star f x ▸ congr_arg f hx

section add_monoid
variables [add_monoid R] [star_add_monoid R]

variables (R)

lemma _root_.is_self_adjoint_zero : is_self_adjoint (0 : R) := star_zero R

variables {R}

lemma add {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y) : is_self_adjoint (x + y) :=
by simp only [is_self_adjoint_iff, star_add, hx.star_eq, hy.star_eq]

lemma bit0 {x : R} (hx : is_self_adjoint x) : is_self_adjoint (bit0 x) :=
by simp only [is_self_adjoint_iff, star_bit0, hx.star_eq]

end add_monoid

section add_group
variables [add_group R] [star_add_monoid R]

lemma neg {x : R} (hx : is_self_adjoint x) : is_self_adjoint (-x) :=
by simp only [is_self_adjoint_iff, star_neg, hx.star_eq]

lemma sub {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y) : is_self_adjoint (x - y) :=
by simp only [is_self_adjoint_iff, star_sub, hx.star_eq, hy.star_eq]

end add_group

section semigroup
variables [semigroup R] [star_semigroup R]

lemma conjugate {x : R} (hx : is_self_adjoint x) (z : R) : is_self_adjoint (z * x * star z) :=
by simp only [is_self_adjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

lemma conjugate' {x : R} (hx : is_self_adjoint x) (z : R) : is_self_adjoint (star z * x * z) :=
by simp only [is_self_adjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

lemma is_star_normal {x : R} (hx : is_self_adjoint x) : is_star_normal x :=
⟨by simp only [hx.star_eq]⟩

end semigroup

section monoid
variables [monoid R] [star_semigroup R]

variables (R)

lemma _root_.is_self_adjoint_one : is_self_adjoint (1 : R) := star_one R

variables {R}

lemma pow {x : R} (hx : is_self_adjoint x) (n : ℕ) : is_self_adjoint (x ^ n):=
by simp only [is_self_adjoint_iff, star_pow, hx.star_eq]

end monoid

section semiring
variables [semiring R] [star_ring R]

lemma bit1 {x : R} (hx : is_self_adjoint x) : is_self_adjoint (bit1 x) :=
by simp only [is_self_adjoint_iff, star_bit1, hx.star_eq]

@[simp] lemma _root_.is_self_adjoint_nat_cast (n : ℕ) : is_self_adjoint (n : R) :=
star_nat_cast _

end semiring

section comm_semigroup
variables [comm_semigroup R] [star_semigroup R]

lemma mul {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y) : is_self_adjoint (x * y) :=
by simp only [is_self_adjoint_iff, star_mul', hx.star_eq, hy.star_eq]

end comm_semigroup

section ring
variables [ring R] [star_ring R]

@[simp] lemma _root_.is_self_adjoint_int_cast (z : ℤ) : is_self_adjoint (z : R) :=
star_int_cast _

end ring

section division_ring
variables [division_ring R] [star_ring R]

lemma inv {x : R} (hx : is_self_adjoint x) : is_self_adjoint x⁻¹ :=
by simp only [is_self_adjoint_iff, star_inv', hx.star_eq]

lemma zpow {x : R} (hx : is_self_adjoint x) (n : ℤ) : is_self_adjoint (x ^ n):=
by simp only [is_self_adjoint_iff, star_zpow₀, hx.star_eq]

lemma _root_.is_self_adjoint_rat_cast (x : ℚ) : is_self_adjoint (x : R) :=
star_rat_cast _

end division_ring

section field
variables [field R] [star_ring R]

lemma div {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y) : is_self_adjoint (x / y) :=
by simp only [is_self_adjoint_iff, star_div', hx.star_eq, hy.star_eq]

end field

section has_smul
variables [has_star R] [add_monoid A] [star_add_monoid A] [has_smul R A] [star_module R A]

lemma smul {r : R} (hr : is_self_adjoint r) {x : A} (hx : is_self_adjoint x) :
  is_self_adjoint (r • x) :=
by simp only [is_self_adjoint_iff, star_smul, hr.star_eq, hx.star_eq]

end has_smul

end is_self_adjoint

variables (R)

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def self_adjoint [add_group R] [star_add_monoid R] : add_subgroup R :=
{ carrier := {x | is_self_adjoint x},
  zero_mem' := star_zero R,
  add_mem' := λ _ _ hx, hx.add,
  neg_mem' := λ _ hx, hx.neg }

/-- The skew-adjoint elements of a star additive group, as an additive subgroup. -/
def skew_adjoint [add_comm_group R] [star_add_monoid R] : add_subgroup R :=
{ carrier := {x | star x = -x},
  zero_mem' := show star (0 : R) = -0, by simp only [star_zero, neg_zero],
  add_mem' := λ x y (hx : star x = -x) (hy : star y = -y),
                show star (x + y) = -(x + y), by rw [star_add x y, hx, hy, neg_add],
  neg_mem' := λ x (hx : star x = -x), show star (-x) = (- -x), by simp only [hx, star_neg] }

variables {R}

namespace self_adjoint

section add_group
variables [add_group R] [star_add_monoid R]

lemma mem_iff {x : R} : x ∈ self_adjoint R ↔ star x = x :=
by { rw [←add_subgroup.mem_carrier], exact iff.rfl }

@[simp, norm_cast] lemma star_coe_eq {x : self_adjoint R} : star (x : R) = x := x.prop

instance : inhabited (self_adjoint R) := ⟨0⟩

end add_group

section ring
variables [ring R] [star_ring R]

instance : has_one (self_adjoint R) := ⟨⟨1, is_self_adjoint_one R⟩⟩

@[simp, norm_cast] lemma coe_one : ↑(1 : self_adjoint R) = (1 : R) := rfl

instance [nontrivial R] : nontrivial (self_adjoint R) := ⟨⟨0, 1, subtype.ne_of_val_ne zero_ne_one⟩⟩

instance : has_nat_cast (self_adjoint R) :=
⟨λ n, ⟨n, is_self_adjoint_nat_cast _⟩⟩

instance : has_int_cast (self_adjoint R) :=
⟨λ n, ⟨n, is_self_adjoint_int_cast _⟩ ⟩

instance : has_pow (self_adjoint R) ℕ :=
⟨λ x n, ⟨(x : R) ^ n, x.prop.pow n⟩⟩

@[simp, norm_cast] lemma coe_pow (x : self_adjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n := rfl

end ring

section non_unital_comm_ring
variables [non_unital_comm_ring R] [star_ring R]

instance : has_mul (self_adjoint R) :=
⟨λ x y, ⟨(x : R) * y, x.prop.mul y.prop⟩⟩

@[simp, norm_cast] lemma coe_mul (x y : self_adjoint R) : ↑(x * y) = (x : R) * y := rfl

end non_unital_comm_ring

section comm_ring
variables [comm_ring R] [star_ring R]

instance : comm_ring (self_adjoint R) :=
function.injective.comm_ring _ subtype.coe_injective
  (self_adjoint R).coe_zero coe_one (self_adjoint R).coe_add coe_mul (self_adjoint R).coe_neg
  (self_adjoint R).coe_sub (self_adjoint R).coe_nsmul (self_adjoint R).coe_zsmul coe_pow
  (λ _, rfl) (λ _, rfl)

end comm_ring

section field

variables [field R] [star_ring R]

instance : has_inv (self_adjoint R) :=
{ inv := λ x, ⟨(x.val)⁻¹, x.prop.inv⟩ }

@[simp, norm_cast] lemma coe_inv (x : self_adjoint R) : ↑(x⁻¹) = (x : R)⁻¹ := rfl

instance : has_div (self_adjoint R) :=
{ div := λ x y, ⟨x / y, x.prop.div y.prop⟩ }

@[simp, norm_cast] lemma coe_div (x y : self_adjoint R) : ↑(x / y) = (x / y : R) := rfl

instance : has_pow (self_adjoint R) ℤ :=
{ pow := λ x z, ⟨x ^ z, x.prop.zpow z⟩ }

@[simp, norm_cast] lemma coe_zpow (x : self_adjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z := rfl

instance : has_rat_cast (self_adjoint R) :=
⟨λ n, ⟨n, is_self_adjoint_rat_cast n⟩⟩

@[simp, norm_cast] lemma coe_rat_cast (x : ℚ) : ↑(x : self_adjoint R) = (x : R) :=
rfl

instance has_qsmul : has_smul ℚ (self_adjoint R) :=
⟨λ a x, ⟨a • x, by rw rat.smul_def; exact is_self_adjoint.mul (is_self_adjoint_rat_cast a) x.prop⟩⟩

@[simp, norm_cast] lemma coe_rat_smul (x : self_adjoint R) (a : ℚ) : ↑(a • x) = a • (x : R) :=
rfl

instance : field (self_adjoint R) :=
function.injective.field _ subtype.coe_injective
  (self_adjoint R).coe_zero coe_one (self_adjoint R).coe_add coe_mul (self_adjoint R).coe_neg
  (self_adjoint R).coe_sub coe_inv coe_div (self_adjoint R).coe_nsmul (self_adjoint R).coe_zsmul
  coe_rat_smul coe_pow coe_zpow (λ _, rfl) (λ _, rfl) coe_rat_cast

end field

section has_smul
variables [has_star R] [has_trivial_star R] [add_group A] [star_add_monoid A]

instance [has_smul R A] [star_module R A] : has_smul R (self_adjoint A) :=
⟨λ r x, ⟨r • x, (is_self_adjoint.all _).smul x.prop⟩⟩

@[simp, norm_cast] lemma coe_smul [has_smul R A] [star_module R A] (r : R) (x : self_adjoint A) :
  ↑(r • x) = r • (x : A) := rfl

instance [monoid R] [mul_action R A] [star_module R A] : mul_action R (self_adjoint A) :=
function.injective.mul_action coe subtype.coe_injective coe_smul

instance [monoid R] [distrib_mul_action R A] [star_module R A] :
  distrib_mul_action R (self_adjoint A) :=
function.injective.distrib_mul_action (self_adjoint A).subtype subtype.coe_injective coe_smul

end has_smul

section module
variables [has_star R] [has_trivial_star R] [add_comm_group A] [star_add_monoid A]

instance [semiring R] [module R A] [star_module R A] : module R (self_adjoint A) :=
function.injective.module R (self_adjoint A).subtype subtype.coe_injective coe_smul

end module

end self_adjoint

namespace skew_adjoint

section add_group
variables [add_comm_group R] [star_add_monoid R]

lemma mem_iff {x : R} : x ∈ skew_adjoint R ↔ star x = -x :=
by { rw [←add_subgroup.mem_carrier], exact iff.rfl }

@[simp, norm_cast] lemma star_coe_eq {x : skew_adjoint R} : star (x : R) = -x := x.prop

instance : inhabited (skew_adjoint R) := ⟨0⟩

lemma bit0_mem {x : R} (hx : x ∈ skew_adjoint R) : bit0 x ∈ skew_adjoint R :=
by rw [mem_iff, star_bit0, mem_iff.mp hx, bit0, bit0, neg_add]

end add_group

section ring
variables [ring R] [star_ring R]

lemma conjugate {x : R} (hx : x ∈ skew_adjoint R) (z : R) : z * x * star z ∈ skew_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

lemma conjugate' {x : R} (hx : x ∈ skew_adjoint R) (z : R) : star z * x * z ∈ skew_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

lemma is_star_normal_of_mem {x : R} (hx : x ∈ skew_adjoint R) : is_star_normal x :=
⟨by { simp only [mem_iff] at hx, simp only [hx, commute.neg_left] }⟩

instance (x : skew_adjoint R) : is_star_normal (x : R) :=
is_star_normal_of_mem (set_like.coe_mem _)

end ring

section has_smul
variables [has_star R] [has_trivial_star R] [add_comm_group A] [star_add_monoid A]

lemma smul_mem [monoid R] [distrib_mul_action R A] [star_module R A] (r : R) {x : A}
  (h : x ∈ skew_adjoint A) : r • x ∈ skew_adjoint A :=
by rw [mem_iff, star_smul, star_trivial, mem_iff.mp h, smul_neg r]

instance [monoid R] [distrib_mul_action R A] [star_module R A] : has_smul R (skew_adjoint A) :=
⟨λ r x, ⟨r • x, smul_mem r x.prop⟩⟩

@[simp, norm_cast] lemma coe_smul [monoid R] [distrib_mul_action R A] [star_module R A]
  (r : R) (x : skew_adjoint A) : ↑(r • x) = r • (x : A) := rfl

instance [monoid R] [distrib_mul_action R A] [star_module R A] :
  distrib_mul_action R (skew_adjoint A) :=
function.injective.distrib_mul_action (skew_adjoint A).subtype subtype.coe_injective coe_smul

instance [semiring R] [module R A] [star_module R A] : module R (skew_adjoint A) :=
function.injective.module R (skew_adjoint A).subtype subtype.coe_injective coe_smul

end has_smul

end skew_adjoint

/-- Scalar multiplication of a self-adjoint element by a skew-adjoint element produces a
skew-adjoint element. -/
lemma is_self_adjoint.smul_mem_skew_adjoint [ring R] [add_comm_group A] [module R A]
  [star_add_monoid R] [star_add_monoid A] [star_module R A] {r : R}
  (hr : r ∈ skew_adjoint R) {a : A} (ha : is_self_adjoint a) :
  r • a ∈ skew_adjoint A :=
(star_smul _ _).trans $ (congr_arg2 _ hr ha).trans $ neg_smul _ _

/-- Scalar multiplication of a skew-adjoint element by a skew-adjoint element produces a
self-adjoint element. -/
lemma is_self_adjoint_smul_of_mem_skew_adjoint [ring R] [add_comm_group A] [module R A]
  [star_add_monoid R] [star_add_monoid A] [star_module R A] {r : R}
  (hr : r ∈ skew_adjoint R) {a : A} (ha : a ∈ skew_adjoint A) :
  is_self_adjoint (r • a) :=
(star_smul _ _).trans $ (congr_arg2 _ hr ha).trans $ neg_smul_neg _ _

instance is_star_normal_zero [semiring R] [star_ring R] : is_star_normal (0 : R) :=
⟨by simp only [star_comm_self, star_zero]⟩

instance is_star_normal_one [monoid R] [star_semigroup R] : is_star_normal (1 : R) :=
⟨by simp only [star_comm_self, star_one]⟩

instance is_star_normal_star_self [monoid R] [star_semigroup R] {x : R} [is_star_normal x] :
  is_star_normal (star x) :=
⟨show star (star x) * (star x) = (star x) * star (star x), by rw [star_star, star_comm_self']⟩

@[priority 100] -- see Note [lower instance priority]
instance has_trivial_star.is_star_normal [monoid R] [star_semigroup R]
  [has_trivial_star R] {x : R} : is_star_normal x :=
⟨by rw [star_trivial]⟩

@[priority 100] -- see Note [lower instance priority]
instance comm_monoid.is_star_normal [comm_monoid R] [star_semigroup R] {x : R} :
  is_star_normal x :=
⟨mul_comm _ _⟩
