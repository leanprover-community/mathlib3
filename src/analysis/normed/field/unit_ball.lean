/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed.field.basic
import analysis.normed.group.ball_sphere

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`semigroup`, `comm_semigroup`, `monoid`, `comm_monoid`,
`group`, `comm_group`) on `metric.ball (0 : 𝕜) 1`, `metric.closed_ball (0 : 𝕜) 1`, and
`metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `non_unital_semi_normed_ring` to `normed_field`.
-/

open set metric

variables {𝕜 : Type*}

/-- Unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def subsemigroup.unit_ball (𝕜 : Type*) [non_unital_semi_normed_ring 𝕜] :
  subsemigroup 𝕜 :=
{ carrier := ball (0 : 𝕜) 1,
  mul_mem' := λ x y hx hy,
    begin
      rw [mem_ball_zero_iff] at *,
      exact (norm_mul_le x y).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _)
        hx hy.le)
    end }

instance [non_unital_semi_normed_ring 𝕜] : semigroup (ball (0 : 𝕜) 1) :=
mul_mem_class.to_semigroup (subsemigroup.unit_ball 𝕜)

instance [non_unital_semi_normed_ring 𝕜] : has_continuous_mul (ball (0 : 𝕜) 1) :=
(subsemigroup.unit_ball 𝕜).has_continuous_mul

instance [semi_normed_comm_ring 𝕜] : comm_semigroup (ball (0 : 𝕜) 1) :=
mul_mem_class.to_comm_semigroup (subsemigroup.unit_ball 𝕜)

instance [non_unital_semi_normed_ring 𝕜] : has_distrib_neg (ball (0 : 𝕜) 1) :=
subtype.coe_injective.has_distrib_neg (coe : ball (0 : 𝕜) 1 → 𝕜) (λ _, rfl) (λ _ _, rfl)

@[simp, norm_cast] lemma coe_mul_unit_ball [non_unital_semi_normed_ring 𝕜] (x y : ball (0 : 𝕜) 1) :
  ↑(x * y) = (x * y : 𝕜) := rfl

/-- Closed unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def subsemigroup.unit_closed_ball (𝕜 : Type*) [non_unital_semi_normed_ring 𝕜] :
  subsemigroup 𝕜 :=
{ carrier := closed_ball 0 1,
  mul_mem' := λ x y hx hy,
    begin
      rw [mem_closed_ball_zero_iff] at *,
      exact (norm_mul_le x y).trans (mul_le_one hx (norm_nonneg _) hy)
    end }

instance [non_unital_semi_normed_ring 𝕜] : semigroup (closed_ball (0 : 𝕜) 1) :=
mul_mem_class.to_semigroup (subsemigroup.unit_closed_ball 𝕜)

instance [non_unital_semi_normed_ring 𝕜] : has_distrib_neg (closed_ball (0 : 𝕜) 1) :=
subtype.coe_injective.has_distrib_neg (coe : closed_ball (0 : 𝕜) 1 → 𝕜) (λ _, rfl) (λ _ _, rfl)

instance [non_unital_semi_normed_ring 𝕜] : has_continuous_mul (closed_ball (0 : 𝕜) 1) :=
(subsemigroup.unit_closed_ball 𝕜).has_continuous_mul

@[simp, norm_cast]
lemma coe_mul_unit_closed_ball [non_unital_semi_normed_ring 𝕜] (x y : closed_ball (0 : 𝕜) 1) :
  ↑(x * y) = (x * y : 𝕜) := rfl

/-- Closed unit ball in a semi normed ring as a bundled `submonoid`. -/
def submonoid.unit_closed_ball (𝕜 : Type*) [semi_normed_ring 𝕜] [norm_one_class 𝕜] :
  submonoid 𝕜 :=
{ carrier := closed_ball 0 1,
  one_mem' := mem_closed_ball_zero_iff.2 norm_one.le,
  .. subsemigroup.unit_closed_ball 𝕜 }

instance [semi_normed_ring 𝕜] [norm_one_class 𝕜] : monoid (closed_ball (0 : 𝕜) 1) :=
submonoid_class.to_monoid (submonoid.unit_closed_ball 𝕜)

instance [semi_normed_comm_ring 𝕜] [norm_one_class 𝕜] : comm_monoid (closed_ball (0 : 𝕜) 1) :=
submonoid_class.to_comm_monoid (submonoid.unit_closed_ball 𝕜)

@[simp, norm_cast]
lemma coe_one_unit_closed_ball [semi_normed_ring 𝕜] [norm_one_class 𝕜] :
  ((1 : closed_ball (0 : 𝕜) 1) : 𝕜) = 1 := rfl

@[simp, norm_cast]
lemma coe_pow_unit_closed_ball [semi_normed_ring 𝕜] [norm_one_class 𝕜]
  (x : closed_ball (0 : 𝕜) 1) (n : ℕ) :
  ↑(x ^ n) = (x ^ n : 𝕜) := rfl

/-- Unit sphere in a normed division ring as a bundled `submonoid`. -/
def submonoid.unit_sphere (𝕜 : Type*) [normed_division_ring 𝕜] : submonoid 𝕜 :=
{ carrier := sphere (0 : 𝕜) 1,
  mul_mem' := λ x y hx hy, by { rw [mem_sphere_zero_iff_norm] at *, simp * },
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one }

instance [normed_division_ring 𝕜] : has_inv (sphere (0 : 𝕜) 1) :=
⟨λ x, ⟨x⁻¹, mem_sphere_zero_iff_norm.2 $
  by rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]⟩⟩

@[simp, norm_cast]
lemma coe_inv_unit_sphere [normed_division_ring 𝕜] (x : sphere (0 : 𝕜) 1) : ↑x⁻¹ = (x⁻¹ : 𝕜) := rfl

instance [normed_division_ring 𝕜] : has_div (sphere (0 : 𝕜) 1) :=
⟨λ x y, ⟨x / y, mem_sphere_zero_iff_norm.2 $ by rw [norm_div, mem_sphere_zero_iff_norm.1 x.coe_prop,
  mem_sphere_zero_iff_norm.1 y.coe_prop, div_one]⟩⟩

@[simp, norm_cast]
lemma coe_div_unit_sphere [normed_division_ring 𝕜] (x y : sphere (0 : 𝕜) 1) :
  ↑(x / y) = (x / y : 𝕜) := rfl

instance [normed_division_ring 𝕜] : has_pow (sphere (0 : 𝕜) 1) ℤ :=
⟨λ x n, ⟨x ^ n, by rw [mem_sphere_zero_iff_norm, norm_zpow,
    mem_sphere_zero_iff_norm.1 x.coe_prop, one_zpow]⟩⟩

@[simp, norm_cast]
lemma coe_zpow_unit_sphere [normed_division_ring 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℤ) :
  ↑(x ^ n) = (x ^ n : 𝕜) := rfl

instance [normed_division_ring 𝕜] : monoid (sphere (0 : 𝕜) 1) :=
submonoid_class.to_monoid (submonoid.unit_sphere 𝕜)

@[simp, norm_cast]
lemma coe_one_unit_sphere [normed_division_ring 𝕜] : ((1 : sphere (0 : 𝕜) 1) : 𝕜) = 1 := rfl

@[simp, norm_cast]
lemma coe_mul_unit_sphere [normed_division_ring 𝕜] (x y : sphere (0 : 𝕜) 1) :
  ↑(x * y) = (x * y : 𝕜) := rfl

@[simp, norm_cast]
lemma coe_pow_unit_sphere [normed_division_ring 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℕ) :
  ↑(x ^ n) = (x ^ n : 𝕜) := rfl

/-- Monoid homomorphism from the unit sphere to the group of units. -/
def unit_sphere_to_units (𝕜 : Type*) [normed_division_ring 𝕜] : sphere (0 : 𝕜) 1 →* units 𝕜 :=
units.lift_right (submonoid.unit_sphere 𝕜).subtype (λ x, units.mk0 x $ ne_zero_of_mem_unit_sphere _)
  (λ x, rfl)

@[simp] lemma unit_sphere_to_units_apply_coe [normed_division_ring 𝕜] (x : sphere (0 : 𝕜) 1) :
  (unit_sphere_to_units 𝕜 x : 𝕜) = x := rfl

lemma unit_sphere_to_units_injective [normed_division_ring 𝕜] :
  function.injective (unit_sphere_to_units 𝕜) :=
λ x y h, subtype.eq $ by convert congr_arg units.val h

instance [normed_division_ring 𝕜] : group (sphere (0 : 𝕜) 1) :=
unit_sphere_to_units_injective.group (unit_sphere_to_units 𝕜) (units.ext rfl)
  (λ x y, units.ext rfl) (λ x, units.ext rfl) (λ x y, units.ext $ div_eq_mul_inv _ _)
  (λ x n, units.ext (units.coe_pow (unit_sphere_to_units 𝕜 x) n).symm)
  (λ x n, units.ext (units.coe_zpow (unit_sphere_to_units 𝕜 x) n).symm)

instance [normed_division_ring 𝕜] : has_distrib_neg (sphere (0 : 𝕜) 1) :=
subtype.coe_injective.has_distrib_neg (coe : sphere (0 : 𝕜) 1 → 𝕜) (λ _, rfl) (λ _ _, rfl)

instance [normed_division_ring 𝕜] : topological_group (sphere (0 : 𝕜) 1) :=
{ to_has_continuous_mul := (submonoid.unit_sphere 𝕜).has_continuous_mul,
  continuous_inv := (continuous_subtype_coe.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _ }

instance [normed_field 𝕜] : comm_group (sphere (0 : 𝕜) 1) :=
{ .. metric.sphere.group,
  .. submonoid_class.to_comm_monoid (submonoid.unit_sphere 𝕜) }
