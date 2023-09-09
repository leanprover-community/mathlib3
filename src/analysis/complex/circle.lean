/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.special_functions.exp
import topology.continuous_function.basic
import analysis.normed.field.unit_ball

/-!
# The circle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `circle` to be the metric sphere (`metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `exp_map_circle` to be the natural map `λ t, exp (t * I)` from `ℝ` to
`circle`, and show that this map is a group homomorphism.

## Implementation notes

Because later (in `geometry.manifold.instances.sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | norm_sq z = 1}`, which
is the kernel of the homomorphism `complex.norm_sq` from `ℂ` to `ℝ`.

-/

noncomputable theory

open complex metric
open_locale complex_conjugate

/-- The unit circle in `ℂ`, here given the structure of a submonoid of `ℂ`. -/
def circle : submonoid ℂ := submonoid.unit_sphere ℂ

@[simp] lemma mem_circle_iff_abs {z : ℂ} : z ∈ circle ↔ abs z = 1 := mem_sphere_zero_iff_norm

lemma circle_def : ↑circle = {z : ℂ | abs z = 1} := set.ext $ λ z, mem_circle_iff_abs

@[simp] lemma abs_coe_circle (z : circle) : abs z = 1 :=
mem_circle_iff_abs.mp z.2

lemma mem_circle_iff_norm_sq {z : ℂ} : z ∈ circle ↔ norm_sq z = 1 :=
by simp [complex.abs]

@[simp] lemma norm_sq_eq_of_mem_circle (z : circle) : norm_sq z = 1 := by simp [norm_sq_eq_abs]

lemma ne_zero_of_mem_circle (z : circle) : (z:ℂ) ≠ 0 := ne_zero_of_mem_unit_sphere z

instance : comm_group circle := metric.sphere.comm_group

@[simp] lemma coe_inv_circle (z : circle) : ↑(z⁻¹) = (z : ℂ)⁻¹ := rfl

lemma coe_inv_circle_eq_conj (z : circle) : ↑(z⁻¹) = conj (z : ℂ) :=
by rw [coe_inv_circle, inv_def, norm_sq_eq_of_mem_circle, inv_one, of_real_one, mul_one]

@[simp] lemma coe_div_circle (z w : circle) : ↑(z / w) = (z:ℂ) / w :=
circle.subtype.map_div z w

/-- The elements of the circle embed into the units. -/
def circle.to_units : circle →* units ℂ := unit_sphere_to_units ℂ

-- written manually because `@[simps]` was slow and generated the wrong lemma
@[simp] lemma circle.to_units_apply (z : circle) :
  circle.to_units z = units.mk0 z (ne_zero_of_mem_circle z) := rfl

instance : compact_space circle := metric.sphere.compact_space _ _

instance : topological_group circle := metric.sphere.topological_group

/-- If `z` is a nonzero complex number, then `conj z / z` belongs to the unit circle. -/
@[simps] def circle.of_conj_div_self (z : ℂ) (hz : z ≠ 0) : circle :=
⟨conj z / z, mem_circle_iff_abs.2 $ by rw [map_div₀, abs_conj, div_self (complex.abs.ne_zero hz)]⟩

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def exp_map_circle : C(ℝ, circle) :=
{ to_fun := λ t, ⟨exp (t * I), by simp [exp_mul_I, abs_cos_add_sin_mul_I]⟩ }

@[simp] lemma exp_map_circle_apply (t : ℝ) : ↑(exp_map_circle t) = complex.exp (t * complex.I) :=
rfl

@[simp] lemma exp_map_circle_zero : exp_map_circle 0 = 1 :=
subtype.ext $ by rw [exp_map_circle_apply, of_real_zero, zero_mul, exp_zero, submonoid.coe_one]

@[simp] lemma exp_map_circle_add (x y : ℝ) :
  exp_map_circle (x + y) = exp_map_circle x * exp_map_circle y :=
subtype.ext $ by simp only [exp_map_circle_apply, submonoid.coe_mul, of_real_add, add_mul,
  complex.exp_add]

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`, considered as a homomorphism of
groups. -/
@[simps]
def exp_map_circle_hom : ℝ →+ (additive circle) :=
{ to_fun := additive.of_mul ∘ exp_map_circle,
  map_zero' := exp_map_circle_zero,
  map_add' := exp_map_circle_add }

@[simp] lemma exp_map_circle_sub (x y : ℝ) :
  exp_map_circle (x - y) = exp_map_circle x / exp_map_circle y :=
exp_map_circle_hom.map_sub x y

@[simp] lemma exp_map_circle_neg (x : ℝ) : exp_map_circle (-x) = (exp_map_circle x)⁻¹ :=
exp_map_circle_hom.map_neg x
