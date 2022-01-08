/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.special_functions.exp
import topology.continuous_function.basic

/-!
# The circle

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
def circle : submonoid ℂ :=
{ carrier := sphere (0:ℂ) 1,
  one_mem' := by simp,
  mul_mem' := λ a b, begin
    simp only [norm_eq_abs, mem_sphere_zero_iff_norm],
    intros ha hb,
    simp [ha, hb],
  end }

@[simp] lemma mem_circle_iff_abs {z : ℂ} : z ∈ circle ↔ abs z = 1 := mem_sphere_zero_iff_norm

lemma circle_def : ↑circle = {z : ℂ | abs z = 1} := set.ext $ λ z, mem_circle_iff_abs

@[simp] lemma abs_coe_circle (z : circle) : abs z = 1 :=
mem_circle_iff_abs.mp z.2

lemma mem_circle_iff_norm_sq {z : ℂ} : z ∈ circle ↔ norm_sq z = 1 :=
by rw [mem_circle_iff_abs, complex.abs, real.sqrt_eq_one]

@[simp] lemma norm_sq_eq_of_mem_circle (z : circle) : norm_sq z = 1 := by simp [norm_sq_eq_abs]

lemma nonzero_of_mem_circle (z : circle) : (z:ℂ) ≠ 0 := nonzero_of_mem_unit_sphere z

instance : group circle :=
{ inv := λ z, ⟨conj (z : ℂ), by simp⟩,
  mul_left_inv := λ z, subtype.ext $ by { simp [has_inv.inv, ← norm_sq_eq_conj_mul_self,
    ← mul_self_abs] },
  .. circle.to_monoid }

lemma coe_inv_circle_eq_conj (z : circle) : ↑(z⁻¹) = (conj : ring_aut ℂ) z := rfl

@[simp] lemma coe_inv_circle (z : circle) : ↑(z⁻¹) = (z : ℂ)⁻¹ :=
begin
  rw coe_inv_circle_eq_conj,
  apply eq_inv_of_mul_right_eq_one,
  rw [mul_comm, ← complex.norm_sq_eq_conj_mul_self],
  simp,
end

@[simp] lemma coe_div_circle (z w : circle) : ↑(z / w) = (z:ℂ) / w :=
show ↑(z * w⁻¹) = (z:ℂ) * w⁻¹, by simp

instance : compact_space circle := metric.sphere.compact_space _ _

-- the following result could instead be deduced from the Lie group structure on the circle using
-- `topological_group_of_lie_group`, but that seems a little awkward since one has to first provide
-- and then forget the model space
instance : topological_group circle :=
{ continuous_mul := let h : continuous (λ x : circle, (x : ℂ)) := continuous_subtype_coe in
    continuous_induced_rng (continuous_mul.comp (h.prod_map h)),
  continuous_inv := continuous_induced_rng $
    complex.conj_cle.continuous.comp continuous_subtype_coe }

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
