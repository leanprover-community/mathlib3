/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import measure_theory.l2_space
import measure_theory.haar_measure
import geometry.manifold.instances.circle

/-!

# Fourier analysis on the circle

This file contains some first steps towards Fourier series.

## Main definitions

* `haar_circle`, Haar measure on the circle, normalized to have total measure `1`
* instances `measure_space`, `probability_measure` for the circle with respect to this measure
* for `n : ℤ`, `fourier n` is the monomial `λ z, z ^ n`, bundled as a continuous map from `circle`
  to `ℂ`

## Main statements

The theorem `orthonormal_fourier` states that the functions `fourier n`, when sent via
`continuous_map.to_Lp` to the L^2 space on the circle, form an orthonormal set.

## TODO

* Show that `submodule.span fourier` is dense in `C(circle, ℂ)`, i.e. that its
  `submodule.topological_closure` is `⊤`.  This follows from the Stone-Weierstrass theorem after
  checking that it is a subalgebra, closed under conjugation, and separates points.
* Show that the image of `submodule.span fourier` under `continuous_map.to_Lp` is dense in the
  `L^2` space on the circle, and thus that the functions `fourier` form a Hilbert basis.  This
  follows from the previous result using general theory on approximation by continuous functions.

-/

noncomputable theory
open topological_space continuous_map measure_theory measure_theory.measure

local attribute [instance] fact_one_le_two_ennreal

section haar_circle
/-! We make the circle into a measure space, using the Haar measure normalized to have total
measure 1. -/

instance : measurable_space circle := borel circle
instance : borel_space circle := ⟨rfl⟩

/-- Haar measure on the circle, normalized to have total measure 1. -/
def haar_circle : measure circle := haar_measure positive_compacts_univ

instance : probability_measure haar_circle := ⟨haar_measure_self⟩

instance : measure_space circle :=
{ volume := haar_circle,
  .. circle.measurable_space }

end haar_circle

section fourier

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as bundled
continuous maps from `circle` to `ℂ`. -/
def fourier (n : ℤ) : C(circle, ℂ) :=
{ to_fun := λ z, z ^ n,
  continuous_to_fun := begin
    rw continuous_iff_continuous_at,
    intros z,
    exact (continuous_at_fpow (nonzero_of_mem_circle z) n).comp
      continuous_subtype_coe.continuous_at,
  end }

@[simp] lemma fourier_apply {n : ℤ} {z : circle} : fourier n z = z ^ n := rfl

@[simp] lemma fourier_zero {z : circle} : fourier 0 z = 1 := rfl

lemma conj_fourier {n : ℤ} {z : circle} : complex.conj (fourier n z) = fourier (-n) z :=
by simp [← coe_inv_circle_eq_conj z]

lemma mul_fourier {m n : ℤ} {z : circle} : (fourier m z) * (fourier n z) = fourier (m + n) z :=
by simp [fpow_add (nonzero_of_mem_circle z)]

/-- For `n ≠ 0`, a rotation by `n⁻¹ * real.pi` negates the monomial `z ^ n`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (z : circle) :
  fourier n ((exp_map_circle (n⁻¹ * real.pi) * z)) = - fourier n z :=
begin
  have : ↑n * ((↑n)⁻¹ * ↑real.pi * complex.I) = ↑real.pi * complex.I,
  { have : (n:ℂ) ≠ 0 := by exact_mod_cast hn,
    field_simp,
    ring },
  simp [mul_fpow, ← complex.exp_int_mul, complex.exp_pi_mul_I, this]
end

/-- The monomials `z ^ n` are an orthonormal set with respect to Haar measure on the circle. -/
lemma orthonormal_fourier : orthonormal ℂ (λ n, to_Lp ℂ 2 haar_circle ℂ (fourier n)) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp haar_circle (fourier i) (fourier j),
  split_ifs,
  { simp [h, probability_measure.measure_univ, conj_fourier, mul_fourier, -fourier_apply] },
  simp only [conj_fourier, mul_fourier, is_R_or_C.conj_to_complex],
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  exact integral_zero_of_mul_left_eq_neg (is_mul_left_invariant_haar_measure _)
    (fourier (-i + j)).continuous.measurable (fourier_add_half_inv_index hij)
end

end fourier
