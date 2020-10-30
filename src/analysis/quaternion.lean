/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import data.quaternion analysis.normed_space.real_inner_product

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

## Notation

* `ℍ` : quaternions

## TODO

* Define normed algebras and prove that `ℍ` form a normed division algebra over `ℝ`.
* Prove that `ℍ` form a normed algebra over `ℂ`.

## Tags

quaternion, normed_ring, normed_space
-/

notation `ℍ` := ℍ[ℝ]

namespace quaternion

@[simps] instance : has_inner ℍ := ⟨λ a b, (a * b.conj).re⟩

lemma inner_self (a : ℍ) : inner a a = norm_sq ℝ a := rfl

instance : inner_product_space ℍ :=
{ comm := λ x y, by rw [has_inner_inner, has_inner_inner, ← conj_mul_conj, conj_re],
  add_left := λ x y z, by simp only [has_inner_inner, add_mul, has_add_re],
  smul_left := λ r x y,
    by simp only [has_inner_inner, algebra.smul_mul_assoc, smul_re, smul_eq_mul],
  nonneg := λ x, norm_sq_nonneg,
  definite := λ x, norm_sq_eq_zero.1,
  .. quaternion.algebra }

lemma norm_sq_eq_norm_square (a : ℍ) : norm_sq ℝ a = ∥a∥ * ∥a∥ :=
by rw [← inner_self, inner_self_eq_norm_square]

@[simp] lemma norm_one : ∥(1 : ℍ)∥ = 1 :=
by rw [norm_eq_sqrt_inner, inner_self, (norm_sq ℝ).map_one, real.sqrt_one]

@[simp] lemma norm_mul (a b : ℍ) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
begin
  simp only [norm_eq_sqrt_inner, inner_self, (norm_sq ℝ).map_mul],
  exact real.sqrt_mul norm_sq_nonneg _
end

lemma norm_coe (a : ℝ) : ∥(a : ℍ)∥ = ∥a∥ :=
by rw [norm_eq_sqrt_inner, inner_self, norm_sq_coe, real.sqrt_sqr_eq_abs, real.norm_eq_abs]

noncomputable instance : normed_ring ℍ :=
{ dist_eq := λ _ _, rfl,
  norm_mul := λ a b, le_of_eq (norm_mul a b) }

noncomputable instance : normed_space ℝ ℍ :=
{ norm_smul := λ r a, by rw [← norm_coe, ← norm_mul, coe_mul_eq_smul],
  .. quaternion.algebra }

end quaternion
