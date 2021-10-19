/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.quaternion
import analysis.inner_product_space.basic

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

## Notation

The following notation is available with `open_locale quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/

localized "notation `ℍ` := quaternion ℝ" in quaternion
open_locale real_inner_product_space

noncomputable theory

namespace quaternion

instance : has_inner ℝ ℍ := ⟨λ a b, (a * b.conj).re⟩

lemma inner_self (a : ℍ) : ⟪a, a⟫ = norm_sq a := rfl

lemma inner_def (a b : ℍ) : ⟪a, b⟫ = (a * b.conj).re := rfl

instance : inner_product_space ℝ ℍ :=
inner_product_space.of_core
{ inner := has_inner.inner,
  conj_sym := λ x y, by simp [inner_def, mul_comm],
  nonneg_re := λ x, norm_sq_nonneg,
  definite := λ x, norm_sq_eq_zero.1,
  add_left := λ x y z, by simp only [inner_def, add_mul, add_re],
  smul_left := λ x y r, by simp [inner_def] }

lemma norm_sq_eq_norm_sq (a : ℍ) : norm_sq a = ∥a∥ * ∥a∥ :=
by rw [← inner_self, real_inner_self_eq_norm_sq]

instance : norm_one_class ℍ :=
⟨by rw [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_one, real.sqrt_one]⟩

@[simp] lemma norm_mul (a b : ℍ) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
begin
  simp only [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_mul],
  exact real.sqrt_mul norm_sq_nonneg _
end

@[simp, norm_cast] lemma norm_coe (a : ℝ) : ∥(a : ℍ)∥ = ∥a∥ :=
by rw [norm_eq_sqrt_real_inner, inner_self, norm_sq_coe, real.sqrt_sq_eq_abs, real.norm_eq_abs]

noncomputable instance : normed_ring ℍ :=
{ dist_eq := λ _ _, rfl,
  norm_mul := λ a b, (norm_mul a b).le }

noncomputable instance : normed_algebra ℝ ℍ :=
{ norm_algebra_map_eq := norm_coe,
  to_algebra := quaternion.algebra }

instance : has_coe ℂ ℍ := ⟨λ z, ⟨z.re, z.im, 0, 0⟩⟩

@[simp, norm_cast] lemma coe_complex_re (z : ℂ) : (z : ℍ).re = z.re := rfl
@[simp, norm_cast] lemma coe_complex_im_i (z : ℂ) : (z : ℍ).im_i = z.im := rfl
@[simp, norm_cast] lemma coe_complex_im_j (z : ℂ) : (z : ℍ).im_j = 0 := rfl
@[simp, norm_cast] lemma coe_complex_im_k (z : ℂ) : (z : ℍ).im_k = 0 := rfl

@[simp, norm_cast] lemma coe_complex_add (z w : ℂ) : ↑(z + w) = (z + w : ℍ) := by ext; simp
@[simp, norm_cast] lemma coe_complex_mul (z w : ℂ) : ↑(z * w) = (z * w : ℍ) := by ext; simp
@[simp, norm_cast] lemma coe_complex_zero : ((0 : ℂ) : ℍ) = 0 := rfl
@[simp, norm_cast] lemma coe_complex_one : ((1 : ℂ) : ℍ) = 1 := rfl
@[simp, norm_cast] lemma coe_real_complex_mul (r : ℝ) (z : ℂ) : (r • z : ℍ) = ↑r * ↑z :=
by ext; simp
@[simp, norm_cast] lemma coe_complex_coe (r : ℝ) : ((r : ℂ) : ℍ) = r := rfl

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
def of_complex : ℂ →ₐ[ℝ] ℍ :=
{ to_fun := coe,
  map_one' := rfl,
  map_zero' := rfl,
  map_add' := coe_complex_add,
  map_mul' := coe_complex_mul,
  commutes' := λ x, rfl }

@[simp] lemma coe_of_complex : ⇑of_complex = coe := rfl

end quaternion
