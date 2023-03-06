/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
import algebra.quaternion
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import topology.algebra.algebra

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

We show that the norm on `ℍ[ℝ]` agrees with the euclidean norm of its components.

## Notation

The following notation is available with `open_locale quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/

localized "notation (name := quaternion.real) `ℍ` := quaternion ℝ" in quaternion
open_locale real_inner_product_space

namespace quaternion

instance : has_inner ℝ ℍ := ⟨λ a b, (a * b.conj).re⟩

lemma inner_self (a : ℍ) : ⟪a, a⟫ = norm_sq a := rfl

lemma inner_def (a b : ℍ) : ⟪a, b⟫ = (a * b.conj).re := rfl

noncomputable instance : inner_product_space ℝ ℍ :=
inner_product_space.of_core
{ inner := has_inner.inner,
  conj_sym := λ x y, by simp [inner_def, mul_comm],
  nonneg_re := λ x, norm_sq_nonneg,
  definite := λ x, norm_sq_eq_zero.1,
  add_left := λ x y z, by simp only [inner_def, add_mul, add_re],
  smul_left := λ x y r, by simp [inner_def] }

lemma norm_sq_eq_norm_sq (a : ℍ) : norm_sq a = ‖a‖ * ‖a‖ :=
by rw [← inner_self, real_inner_self_eq_norm_mul_norm]

instance : norm_one_class ℍ :=
⟨by rw [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_one, real.sqrt_one]⟩

@[simp, norm_cast] lemma norm_coe (a : ℝ) : ‖(a : ℍ)‖ = ‖a‖ :=
by rw [norm_eq_sqrt_real_inner, inner_self, norm_sq_coe, real.sqrt_sq_eq_abs, real.norm_eq_abs]

@[simp, norm_cast] lemma nnnorm_coe (a : ℝ) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
subtype.ext $ norm_coe a

@[simp] lemma norm_conj (a : ℍ) : ‖conj a‖ = ‖a‖ :=
by simp_rw [norm_eq_sqrt_real_inner, inner_self, norm_sq_conj]

@[simp] lemma nnnorm_conj (a : ℍ) : ‖conj a‖₊ = ‖a‖₊ :=
subtype.ext $ norm_conj a

noncomputable instance : normed_division_ring ℍ :=
{ dist_eq := λ _ _, rfl,
  norm_mul' := λ a b, by { simp only [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_mul],
                           exact real.sqrt_mul norm_sq_nonneg _ } }

instance : normed_algebra ℝ ℍ :=
{ norm_smul_le := λ a x, (norm_smul a x).le,
  to_algebra := (quaternion.algebra : algebra ℝ ℍ) }

instance : cstar_ring ℍ :=
{ norm_star_mul_self := λ x, (norm_mul _ _).trans $ congr_arg (* ‖x‖) (norm_conj x) }

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

/-- The norm of the components as a euclidean vector equals the norm of the quaternion. -/
lemma norm_pi_Lp_equiv_symm_equiv_tuple (x : ℍ) :
  ‖(pi_Lp.equiv 2 (λ _ : fin 4, _)).symm (equiv_tuple ℝ x)‖ = ‖x‖ :=
begin
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_self, norm_sq_def', pi_Lp.inner_apply,
    fin.sum_univ_four],
  simp_rw [is_R_or_C.inner_apply, star_ring_end_apply, star_trivial, ←sq],
  refl,
end

/-- `quaternion_algebra.linear_equiv_tuple` as a `linear_isometry_equiv`. -/
@[simps apply symm_apply]
noncomputable def linear_isometry_equiv_tuple : ℍ ≃ₗᵢ[ℝ] euclidean_space ℝ (fin 4) :=
{ to_fun := λ a, (pi_Lp.equiv _ (λ _ : fin 4, _)).symm ![a.1, a.2, a.3, a.4],
  inv_fun := λ a, ⟨a 0, a 1, a 2, a 3⟩,
  norm_map' := norm_pi_Lp_equiv_symm_equiv_tuple,
  ..(quaternion_algebra.linear_equiv_tuple (-1 : ℝ) (-1 : ℝ)).trans
      (pi_Lp.linear_equiv 2 ℝ (λ _ : fin 4, ℝ)).symm }

@[continuity] lemma continuous_conj : continuous (conj : ℍ → ℍ) :=
continuous_star

@[continuity] lemma continuous_coe : continuous (coe : ℝ → ℍ) :=
continuous_algebra_map ℝ ℍ

@[continuity] lemma continuous_norm_sq : continuous (norm_sq : ℍ → ℝ) :=
by simpa [←norm_sq_eq_norm_sq]
  using (continuous_norm.mul continuous_norm : continuous (λ q : ℍ, ‖q‖ * ‖q‖))

@[continuity] lemma continuous_re : continuous (λ q : ℍ, q.re) :=
(continuous_apply 0).comp linear_isometry_equiv_tuple.continuous

@[continuity] lemma continuous_im_i : continuous (λ q : ℍ, q.im_i) :=
(continuous_apply 1).comp linear_isometry_equiv_tuple.continuous

@[continuity] lemma continuous_im_j : continuous (λ q : ℍ, q.im_j) :=
(continuous_apply 2).comp linear_isometry_equiv_tuple.continuous

@[continuity] lemma continuous_im_k : continuous (λ q : ℍ, q.im_k) :=
(continuous_apply 3).comp linear_isometry_equiv_tuple.continuous

@[continuity] lemma continuous_im : continuous (λ q : ℍ, q.im) :=
by simpa only [←sub_self_re] using continuous_id.sub (continuous_coe.comp continuous_re)

instance : complete_space ℍ :=
begin
  have : uniform_embedding linear_isometry_equiv_tuple.to_linear_equiv.to_equiv.symm :=
    linear_isometry_equiv_tuple.to_continuous_linear_equiv.symm.uniform_embedding,
  exact (complete_space_congr this).1 (by apply_instance)
end

end quaternion
