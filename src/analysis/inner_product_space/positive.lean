/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.adjoint
import analysis.inner_product_space.spectrum

/-!
# Positive operators

In this file we define positive operators in a Hilbert space. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

for linear maps:
* `is_positive` : a linear map is positive if it is symmetric and `∀ x, 0 ≤ re ⟪T x, x⟫`

for continuous linear maps:
* `is_positive` : a continuous linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`

## Main statements

for linear maps:
* `linear_map.is_positive.conj_adjoint` : if `T : E →ₗ[𝕜] E` and `E` is a finite-dimensional space,
  then for any `S : E →ₗ[𝕜] F`, we have `S.comp (T.comp S.adjoint)` is also positive.

for continuous linear maps:
* `continuous_linear_map.is_positive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `continuous_linear_map.is_positive_iff_complex` : in a ***complex*** hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/
open inner_product_space is_R_or_C
open_locale inner_product complex_conjugate

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [normed_add_comm_group F]
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace linear_map

/-- `T` is (semi-definite) **positive** if `T` is symmetric
and `∀ x : V, 0 ≤ re ⟪x, T x⟫` -/
def is_positive (T : E →ₗ[𝕜] E) : Prop :=
T.is_symmetric ∧ ∀ x : E, 0 ≤ re ⟪x, T x⟫

lemma is_positive_zero : (0 : E →ₗ[𝕜] E).is_positive :=
begin
  refine ⟨is_symmetric_zero, λ x, _⟩,
  simp_rw [zero_apply, inner_re_zero_right],
end

lemma is_positive_one : (1 : E →ₗ[𝕜] E).is_positive :=
⟨is_symmetric_id, λ x, inner_self_nonneg⟩

lemma is_positive.add {S T : E →ₗ[𝕜] E} (hS : S.is_positive) (hT : T.is_positive) :
  (S + T).is_positive :=
begin
  refine ⟨is_symmetric.add hS.1 hT.1, λ x, _⟩,
  rw [add_apply, inner_add_right, map_add],
  exact add_nonneg (hS.2 _) (hT.2 _),
end

lemma is_positive.inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪T x, x⟫ :=
by { rw inner_re_symm, exact hT.2 x, }

lemma is_positive.inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪x, T x⟫ :=
hT.2 x

/-- a linear projection onto `U` along its complement `V` is positive if
and only if `U` and `V` are orthogonal -/
lemma linear_proj_is_positive_iff {U V : submodule 𝕜 E} (hUV : is_compl U V) :
  (U.subtype.comp (U.linear_proj_of_is_compl V hUV)).is_positive ↔ U ⟂ V :=
begin
  split,
  { intros h u hu v hv,
    let a : U := ⟨u, hu⟩,
    let b : V := ⟨v, hv⟩,
    have hau : u = a := rfl,
    have hbv : v = b := rfl,
    rw [hau, ← submodule.linear_proj_of_is_compl_apply_left hUV a,
        ← submodule.subtype_apply _, ← comp_apply, ← h.1 _ _,
        comp_apply, hbv, submodule.linear_proj_of_is_compl_apply_right hUV b,
        map_zero, inner_zero_left], },
  { intro h,
    have : (U.subtype.comp (U.linear_proj_of_is_compl V hUV)).is_symmetric,
    { intros x y,
      nth_rewrite 0 ← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hUV y,
      nth_rewrite 1 ← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hUV x,
      simp_rw [inner_add_right, inner_add_left, comp_apply, submodule.subtype_apply _,
        ← submodule.coe_inner, submodule.is_ortho_iff_inner_eq.mp h _
          (submodule.coe_mem _) _ (submodule.coe_mem _),
        submodule.is_ortho_iff_inner_eq.mp h.symm _
          (submodule.coe_mem _) _ (submodule.coe_mem _)], },
    refine ⟨this, _⟩,
    intros x,
    rw [comp_apply, submodule.subtype_apply, ← submodule.linear_proj_of_is_compl_idempotent,
        ← submodule.subtype_apply, ← comp_apply, ← this _ ((U.linear_proj_of_is_compl V hUV) x)],
    exact inner_self_nonneg, },
end

/-- set over `𝕜` is **non-negative** if all its elements are real and non-negative -/
def set.is_nonneg (A : set 𝕜) : Prop :=
∀ x : 𝕜, x ∈ A → ↑(re x) = x ∧ 0 ≤ re x

section finite_dimensional

local notation `e` := is_symmetric.eigenvector_basis
local notation `α` := is_symmetric.eigenvalues
local notation `√` := real.sqrt

variables {n : ℕ} [finite_dimensional 𝕜 E] (T : E →ₗ[𝕜] E)

/-- the spectrum of a positive linear map is non-negative -/
lemma is_positive.nonneg_spectrum (h : T.is_positive) :
  (spectrum 𝕜 T).is_nonneg :=
begin
  cases h with hT h,
  intros μ hμ,
  simp_rw [← module.End.has_eigenvalue_iff_mem_spectrum] at hμ,
  have : ↑(re μ) = μ,
  { simp_rw [← eq_conj_iff_re],
    exact is_symmetric.conj_eigenvalue_eq_self hT hμ, },
  rw ← this at hμ,
  exact ⟨this, eigenvalue_nonneg_of_nonneg hμ h⟩,
end

open_locale big_operators
/-- given a symmetric linear map with a non-negative spectrum,
we can write `T x = ∑ i, √α i • √α i • ⟪e i, x⟫` for any `x ∈ E`,
where `α i` are the eigenvalues of `T` and `e i` are the respective eigenvectors
that form an eigenbasis (`is_symmetric.eigenvector_basis`) -/
lemma sq_mul_sq_eq_self_of_is_symmetric_and_nonneg_spectrum
  [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n) (hT : T.is_symmetric)
  (hT1 : (spectrum 𝕜 T).is_nonneg) (v : E) :
  T v = ∑ i, ((√ (α hT hn i) • √ (α hT hn i)) : 𝕜) • ⟪e hT hn i, v⟫ • e hT hn i :=
begin
  have : ∀ i : fin n, 0 ≤ α hT hn i := λ i,
  by { specialize hT1 (hT.eigenvalues hn i),
       simp only [of_real_re, eq_self_iff_true, true_and] at hT1,
       apply hT1 (module.End.mem_spectrum_of_has_eigenvalue
         (is_symmetric.has_eigenvalue_eigenvalues hT hn i)), },
  calc T v = ∑ i, ⟪e hT hn i, v⟫ • T (e hT hn i) : _
       ... = ∑ i, ((√ (α hT hn i) • √ (α hT hn i)) : 𝕜) • ⟪e hT hn i, v⟫ • (e hT hn i) : _,
  simp_rw [← orthonormal_basis.repr_apply_apply, ← map_smul_of_tower, ← linear_map.map_sum,
    orthonormal_basis.sum_repr (e hT hn) v, is_symmetric.apply_eigenvector_basis,
    smul_smul, of_real_smul, ← of_real_mul, ← real.sqrt_mul (this _),
    real.sqrt_mul_self (this _), mul_comm],
end

/-- given a symmetric linear map `T` and a real number `r`,
we can define a linear map `S` such that `S = T ^ r` -/
noncomputable def rpow [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n)
  (hT : T.is_symmetric) (r : ℝ) : E →ₗ[𝕜] E :=
{ to_fun := λ v, ∑ i : fin n, ((((α hT hn i : ℝ) ^ r : ℝ)) : 𝕜) • ⟪e hT hn i, v⟫ • e hT hn i,
  map_add' := λ x y, by simp_rw [inner_add_right, add_smul, smul_add, finset.sum_add_distrib],
  map_smul' := λ r x, by simp_rw [inner_smul_right, ← smul_smul, finset.smul_sum,
                           ring_hom.id_apply, smul_smul, ← mul_assoc, mul_comm] }

lemma rpow_apply [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n)
  (hT : T.is_symmetric) (r : ℝ) (v : E) :
  T.rpow hn hT r v = ∑ i : fin n, (((α hT hn i : ℝ) ^ r : ℝ) : 𝕜) • ⟪e hT hn i, v⟫ • e hT hn i :=
rfl

/-- the square root of a symmetric linear map can then directly be defined with `re_pow` -/
noncomputable def sqrt [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n)
  (h : T.is_symmetric) :
  E →ₗ[𝕜] E := T.rpow hn h (1 / 2 : ℝ)

/-- the square root of a symmetric linear map `T`
is written as `T x = ∑ i, √ (α i) • ⟪e i, x⟫ • e i` for any `x ∈ E`,
where `α i` are the eigenvalues of `T` and `e i` are the respective eigenvectors
that form an eigenbasis (`is_symmetric.eigenvector_basis`) -/
lemma sqrt_apply (hn : finite_dimensional.finrank 𝕜 E = n) [decidable_eq 𝕜]
  (hT : T.is_symmetric) (x : E) :
  T.sqrt hn hT x = ∑ i, (√ (α hT hn i) : 𝕜) • ⟪e hT hn i, x⟫ • e hT hn i :=
by { simp_rw [real.sqrt_eq_rpow _], refl }

/-- given a symmetric linear map `T` with a non-negative spectrum,
the square root of `T` composed with itself equals itself, i.e., `T.sqrt ^ 2 = T`  -/
lemma sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum
  [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n) (hT : T.is_symmetric)
  (hT1 : (spectrum 𝕜 T).is_nonneg) :
  (T.sqrt hn hT) ^ 2 = T :=
by simp_rw [pow_two, mul_eq_comp, linear_map.ext_iff, comp_apply, sqrt_apply,
     inner_sum, inner_smul_real_right, smul_smul, inner_smul_right,
     ← orthonormal_basis.repr_apply_apply, orthonormal_basis.repr_self,
     euclidean_space.single_apply, mul_boole, smul_ite, smul_zero,
     finset.sum_ite_eq, finset.mem_univ, if_true, algebra.mul_smul_comm,
     sq_mul_sq_eq_self_of_is_symmetric_and_nonneg_spectrum T hn hT hT1,
     orthonormal_basis.repr_apply_apply, ← smul_eq_mul, ← smul_assoc,
     eq_self_iff_true, forall_const]

/-- given a symmetric linear map `T`, we have that its root is positive -/
lemma is_symmetric.sqrt_is_positive
  [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n) (hT : T.is_symmetric) :
  (T.sqrt hn hT).is_positive :=
begin
  have : (T.sqrt hn hT).is_symmetric,
  { intros x y,
    simp_rw [sqrt_apply T hn hT, inner_sum, sum_inner, smul_smul, inner_smul_right,
      inner_smul_left],
    have : ∀ i : fin n, conj ((√ (α hT hn i)) : 𝕜) = ((√ (α hT hn i)) : 𝕜) := λ i,
    by simp_rw [eq_conj_iff_re, of_real_re],
    simp_rw  [mul_assoc, map_mul, this, inner_conj_symm,
      mul_comm ⟪e hT hn _, y⟫, ← mul_assoc], },
  refine ⟨this, _⟩,
  intro x,
  simp_rw [sqrt_apply _ hn hT, inner_sum, add_monoid_hom.map_sum, inner_smul_right],
  apply finset.sum_nonneg',
  intros i,
  simp_rw [← inner_conj_symm x, ← orthonormal_basis.repr_apply_apply,
    mul_conj, ← of_real_mul, of_real_re],
  exact mul_nonneg (real.sqrt_nonneg _) (norm_sq_nonneg _),
end

/-- `T` is positive if and only if `T` is symmetric
(which is automatic from the definition of positivity)
and has a non-negative spectrum -/
lemma is_positive_iff_is_symmetric_and_nonneg_spectrum
  (hn : finite_dimensional.finrank 𝕜 E = n) :
  T.is_positive ↔ T.is_symmetric ∧ (spectrum 𝕜 T).is_nonneg :=
begin
  classical,
  refine ⟨λ h, ⟨h.1, λ μ hμ, is_positive.nonneg_spectrum T h μ hμ⟩,
          λ h, ⟨h.1, _⟩⟩,
  intros x,
  rw [← sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum T hn h.1 h.2,
    pow_two, mul_apply, ← adjoint_inner_left, is_self_adjoint_iff'.mp
      ((is_symmetric_iff_is_self_adjoint _).mp (is_symmetric.sqrt_is_positive T hn h.1).1)],
  exact inner_self_nonneg,
end

/-- `T` is positive if and only if there exists a
linear map `S` such that `T = S.adjoint * S` -/
lemma is_positive_iff_exists_adjoint_mul_self
  (hn : finite_dimensional.finrank 𝕜 E = n) :
  T.is_positive ↔ ∃ S : E →ₗ[𝕜] E, T = S.adjoint * S :=
begin
  classical,
   split,
  { rw [is_positive_iff_is_symmetric_and_nonneg_spectrum T hn],
    rintro ⟨hT, hT1⟩,
    use T.sqrt hn hT,
    rw [is_self_adjoint_iff'.mp
          ((is_symmetric_iff_is_self_adjoint _).mp (is_symmetric.sqrt_is_positive T hn hT).1),
      ← pow_two],
    exact (sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum T hn hT hT1).symm, },
  { intros h,
    rcases h with ⟨S, rfl⟩,
    refine ⟨is_symmetric_adjoint_mul_self S, _⟩,
    intro x,
    simp_rw [mul_apply, adjoint_inner_right],
    exact inner_self_nonneg, },
end

section complex

/-- for spaces `V` over `ℂ`, it suffices to define positivity with
`0 ≤ ⟪v, T v⟫_ℂ` for all `v ∈ V` -/
lemma complex_is_positive {V : Type*} [normed_add_comm_group V]
  [inner_product_space ℂ V] (T : V →ₗ[ℂ] V) :
  T.is_positive ↔ ∀ v : V, ↑(re ⟪v, T v⟫_ℂ) = ⟪v, T v⟫_ℂ ∧ 0 ≤ re ⟪v, T v⟫_ℂ :=
by simp_rw [is_positive, is_symmetric_iff_inner_map_self_real, inner_conj_symm,
     ← eq_conj_iff_re, inner_conj_symm, ← forall_and_distrib, and_comm, eq_comm]

end complex

lemma is_positive.conj_adjoint [finite_dimensional 𝕜 F]
  (T : E →ₗ[𝕜] E) (S : E →ₗ[𝕜] F) (h : T.is_positive) :
  (S.comp (T.comp S.adjoint)).is_positive :=
begin
  split,
  intros u v,
  simp_rw [comp_apply, ← adjoint_inner_left _ (T _), ← adjoint_inner_right _ (T _)],
  exact h.1 _ _,
  intros v,
  simp_rw [comp_apply, ← adjoint_inner_left _ (T _)],
  exact h.2 _,
end

lemma is_positive.adjoint_conj [finite_dimensional 𝕜 F]
  (T : E →ₗ[𝕜] E) (S : F →ₗ[𝕜] E) (h : T.is_positive) :
  (S.adjoint.comp (T.comp S)).is_positive :=
begin
  split,
  intros u v,
  simp_rw [comp_apply, adjoint_inner_left, adjoint_inner_right],
  exact h.1 _ _,
  intros v,
  simp_rw [comp_apply, adjoint_inner_right],
  exact h.2 _,
end

variable (hn : finite_dimensional.finrank 𝕜 E = n)
local notation `√T⋆`T := (T.adjoint.comp T).sqrt hn (is_symmetric_adjoint_mul_self T)

/-- we have `(T.adjoint.comp T).sqrt` is positive, given any linear map `T` -/
lemma sqrt_adjoint_self_is_positive [decidable_eq 𝕜] (T : E →ₗ[𝕜] E) : (√T⋆T).is_positive :=
is_symmetric.sqrt_is_positive _ hn (is_symmetric_adjoint_mul_self T)

/-- given any linear map `T` and `x ∈ E` we have
`‖(T.adjoint.comp T).sqrt x‖ = ‖T x‖` -/
lemma norm_of_sqrt_adjoint_mul_self_eq [decidable_eq 𝕜] (T : E →ₗ[𝕜] E) (x : E) :
  ‖(√T⋆T) x‖ = ‖T x‖ :=
begin
  simp_rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), ← @inner_self_eq_norm_sq 𝕜,
    ← adjoint_inner_left, is_self_adjoint_iff'.mp
      ((is_symmetric_iff_is_self_adjoint _).mp (sqrt_adjoint_self_is_positive hn T).1),
    ← mul_eq_comp, ← mul_apply, ← pow_two, mul_eq_comp],
 congr,
 apply sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum,
 apply is_positive.nonneg_spectrum _ ⟨is_symmetric_adjoint_mul_self T, _⟩,
 intros x,
 simp_rw [mul_apply, adjoint_inner_right],
 exact inner_self_nonneg,
end

end finite_dimensional

end linear_map


namespace continuous_linear_map

open continuous_linear_map

variables [complete_space E] [complete_space F]

/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is self adjoint
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def is_positive (T : E →L[𝕜] E) : Prop :=
  is_self_adjoint T ∧ ∀ x, 0 ≤ T.re_apply_inner_self x

lemma is_positive.to_linear_map (T : E →L[𝕜] E) :
  T.to_linear_map.is_positive ↔ T.is_positive :=
by simp_rw [to_linear_map_eq_coe, linear_map.is_positive, continuous_linear_map.coe_coe,
     is_positive, is_self_adjoint_iff_is_symmetric, re_apply_inner_self_apply T, inner_re_symm]

lemma is_positive.is_self_adjoint {T : E →L[𝕜] E} (hT : is_positive T) :
  is_self_adjoint T :=
hT.1

lemma is_positive.inner_nonneg_left {T : E →L[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪T x, x⟫ :=
hT.2 x

lemma is_positive.inner_nonneg_right {T : E →L[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪x, T x⟫ :=
by rw inner_re_symm; exact hT.inner_nonneg_left x

lemma is_positive_zero : is_positive (0 : E →L[𝕜] E) :=
begin
  refine ⟨is_self_adjoint_zero _, λ x, _⟩,
  change 0 ≤ re ⟪_, _⟫,
  rw [zero_apply, inner_zero_left, zero_hom_class.map_zero]
end

lemma is_positive_one : is_positive (1 : E →L[𝕜] E) :=
⟨is_self_adjoint_one _, λ x, inner_self_nonneg⟩

lemma is_positive.add {T S : E →L[𝕜] E} (hT : T.is_positive)
  (hS : S.is_positive) : (T + S).is_positive :=
begin
  refine ⟨hT.is_self_adjoint.add hS.is_self_adjoint, λ x, _⟩,
  rw [re_apply_inner_self, add_apply, inner_add_left, map_add],
  exact add_nonneg (hT.inner_nonneg_left x) (hS.inner_nonneg_left x)
end

lemma is_positive.conj_adjoint {T : E →L[𝕜] E}
  (hT : T.is_positive) (S : E →L[𝕜] F) : (S ∘L T ∘L S†).is_positive :=
begin
  refine ⟨hT.is_self_adjoint.conj_adjoint S, λ x, _⟩,
  rw [re_apply_inner_self, comp_apply, ← adjoint_inner_right],
  exact hT.inner_nonneg_left _
end

lemma is_positive.adjoint_conj {T : E →L[𝕜] E}
  (hT : T.is_positive) (S : F →L[𝕜] E) : (S† ∘L T ∘L S).is_positive :=
begin
  convert hT.conj_adjoint (S†),
  rw adjoint_adjoint
end

lemma is_positive.conj_orthogonal_projection (U : submodule 𝕜 E) {T : E →L[𝕜] E}
  (hT : T.is_positive) [complete_space U] :
  (U.subtypeL ∘L orthogonal_projection U ∘L T ∘L U.subtypeL ∘L
    orthogonal_projection U).is_positive :=
begin
  have := hT.conj_adjoint (U.subtypeL ∘L orthogonal_projection U),
  rwa (orthogonal_projection_is_self_adjoint U).adjoint_eq at this
end

lemma is_positive.orthogonal_projection_comp {T : E →L[𝕜] E}
  (hT : T.is_positive) (U : submodule 𝕜 E) [complete_space U] :
  (orthogonal_projection U ∘L T ∘L U.subtypeL).is_positive :=
begin
  have := hT.conj_adjoint (orthogonal_projection U : E →L[𝕜] U),
  rwa [U.adjoint_orthogonal_projection] at this,
end

section complex

variables {E' : Type*} [normed_add_comm_group E'] [inner_product_space ℂ E'] [complete_space E']

lemma is_positive_iff_complex (T : E' →L[ℂ] E') :
  is_positive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ :=
begin
  simp_rw [is_positive, forall_and_distrib, is_self_adjoint_iff_is_symmetric,
    linear_map.is_symmetric_iff_inner_map_self_real, eq_conj_iff_re],
  refl
end

end complex

end continuous_linear_map
