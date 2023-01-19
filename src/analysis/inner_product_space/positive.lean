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

* `is_positive` : a continuous linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`

## Main statements

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

namespace continuous_linear_map

open inner_product_space is_R_or_C continuous_linear_map
open_locale inner_product complex_conjugate


variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
  [complete_space E] [complete_space F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is self adjoint
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def is_positive (T : E →L[𝕜] E) : Prop :=
  is_self_adjoint T ∧ ∀ x, 0 ≤ T.re_apply_inner_self x

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

variables {E' : Type*} [inner_product_space ℂ E'] [complete_space E']

lemma is_positive_iff_complex (T : E' →L[ℂ] E') :
  is_positive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ :=
begin
  simp_rw [is_positive, forall_and_distrib, is_self_adjoint_iff_is_symmetric,
    linear_map.is_symmetric_iff_inner_map_self_real, eq_conj_iff_re],
  refl
end

end complex

end continuous_linear_map

namespace linear_map

open linear_map

variables {V : Type*} [inner_product_space ℂ V]

local notation `e` := is_symmetric.eigenvector_basis
open_locale big_operators

/-- `T` is (semi-definite) positive if `∀ x : V, ⟪x, T x⟫_ℂ ≥ 0` -/
def is_positive (T : V →ₗ[ℂ] V) :
  Prop := ∀ x : V, 0 ≤ ⟪x, T x⟫_ℂ.re ∧ (⟪x, T x⟫_ℂ.re : ℂ) = ⟪x, T x⟫_ℂ

lemma is_self_adjoint_iff_real_inner [finite_dimensional ℂ V] (T : V →ₗ[ℂ] V) :
  is_self_adjoint T ↔ ∀ x, (⟪x, T x⟫_ℂ.re : ℂ) = ⟪x, T x⟫_ℂ :=
begin
  simp_rw [← is_symmetric_iff_is_self_adjoint, is_symmetric_iff_inner_map_self_real,
           inner_conj_sym, ← is_R_or_C.re_eq_complex_re, ← is_R_or_C.eq_conj_iff_re,
           inner_conj_sym],
  exact ⟨λ h x, (h x).symm, λ h x, (h x).symm⟩,
end

/-- if `T.is_positive`, then `T.is_self_adjoint` and all its eigenvalues are non-negative -/
lemma is_positive.self_adjoint_and_nonneg_spectrum [finite_dimensional ℂ V]
  (T : V →ₗ[ℂ] V) (h : T.is_positive) :
  is_self_adjoint T ∧ ∀ μ : ℂ, μ ∈ spectrum ℂ T → μ = μ.re ∧ 0 ≤ μ.re :=
begin
  have frs : is_self_adjoint T,
  { rw linear_map.is_self_adjoint_iff',
    symmetry,
    rw [← sub_eq_zero, ← inner_map_self_eq_zero],
    intro x,
    cases h x,
    have := complex.re_add_im (inner x (T x)),
    rw [← right, complex.of_real_re, complex.of_real_im] at this,
    rw [linear_map.sub_apply, inner_sub_left, ← inner_conj_sym, linear_map.adjoint_inner_left,
        ← right, is_R_or_C.conj_of_real, sub_self], },
   refine ⟨frs,_⟩,
   intros μ hμ,
   rw ← module.End.has_eigenvalue_iff_mem_spectrum at hμ,
   have realeigen := (complex.eq_conj_iff_re.mp
     (linear_map.is_symmetric.conj_eigenvalue_eq_self
       ((linear_map.is_symmetric_iff_is_self_adjoint T).mpr frs) hμ)).symm,
   refine ⟨realeigen, _⟩,
   have hα : ∃ α : ℝ, α = μ.re := by use μ.re,
   cases hα with α hα,
   rw ← hα,
   rw [realeigen, ← hα] at hμ,
   exact eigenvalue_nonneg_of_nonneg hμ (λ x, ge_iff_le.mp (h x).1),
end

variables [finite_dimensional ℂ V] {n : ℕ} (hn : finite_dimensional.finrank ℂ V = n)
variables (T : V →ₗ[ℂ] V)

lemma of_pos_eq_sqrt_sqrt (hT : T.is_symmetric)
  (hT1 : ∀ μ : ℂ, μ ∈ spectrum ℂ T → μ = ↑μ.re ∧ 0 ≤ μ.re) (v : V) :
  T v = ∑ (i : (fin n)), real.sqrt (hT.eigenvalues hn i) • real.sqrt (hT.eigenvalues hn i)
   • ⟪(e hT hn) i, v⟫_ℂ • (e hT hn) i :=
begin
  have : ∀ i : fin n, 0 ≤ hT.eigenvalues hn i := λ i,
  by { specialize hT1 (hT.eigenvalues hn i),
      simp only [complex.of_real_re, eq_self_iff_true, true_and] at hT1,
      apply hT1 (module.End.mem_spectrum_of_has_eigenvalue
        (is_symmetric.has_eigenvalue_eigenvalues hT hn i)), },
  calc T v = ∑ (i : (fin n)), ⟪(e hT hn) i, v⟫_ℂ • T ((e hT hn) i) :
  by simp_rw [← orthonormal_basis.repr_apply_apply, ← map_smul_of_tower, ← linear_map.map_sum,
                orthonormal_basis.sum_repr (is_symmetric.eigenvector_basis hT hn) v]
       ... = ∑ (i : (fin n)),
        real.sqrt (hT.eigenvalues hn i) • real.sqrt (hT.eigenvalues hn i) •
         ⟪(e hT hn) i, v⟫_ℂ • (e hT hn) i :
  by simp_rw [is_symmetric.apply_eigenvector_basis, smul_smul, ← real.sqrt_mul (this _),
              real.sqrt_mul_self (this _), mul_comm, ← smul_smul, complex.coe_smul],
end

include hn
/-- Let `e = hT.eigenvector_basis hn` so that we have `T (e i) = α i • e i` for each `i`.
Then when `T.is_symmetric` and all its eigenvalues are nonnegative,
we can define `T.sqrt` by `e i ↦ √α i • e i`. -/
noncomputable def sqrt (hT : T.is_symmetric) : V →ₗ[ℂ] V :=
{ to_fun := λ v, ∑ (i : (fin n)),
             real.sqrt (hT.eigenvalues hn i) • ⟪(hT.eigenvector_basis hn) i, v⟫_ℂ
              • (hT.eigenvector_basis hn) i,
  map_add' := λ x y, by simp_rw [inner_add_right, add_smul, smul_add, finset.sum_add_distrib],
  map_smul' := λ r x, by simp_rw [inner_smul_right, ← smul_smul, finset.smul_sum,
                                  ring_hom.id_apply, ← complex.coe_smul, smul_smul,
                                  ← mul_assoc, mul_comm] }

lemma sqrt_eq (hT : T.is_symmetric) (v : V) : (T.sqrt hn hT) v = ∑ (i : (fin n)),
  real.sqrt (hT.eigenvalues hn i) • ⟪(hT.eigenvector_basis hn) i, v⟫_ℂ
   • (hT.eigenvector_basis hn) i := rfl

/-- `T.sqrt ^ 2 = T` and `T.sqrt.is_positive` -/
lemma sqrt_sq_eq_linear_map_and_is_positive (hT : T.is_symmetric)
  (hT1 : ∀ μ : ℂ, μ ∈ spectrum ℂ T → μ = ↑μ.re ∧ 0 ≤ μ.re) :
  (T.sqrt hn hT)^2 = T ∧ (T.sqrt hn hT).is_positive :=
begin
  rw [pow_two, mul_eq_comp],
  split,
  { ext v,
    simp only [comp_apply, linear_map.sqrt_eq, inner_sum, inner_smul_real_right],
    simp only [← complex.coe_smul, smul_smul, inner_smul_right],
    simp only [← orthonormal_basis.repr_apply_apply, orthonormal_basis.repr_self,
               euclidean_space.single_apply, mul_boole, finset.sum_ite_eq,
               finset.mem_univ, if_true, ← smul_smul, complex.coe_smul],
    symmetry,
    simp only [orthonormal_basis.repr_apply_apply],
    exact linear_map.of_pos_eq_sqrt_sqrt hn T hT hT1 v, },
  { intro,
    split,
    { simp_rw [linear_map.sqrt_eq, inner_sum, ← complex.coe_smul, smul_smul, inner_smul_right,
               complex.re_sum, mul_assoc, mul_comm, ← complex.real_smul, ← inner_conj_sym x,
               ← complex.norm_sq_eq_conj_mul_self, complex.smul_re, complex.of_real_re,
               smul_eq_mul],
      apply finset.sum_nonneg',
      intros i,
      specialize hT1 (hT.eigenvalues hn i),
      simp only [complex.of_real_re, eq_self_iff_true, true_and] at hT1,
      simp_rw [mul_nonneg_iff, real.sqrt_nonneg, complex.norm_sq_nonneg, and_self, true_or], },
    { suffices : ∀ x, (star_ring_end ℂ) ⟪x, (T.sqrt hn hT) x⟫_ℂ = ⟪x, (T.sqrt hn hT) x⟫_ℂ,
      { rw [← is_R_or_C.re_eq_complex_re, ← is_R_or_C.eq_conj_iff_re],
        exact this x, },
      intro x,
      simp_rw [inner_conj_sym, linear_map.sqrt_eq, sum_inner, inner_sum, ← complex.coe_smul,
               smul_smul, inner_smul_left, inner_smul_right, map_mul, is_R_or_C.conj_of_real,
               inner_conj_sym, mul_assoc, mul_comm ⟪_, x⟫_ℂ], }, },
end

/-- `T.is_positive` if and only if `T.is_self_adjoint` and all its eigenvalues are nonnegative. -/
theorem is_positive_iff_self_adjoint_and_nonneg_eigenvalues :
  T.is_positive ↔ is_self_adjoint T ∧ (∀ μ : ℂ, μ ∈ spectrum ℂ T → μ = ↑μ.re ∧ 0 ≤ μ.re) :=
begin
  split,
  { intro h, exact linear_map.is_positive.self_adjoint_and_nonneg_spectrum T h, },
  { intro h,
    have hT : T.is_symmetric := (is_symmetric_iff_is_self_adjoint T).mpr h.1,
    rw [← (linear_map.sqrt_sq_eq_linear_map_and_is_positive hn T hT h.2).1, pow_two],
    have : (T.sqrt hn hT) * (T.sqrt hn hT) = (T.sqrt hn hT).adjoint * (T.sqrt hn hT) :=
    by rw is_self_adjoint_iff'.mp (linear_map.is_positive.self_adjoint_and_nonneg_spectrum _
     (linear_map.sqrt_sq_eq_linear_map_and_is_positive hn T hT h.2).2).1,
    rw this, clear this,
    intro,
    simp_rw [mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K],
    norm_cast, refine ⟨sq_nonneg ‖(linear_map.sqrt hn T hT) x‖, rfl⟩, },
end

/-- every positive linear map can be written as `S.adjoint * S` for some linear map `S` -/
lemma is_positive_iff_exists_linear_map_mul_adjoint :
  T.is_positive ↔ ∃ S : V →ₗ[ℂ] V, T = S.adjoint * S :=
begin
  split,
  { rw [linear_map.is_positive_iff_self_adjoint_and_nonneg_eigenvalues hn,
        ← is_symmetric_iff_is_self_adjoint],
    rintro ⟨hT, hT1⟩,
    use T.sqrt hn hT,
    rw [is_self_adjoint_iff'.mp (linear_map.is_positive.self_adjoint_and_nonneg_spectrum _
         (linear_map.sqrt_sq_eq_linear_map_and_is_positive hn T hT hT1).2).1,
        ← pow_two, (linear_map.sqrt_sq_eq_linear_map_and_is_positive hn T hT hT1).1],  },
  { intros h x,
    cases h with S hS,
    simp_rw [hS, mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K],
    norm_cast,
    refine ⟨sq_nonneg _, rfl⟩, },
end

end linear_map

section finite_dimensional

variables (V : Type*) [inner_product_space ℂ V] [finite_dimensional ℂ V] (T : V →L[ℂ] V)

open linear_map
lemma self_adjoint_clm_iff_self_adjoint_lm :
  is_self_adjoint T ↔ is_self_adjoint T.to_linear_map :=
begin
  simp_rw [continuous_linear_map.to_linear_map_eq_coe, is_self_adjoint_iff',
           continuous_linear_map.is_self_adjoint_iff', continuous_linear_map.ext_iff,
           linear_map.ext_iff, continuous_linear_map.coe_coe, adjoint_eq_to_clm_adjoint],
  split,
  { intros h x, rw ← h x, refl, },
  { intros h x, rw ← h x, refl, },
end

lemma is_positive_clm_iff_is_positive_lm :
  T.is_positive ↔ linear_map.is_positive T.to_linear_map :=
begin
  simp_rw [linear_map.is_positive, continuous_linear_map.is_positive,
           self_adjoint_clm_iff_self_adjoint_lm, linear_map.is_self_adjoint_iff_real_inner,
           continuous_linear_map.re_apply_inner_self_apply, inner_re_symm,
           is_R_or_C.re_eq_complex_re, continuous_linear_map.to_linear_map_eq_coe,
           continuous_linear_map.coe_coe, and.comm],
  refine ⟨λ h x, ⟨h.1 x, h.2 x⟩, λ h, ⟨λ x, (h x).1, λ x, (h x).2⟩⟩,
end

end finite_dimensional
