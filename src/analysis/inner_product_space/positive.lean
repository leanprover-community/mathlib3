/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.adjoint

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

open inner_product_space is_R_or_C continuous_linear_map
open_locale inner_product complex_conjugate

namespace continuous_linear_map

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
