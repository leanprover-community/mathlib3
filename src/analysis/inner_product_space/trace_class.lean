/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.l2_space
import analysis.inner_product_space.positive
import linear_algebra.trace

/-!
# Trace-class operators

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open linear_map filter submodule set inner_product_space is_R_or_C
open_locale topological_space classical big_operators ennreal nnreal inner_product

abbreviation findim_subspace (R E : Type*) [division_ring R] [add_comm_group E] [module R E] :=
{U : submodule R E // finite_dimensional R U}

lemma findim_subspace.finite_dimensional {R E : Type*} [division_ring R] [add_comm_group E]
  [module R E] (U : findim_subspace R E) : finite_dimensional R (U : submodule R E) := U.2

local attribute [instance] findim_subspace.finite_dimensional

namespace continuous_linear_map

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

section trace_along

private noncomputable def conj_proj [complete_space E] (T : E →L[𝕜] E) (U : submodule 𝕜 E)
  [complete_space U] : E →L[𝕜] E :=
(U.subtypeL ∘L orthogonal_projection U ∘L T ∘L U.subtypeL ∘L orthogonal_projection U)

private lemma conj_proj_apply [complete_space E] (T : E →L[𝕜] E) (U : submodule 𝕜 E)
  [complete_space U] (x : E) :
  conj_proj T U x = orthogonal_projection U (T (orthogonal_projection U x)) :=
rfl

noncomputable def trace_along (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] :
  (E →L[𝕜] E) →ₗ[𝕜] 𝕜 :=
linear_map.trace 𝕜 U ∘ₗ (coe_lm 𝕜) ∘ₗ
  (compL 𝕜 U E U (orthogonal_projection U) : (U →L[𝕜] E) →ₗ[𝕜] (U →L[𝕜] U)) ∘ₗ
  ((compL 𝕜 U E E).flip U.subtypeL : (E →L[𝕜] E) →ₗ[𝕜] (U →L[𝕜] E))

@[simp] lemma trace_along_apply (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] (T : E →L[𝕜] E) :
  trace_along U T = linear_map.trace 𝕜 U (dom_restrict ((orthogonal_projection U).comp T) U) :=
rfl

-- make the finite dimensional version for `linear_map.trace`

-- Why is `complete_space E` needed ?
lemma trace_along_eq_of_orthonormal_basis [complete_space E] {ι : Type*} [fintype ι]
  {U : submodule 𝕜 E} [finite_dimensional 𝕜 U] (T : E →L[𝕜] E)
  (e : orthonormal_basis ι 𝕜 (U : submodule 𝕜 E)) :
  trace_along U T = ∑ i, ⟪(e i : E), T (e i)⟫ :=
begin
  rw [trace_along_apply, trace_eq_sum_of_basis 𝕜 e.to_basis],
  congr,
  ext i,
  rw [basis.coord_apply, e.coe_to_basis_repr_apply, e.coe_to_basis, e.repr_apply_apply,
      coe_inner, dom_restrict_apply, coe_coe, comp_apply,
      ← inner_orthogonal_projection_left_eq_right U,
      orthogonal_projection_eq_self_iff.mpr (subtype.coe_prop $ e i)]
end

lemma has_sum_trace_along_of_hilbert_basis [complete_space E] {ι : Type*}
  (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] (T : E →L[𝕜] E)
  (e : hilbert_basis ι 𝕜 E) :
  has_sum (λ i, ⟪(e i : E), (conj_proj T U) (e i)⟫) (trace_along U T) :=
begin
  let f := std_orthonormal_basis 𝕜 U,
  rw trace_along_eq_of_orthonormal_basis T f,
  have : ∀ j, has_sum (λ i, ⟪(conj_proj (T†) U) (f j : E), e i⟫ * ⟪e i, f j⟫)
    ⟪(conj_proj (T†) U) (f j : E), f j⟫ :=
    λ j, e.has_sum_inner_mul_inner _ _,
  convert has_sum_sum (λ j (_ : j ∈ finset.univ), this j),
  { ext i,
    rw [conj_proj_apply, ← inner_orthogonal_projection_left_eq_right],
    nth_rewrite 0 ← orthogonal_projection_mem_subspace_eq_self (orthogonal_projection U (e i)),
    rw [inner_orthogonal_projection_left_eq_right, ← coe_inner, ← f.sum_inner_mul_inner],
    congrm ∑ j, _,
    rw [coe_inner, coe_inner, inner_orthogonal_projection_left_eq_right,
        orthogonal_projection_mem_subspace_eq_self, ← inner_orthogonal_projection_left_eq_right,
        ← T.adjoint_inner_left, ← inner_orthogonal_projection_left_eq_right, mul_comm],
    refl },
  { ext j,
    change _ = ⟪orthogonal_projection U (T† (orthogonal_projection U $ f j)), _⟫,
    rw [coe_inner, inner_orthogonal_projection_left_eq_right, T.adjoint_inner_left,
        orthogonal_projection_mem_subspace_eq_self] }
end

lemma trace_along_span_eq_of_orthonormal [complete_space E] {ι : Type*} (T : E →L[𝕜] E) {e : ι → E}
  (he : orthonormal 𝕜 e) (s : finset ι) :
  trace_along (span 𝕜 (s.image e : set E)) T = ∑ i in s, ⟪(e i : E), T (e i)⟫ :=
begin
  let e'' := orthonormal_basis.span he s,
  simp_rw [T.trace_along_eq_of_orthonormal_basis e'', orthonormal_basis.span_apply,
            s.sum_coe_sort (λ i, ⟪e i, T (e i)⟫)]
end

lemma trace_along_continuous [complete_space E] (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] :
  continuous (trace_along U) :=
begin
  let f := std_orthonormal_basis 𝕜 U,
  let φ : (E →L[𝕜] E) →L[𝕜] 𝕜 :=
    ∑ i, innerSL (f i : E) ∘L (continuous_linear_map.apply 𝕜 E (f i : E)),
  convert φ.cont using 2,
  ext T,
  change trace_along U T = φ T,
  dsimp only [φ],
  rw sum_apply,
  exact T.trace_along_eq_of_orthonormal_basis f
end

end trace_along

section positive

lemma is_positive.trace_along_eq_re [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] : trace_along U T = re (trace_along U T) :=
begin
  let e := std_orthonormal_basis 𝕜 U,
  rw [trace_along_eq_of_orthonormal_basis _ e, _root_.map_sum, of_real_sum],
  congr,
  ext i,
  rw [← coe_coe, ← hT.1],
  exact (hT.1.coe_re_apply_inner_self_apply (e i)).symm
end

lemma is_positive.trace_along_nonneg [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] : 0 ≤ re (trace_along U T) :=
begin
  let e := std_orthonormal_basis 𝕜 U,
  rw [trace_along_eq_of_orthonormal_basis _ e, _root_.map_sum],
  refine finset.sum_nonneg (λ i _, _),
  rw [← coe_coe, ← hT.1],
  exact hT.2 (e i)
end

-- This is annoying, can we make it easier ?
lemma is_positive.trace_along_conj_proj_le [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U V : submodule 𝕜 E) [finite_dimensional 𝕜 U] [finite_dimensional 𝕜 V] :
    re (trace_along U (conj_proj T V)) ≤
    re (trace_along V T) :=
begin
  rcases orthonormal.exists_hilbert_basis_extension
    ((std_orthonormal_basis 𝕜 U).orthonormal.comp_linear_isometry U.subtypeₗᵢ).coe_range
    with ⟨s, e, hs, he⟩,
  let t := coe '' (orthonormal_basis_index 𝕜 U : set U),
  have hts : t ⊆ s,
  { rw coe_std_orthonormal_basis at hs,
    change set.range (coe ∘ coe) ⊆ s at hs,
    rwa [set.range_comp, subtype.range_coe] at hs },
  have he₁ : ∀ (i : s) (hit : (i : E) ∈ t), (orthogonal_projection U i : E) = i,
  { rintros i ⟨i₀, hi₀, hii₀⟩,
    rw [← hii₀, orthogonal_projection_eq_self_iff],
    exact submodule.coe_mem _ },
  have he₂ : ∀ (i : s) (hit : (i : E) ∉ t), orthogonal_projection U i = 0,
  { rintros i hit,
    rw (std_orthonormal_basis 𝕜 U).orthogonal_projection_eq_sum,
    refine finset.sum_eq_zero (λ j₀ _, _),
    rw [coe_std_orthonormal_basis],
    rcases j₀ with ⟨j₁, hj₁⟩,
    let j : E := j₁,
    change ⟪j, i⟫ • _ = (0 : U),
    have hjt : j ∈ t := mem_image_of_mem _ hj₁,
    have : j ≠ i := λ h, hit (h ▸ hjt),
    have : (⟨j, hts hjt⟩ : s) ≠ i := λ h, this (congr_arg coe h),
    have := e.orthonormal.2 this,
    rw [he, subtype.coe_mk] at this,
    rw [this, zero_smul] },
  have key₁ := re_clm.has_sum ((conj_proj T V).has_sum_trace_along_of_hilbert_basis U e),
  have key₂ := re_clm.has_sum (T.has_sum_trace_along_of_hilbert_basis V e),
  refine has_sum_le (λ x, _) key₁ key₂,
  simp only [he, conj_proj, comp_apply, coe_subtypeL', subtype_apply, subtype.coe_mk],
  by_cases hxt : (x : E) ∈ t,
  { rw [← inner_orthogonal_projection_left_eq_right, he₁ x hxt] },
  { rw [← inner_orthogonal_projection_left_eq_right, he₂ x hxt, submodule.coe_zero,
        inner_zero_left, _root_.map_zero],
    exact (hT.conj_orthogonal_projection V).inner_nonneg_right x },
end

noncomputable def is_positive.trace_along_nnreal [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {T : E →L[𝕜] E} (hT : T.is_positive) : ℝ≥0 :=
⟨re $ trace_along U T, hT.trace_along_nonneg U⟩

noncomputable def is_positive.trace_along_ennreal [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {T : E →L[𝕜] E} (hT : T.is_positive) : ℝ≥0∞ :=
hT.trace_along_nnreal U

lemma is_positive.trace_along_ennreal_conj_proj_le [complete_space E] {T : E →L[𝕜] E}
  (hT : T.is_positive)
  (U V : submodule 𝕜 E) [finite_dimensional 𝕜 U] [finite_dimensional 𝕜 V] :
    (hT.conj_orthogonal_projection V).trace_along_ennreal U ≤
    hT.trace_along_ennreal V :=
begin
  rw [is_positive.trace_along_ennreal, is_positive.trace_along_ennreal, ennreal.coe_le_coe],
  exact hT.trace_along_conj_proj_le _ _
end

noncomputable def is_positive.trace [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive) :
  ℝ≥0∞ :=
⨆ (U : findim_subspace 𝕜 E), hT.trace_along_ennreal (U : submodule 𝕜 E)

lemma is_positive.has_sum_trace {ι : Type*} [complete_space E] (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) :
  has_sum (λ i : ι, ennreal.of_real (re ⟪e i, T (e i)⟫)) hT.trace :=
begin
  have fact : ∀ J : finset ι, ∀ i ∈ J, 0 ≤ re ⟪e i, T (e i)⟫ :=
    λ J i _, hT.inner_nonneg_right (e i),
  rw [ennreal.summable.has_sum_iff],
  refine le_antisymm _ _,
  { rw [ennreal.tsum_eq_supr_sum],
    refine supr_mono' (λ J, ⟨⟨span 𝕜 (J.image e : set E), infer_instance⟩, _⟩),
    change _ ≤ (hT.trace_along_ennreal (span 𝕜 (J.image e : set E)) : ℝ≥0∞),
    rw [is_positive.trace_along_ennreal, is_positive.trace_along_nnreal,
        ← ennreal.of_real_eq_coe_nnreal, T.trace_along_span_eq_of_orthonormal e.orthonormal J,
        _root_.map_sum, ennreal.of_real_sum_of_nonneg (fact J)],
    exact le_rfl },
  { refine supr_le (λ U, _),
    haveI : finite_dimensional 𝕜 (U : submodule 𝕜 E) := U.finite_dimensional,
    let f := std_orthonormal_basis 𝕜 (U : submodule 𝕜 E),
    let V : finset ι → submodule 𝕜 E := λ J, span 𝕜 (J.image e),
    suffices : tendsto
      (λ J : finset ι, (hT.conj_orthogonal_projection (V J)).trace_along_ennreal U) at_top
      (𝓝 $ hT.trace_along_ennreal U),
    { refine le_of_tendsto_of_tendsto' this ennreal.summable.has_sum (λ J, _),
      rw [← ennreal.of_real_sum_of_nonneg (fact J), ← _root_.map_sum,
          ← T.trace_along_span_eq_of_orthonormal e.orthonormal J,
          ennreal.of_real_eq_coe_nnreal (hT.trace_along_nonneg _)],
      exact hT.trace_along_ennreal_conj_proj_le U (V J) },
    simp_rw [is_positive.trace_along_ennreal, is_positive.trace_along_nnreal,
              ← ennreal.of_real_eq_coe_nnreal],
    refine ennreal.tendsto_of_real (((continuous_re.tendsto _).comp _)),
    simp_rw [trace_along_eq_of_orthonormal_basis _ f],
    refine tendsto_finset_sum _ (λ i _, _),
    change tendsto (λ J, ⟪(f i : E), orthogonal_projection (V J)
      (T (orthogonal_projection (V J) (f i)))⟫) _ _,
    simp_rw [← inner_orthogonal_projection_left_eq_right],
    refine tendsto.inner _ ((T.cont.tendsto _).comp _);
    exact e.tendsto_orthogonal_projection_at_top _ }
end

lemma is_positive.trace_along_eq_trace [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {T : E →L[𝕜] E} (hT : T.is_positive) :
  hT.trace_along_ennreal U = (hT.conj_orthogonal_projection U).trace :=
begin
  rcases exists_hilbert_basis 𝕜 E with ⟨s, e, -⟩,
  have := has_sum_trace_along_of_hilbert_basis U T e,
  have := ennreal.tendsto_of_real (((continuous_re.tendsto _).comp this)),
  simp_rw [is_positive.trace_along_ennreal, is_positive.trace_along_nnreal,
            ← ennreal.of_real_eq_coe_nnreal],
  refine tendsto_nhds_unique this _,
  convert is_positive.has_sum_trace e (hT.conj_orthogonal_projection U),
  ext J : 1,
  dsimp only [function.comp_apply, function.app],
  rw [_root_.map_sum, ennreal.of_real_sum_of_nonneg],
  { refl },
  { exact λ _ _, (hT.conj_orthogonal_projection U).inner_nonneg_right _ }
end

lemma is_positive.trace_conj_proj_add_trace_conj_proj_orthogonal
  [complete_space E] (U : submodule 𝕜 E) [complete_space U] {T : E →L[𝕜] E}
  (hT : T.is_positive) :
  hT.trace = (hT.conj_orthogonal_projection U).trace + (hT.conj_orthogonal_projection Uᗮ).trace :=
begin
  sorry
end

end positive

section trace_class

variables [complete_space E]

variables (𝕜 E)

def trace_class_submodule : submodule 𝕜 (E →L[𝕜] E) :=
submodule.span 𝕜 {T | T.is_positive ∧ if h : T.is_positive then h.trace < ⊤ else false}

variables {𝕜 E}

def is_trace_class (T : E →L[𝕜] E) : Prop :=
T ∈ trace_class_submodule 𝕜 E

lemma is_positive.is_trace_class {T : E →L[𝕜] E} (hT : T.is_positive)
  (htrT : hT.trace < ⊤) : T.is_trace_class :=
begin
  refine subset_span ⟨hT, _⟩,
  split_ifs,
  exact htrT
end

lemma is_trace_class_zero : (0 : E →L[𝕜] E).is_trace_class := zero_mem _

lemma is_trace_class.add {S T : E →L[𝕜] E} (hS : S.is_trace_class) (hT : T.is_trace_class) :
  (S + T).is_trace_class :=
add_mem hS hT

lemma is_trace_class.smul {T : E →L[𝕜] E} (hT : T.is_trace_class) (c : 𝕜) :
  (c • T).is_trace_class :=
smul_mem _ c hT

lemma is_trace_class.summable_of_hilbert_basis {ι : Type*} {T : E →L[𝕜] E} (hT : T.is_trace_class)
  (e : hilbert_basis ι 𝕜 E) : summable (λ i, ⟪e i, T (e i)⟫) :=
begin
  refine submodule.span_induction hT _ _ _ _,
  { rintros S ⟨hSpos, hStrace⟩,
    split_ifs at hStrace,
    rw ← (hSpos.has_sum_trace e).tsum_eq at hStrace,
    have := ennreal.summable_to_real hStrace.ne,
    simp only [ennreal.to_real_of_real, hSpos.inner_nonneg_right] at this,
    convert (of_real_clm : ℝ →L[ℝ] 𝕜).summable this,
    ext i,
    rw [of_real_clm_apply],
    sorry }, -- easy, API hole
  { simp only [summable_zero, zero_apply, inner_zero_right] },
  { intros S₁ S₂ h₁ h₂,
    simp only [h₁.add h₂, inner_add_right, add_apply] },
  { intros a S hS,
    simp only [hS.mul_left a, inner_smul_right, coe_smul', pi.smul_apply] }
end

noncomputable def _root_.hilbert_basis.trace_map {ι : Type*} (e : hilbert_basis ι 𝕜 E) :
  (trace_class_submodule 𝕜 E) →ₗ[𝕜] 𝕜 :=
{ to_fun := λ T, ∑' i, ⟪e i, T (e i)⟫,
  map_add' :=
  begin
    rintros ⟨T, hT : T.is_trace_class⟩ ⟨S, hS : S.is_trace_class⟩,
    change ∑' i, ⟪e i, (T + S) (e i)⟫ = ∑' i, ⟪e i, T (e i)⟫ + ∑' i, ⟪e i, S (e i)⟫,
    rw ← tsum_add (hT.summable_of_hilbert_basis e) (hS.summable_of_hilbert_basis e),
    simp only [inner_add_right, add_apply],
  end,
  map_smul' :=
  begin
    rintros a ⟨T, hT : T.is_trace_class⟩,
    change ∑' i, ⟪e i, (a • T) (e i)⟫ = a • ∑' i, ⟪e i, T (e i)⟫,
    rw ← tsum_const_smul (hT.summable_of_hilbert_basis e),
    { simp only [inner_smul_right, coe_smul', pi.smul_apply, algebra.id.smul_eq_mul] },
    { apply_instance }
  end }

lemma _root_.hilbert_basis.re_trace_map_of_is_positive {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  (re (e.trace_map ⟨T, hT.is_trace_class htrT⟩) : 𝕜) = e.trace_map ⟨T, hT.is_trace_class htrT⟩ :=
sorry

lemma _root_.hilbert_basis.nonneg_trace_map_of_is_positive {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  (0 : ℝ) ≤ re (e.trace_map ⟨T, hT.is_trace_class htrT⟩) :=
sorry

lemma _root_.hilbert_basis.trace_map_eq_is_positive_trace {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  ennreal.of_real (re $ e.trace_map ⟨T, hT.is_trace_class htrT⟩) = hT.trace :=
sorry

lemma exists_extend_trace : ∃ tr : (trace_class_submodule 𝕜 E) →ₗ[𝕜] 𝕜,
  ∀ (T : E →L[𝕜] E) (hT : T.is_positive) (htrT : hT.trace < ⊤),
  tr ⟨T, hT.is_trace_class htrT⟩ = re (tr ⟨T, hT.is_trace_class htrT⟩) ∧
  (0 : ℝ) ≤ re (tr ⟨T, hT.is_trace_class htrT⟩) ∧
  hT.trace = ennreal.of_real (re $ tr ⟨T, hT.is_trace_class htrT⟩) :=
begin
  rcases exists_hilbert_basis 𝕜 E with ⟨s, e, -⟩,
  exact ⟨e.trace_map, λ T hT htrT, ⟨(e.re_trace_map_of_is_positive hT htrT).symm,
    e.nonneg_trace_map_of_is_positive hT htrT, (e.trace_map_eq_is_positive_trace hT htrT).symm⟩⟩
end

noncomputable def traceₗ : (trace_class_submodule 𝕜 E) →ₗ[𝕜] 𝕜 := exists_extend_trace.some

end trace_class

end continuous_linear_map
