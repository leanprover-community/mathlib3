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

instance {R E : Type*} [division_ring R] [add_comm_group E]
  [module R E] : semilattice_sup (findim_subspace R E) :=
subtype.semilattice_sup (λ U V, by introsI hU hV; apply_instance)

instance {R E : Type*} [division_ring R] [add_comm_group E]
  [module R E] : nonempty (findim_subspace R E) :=
⟨⟨⊥, finite_dimensional_bot _ _⟩⟩

lemma findim_subspace.finite_dimensional {R E : Type*} [division_ring R] [add_comm_group E]
  [module R E] (U : findim_subspace R E) : finite_dimensional R (U : submodule R E) := U.2

local attribute [instance] findim_subspace.finite_dimensional

namespace continuous_linear_map

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

--noncomputable def _root_.genial_filter : filter (findim_subspace 𝕜 E) :=
--⨅ x : E, filter.comap
--  (λ U : findim_subspace 𝕜 E, (orthogonal_projection (U : submodule 𝕜 E) x : E))
--  (𝓝 x)
--
--lemma _root_.tendsto_genial_filter {ι : Type*} {l : filter ι} {U : ι → findim_subspace 𝕜 E}

section trace_along

private noncomputable def conj_proj (T : E →L[𝕜] E) (U : submodule 𝕜 E)
  [complete_space U] : E →L[𝕜] E :=
(U.subtypeL ∘L orthogonal_projection U ∘L T ∘L U.subtypeL ∘L orthogonal_projection U)

private lemma conj_proj_apply (T : E →L[𝕜] E) (U : submodule 𝕜 E)
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

lemma trace_along_eq_of_orthonormal_basis {ι : Type*} [fintype ι]
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

lemma trace_along_tendsto_of_pointwise [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {ι : Type*} {Φ : ι → E →L[𝕜] E} {φ : E →L[𝕜] E} {l : filter ι}
  (h : ∀ x, tendsto (λ i, ⟪x, Φ i x⟫) l (𝓝 $ ⟪x, φ x⟫)) :
  tendsto (λ i, trace_along U (Φ i)) l (𝓝 $ trace_along U φ) :=
begin
  let f := std_orthonormal_basis 𝕜 U,
  simp_rw [trace_along_eq_of_orthonormal_basis _ f],
  exact tendsto_finset_sum _ (λ j _, h _)
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

lemma is_positive.trace_along_conj_proj_le [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U V : submodule 𝕜 E) [finite_dimensional 𝕜 U] [finite_dimensional 𝕜 V] :
    re (trace_along U (conj_proj T V)) ≤
    re (trace_along V T) :=
begin
  have := U.is_hilbert_sum_orthogonal,
  let e := is_hilbert_sum.collected_hilbert_basis this
    (λ b, std_hilbert_basis 𝕜 ((cond b U Uᗮ : submodule 𝕜 E) : Type*)),
  have key₁ := re_clm.has_sum ((conj_proj T V).has_sum_trace_along_of_hilbert_basis U e),
  have key₂ := re_clm.has_sum (T.has_sum_trace_along_of_hilbert_basis V e),
  refine has_sum_le (λ i, _) key₁ key₂,
  simp only [conj_proj, comp_apply, coe_subtypeL', subtype_apply, subtype.coe_mk],
  rcases i with ⟨b, i⟩,
  cases b,
  { rw [← inner_orthogonal_projection_left_eq_right,
        is_hilbert_sum.coe_collected_hilbert_basis_mk,
        orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
        submodule.coe_zero, inner_zero_left, _root_.map_zero],
    { exact (hT.conj_orthogonal_projection V).inner_nonneg_right _ },
    { exact submodule.coe_mem _ } },
  { rw [← inner_orthogonal_projection_left_eq_right,
        is_hilbert_sum.coe_collected_hilbert_basis_mk,
        orthogonal_projection_eq_self_iff.mpr],
    exact submodule.coe_mem _ }
end

lemma is_positive.monotone_trace_along [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  {U V : submodule 𝕜 E} [finite_dimensional 𝕜 U] [finite_dimensional 𝕜 V] (hUV : U ≤ V):
    re (trace_along U T) ≤
    re (trace_along V T) :=
begin
  convert hT.trace_along_conj_proj_le U V using 2,
  let e := std_orthonormal_basis 𝕜 U,
  rw [trace_along_eq_of_orthonormal_basis _ e, trace_along_eq_of_orthonormal_basis _ e],
  congrm ∑ i, _,
  rw [conj_proj_apply, ← inner_orthogonal_projection_left_eq_right,
      orthogonal_projection_eq_self_iff.mpr (hUV $ submodule.coe_mem _)]
end

noncomputable def is_positive.trace_along_ennreal [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {T : E →L[𝕜] E} (hT : T.is_positive) : ℝ≥0∞ :=
@coe ℝ≥0 ℝ≥0∞ _ ⟨re $ trace_along U T, hT.trace_along_nonneg U⟩

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

lemma is_positive.trace_eq_supr_of_monotone [complete_space E]
  {T : E →L[𝕜] E} (hT : T.is_positive) {τ : Type*} [nonempty τ] [semilattice_sup τ]
  (U : τ → submodule 𝕜 E) [∀ t, finite_dimensional 𝕜 (U t)] (hU : monotone U)
  (hU' : ⊤ ≤ (⨆ t, U t).topological_closure) :
  hT.trace = ⨆ t, hT.trace_along_ennreal (U t) :=
begin
  haveI : ∀ t, complete_space (U t) := λ t, infer_instance,
  refine le_antisymm _ _,
  { refine supr_le (λ V, _),
    haveI : finite_dimensional 𝕜 (V : submodule 𝕜 E) := V.finite_dimensional,
    suffices : tendsto
      (λ t, (hT.conj_orthogonal_projection (U t)).trace_along_ennreal V) at_top
      (𝓝 $ hT.trace_along_ennreal V),
    from le_of_tendsto' this
      (λ t, le_trans (hT.trace_along_ennreal_conj_proj_le _ _) $ le_supr _ t),
    simp_rw [is_positive.trace_along_ennreal, ← ennreal.of_real_eq_coe_nnreal],
    refine ennreal.tendsto_of_real (((continuous_re.tendsto _).comp $
      trace_along_tendsto_of_pointwise _ $ λ x, _)),
    simp_rw [comp_apply, subtypeL_apply, ← inner_orthogonal_projection_left_eq_right],
    refine tendsto.inner _ ((T.cont.tendsto _).comp _);
    exact orthogonal_projection_tendsto_self _ _ hU _ hU' },
  { exact supr_mono' (λ t, ⟨⟨U t, infer_instance⟩, le_rfl⟩) }
end

lemma is_positive.has_sum_trace {ι : Type*} [complete_space E] (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) :
  has_sum (λ i : ι, ennreal.of_real (re ⟪e i, T (e i)⟫)) hT.trace :=
begin
  have fact : ∀ J : finset ι, ∀ i ∈ J, 0 ≤ re ⟪e i, T (e i)⟫ :=
    λ J i _, hT.inner_nonneg_right (e i),
  rw [ennreal.summable.has_sum_iff, ennreal.tsum_eq_supr_sum,
      hT.trace_eq_supr_of_monotone _ e.partial_span_mono e.partial_span_dense.ge],
  congrm ⨆ J, _,
  unfold hilbert_basis.partial_span,
  rw [is_positive.trace_along_ennreal, ← ennreal.of_real_eq_coe_nnreal,
      T.trace_along_span_eq_of_orthonormal e.orthonormal J,
      _root_.map_sum, ennreal.of_real_sum_of_nonneg (fact J)]
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

@[simp] lemma is_trace_class.mk_apply {T : E →L[𝕜] E} (hT : T.is_trace_class) (x : E) :
  (⟨T, hT⟩ : trace_class_submodule 𝕜 E) x = T x := rfl

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

lemma is_trace_class.adjoint {T : E →L[𝕜] E} (hT : T.is_trace_class) :
  (T†).is_trace_class :=
begin
  refine submodule.span_induction hT _ _ _ _,
  { rintros S hS,
    rw ← hS.1.is_self_adjoint.eq_adjoint,
    exact subset_span hS },
  { sorry }, -- API hole : adjoint of zero !
  { intros S₁ S₂ h₁ h₂,
    rw map_add,
    exact h₁.add h₂ },
  { intros a S hS,
    rw adjoint.map_smulₛₗ a S,
    exact hS.smul _ }
end

lemma is_trace_class_adjoint_iff {T : E →L[𝕜] E} :
  (T†).is_trace_class ↔ T.is_trace_class :=
⟨λ hT, (adjoint_adjoint T) ▸ hT.adjoint, is_trace_class.adjoint⟩

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

lemma is_positive.is_trace_class_iff {ι : Type*} {T : E →L[𝕜] E} (hT : T.is_positive)
  (e : hilbert_basis ι 𝕜 E) :
  T.is_trace_class ↔ summable (λ i, ⟪e i, T (e i)⟫) :=
begin
  refine ⟨λ htrT, htrT.summable_of_hilbert_basis e, λ htrT, hT.is_trace_class _⟩,
  rw [← (hT.has_sum_trace e).tsum_eq, ← ennreal.of_real_tsum_of_nonneg],
  { exact ennreal.of_real_lt_top },
  { exact λ i, hT.inner_nonneg_right _ },
  { exact re_clm.summable htrT }
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

lemma _root_.hilbert_basis.trace_map_apply {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  (T : trace_class_submodule 𝕜 E) : e.trace_map T = ∑' i, ⟪e i, T (e i)⟫ :=
rfl

lemma _root_.hilbert_basis.re_trace_map_of_is_positive {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  (re (e.trace_map ⟨T, hT.is_trace_class htrT⟩) : 𝕜) = e.trace_map ⟨T, hT.is_trace_class htrT⟩ :=
begin
  have : T.is_trace_class := hT.is_trace_class htrT,
  have hsum : summable (λ i, ⟪e i, T (e i)⟫) := this.summable_of_hilbert_basis e,
  simp_rw [e.trace_map_apply, ← re_clm_apply, ← of_real_clm_apply, this.mk_apply,
           continuous_linear_map.map_tsum _ hsum,
           continuous_linear_map.map_tsum _ (re_clm.summable hsum)],
  sorry -- same small API hole
end

lemma _root_.hilbert_basis.nonneg_trace_map_of_is_positive {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  (0 : ℝ) ≤ re (e.trace_map ⟨T, hT.is_trace_class htrT⟩) :=
begin
  have : T.is_trace_class := hT.is_trace_class htrT,
  have hsum : summable (λ i, ⟪e i, T (e i)⟫) := this.summable_of_hilbert_basis e,
  simp_rw [e.trace_map_apply, ← re_clm_apply, this.mk_apply,
           continuous_linear_map.map_tsum _ hsum],
  exact tsum_nonneg (λ i, hT.inner_nonneg_right _),
end

lemma _root_.hilbert_basis.trace_map_eq_is_positive_trace {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  ennreal.of_real (re $ e.trace_map ⟨T, hT.is_trace_class htrT⟩) = hT.trace :=
begin
  have : T.is_trace_class := hT.is_trace_class htrT,
  have hsum : summable (λ i, ⟪e i, T (e i)⟫) := this.summable_of_hilbert_basis e,
  simp_rw [e.trace_map_apply, ← re_clm_apply, this.mk_apply,
           continuous_linear_map.map_tsum _ hsum, re_clm_apply],
  rw ennreal.of_real_tsum_of_nonneg,
  { rw (hT.has_sum_trace e).tsum_eq },
  { exact λ i, hT.inner_nonneg_right _ },
  { exact re_clm.summable hsum }
end

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

variables (𝕜 E)

noncomputable def traceₗ : (trace_class_submodule 𝕜 E) →ₗ[𝕜] 𝕜 := exists_extend_trace.some

variables {𝕜 E}

lemma is_positive.re_traceₗ {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  (re (traceₗ 𝕜 E ⟨T, hT.is_trace_class htrT⟩) : 𝕜) = traceₗ 𝕜 E ⟨T, hT.is_trace_class htrT⟩ :=
(exists_extend_trace.some_spec T hT htrT).1.symm

lemma is_positive.traceₗ_nonneg {T : E →L[𝕜] E} (hT : T.is_positive) (htrT : hT.trace < ⊤) :
  (0 : ℝ) ≤ re (traceₗ 𝕜 E ⟨T, hT.is_trace_class htrT⟩) :=
(exists_extend_trace.some_spec T hT htrT).2.1

lemma is_positive.traceₗ_eq_positive_trace {T : E →L[𝕜] E} (hT : T.is_positive)
  (htrT : hT.trace < ⊤) :
  ennreal.of_real (re $ traceₗ 𝕜 E ⟨T, hT.is_trace_class htrT⟩) = hT.trace :=
(exists_extend_trace.some_spec T hT htrT).2.2.symm

lemma _root_.ennreal.inj_on_of_real : inj_on ennreal.of_real {x | 0 ≤ x} :=
begin
  intros x hx y hy H,
  rwa [ennreal.of_real_eq_coe_nnreal hx, ennreal.of_real_eq_coe_nnreal hy,
      ennreal.coe_eq_coe, subtype.mk_eq_mk] at H
end

lemma traceₗ_spec {tr : (trace_class_submodule 𝕜 E) →ₗ[𝕜] 𝕜}
  (H : ∀ (T : E →L[𝕜] E) (hT : T.is_positive) (htrT : hT.trace < ⊤),
    tr ⟨T, hT.is_trace_class htrT⟩ = re (tr ⟨T, hT.is_trace_class htrT⟩) ∧
    (0 : ℝ) ≤ re (tr ⟨T, hT.is_trace_class htrT⟩) ∧
    hT.trace = ennreal.of_real (re $ tr ⟨T, hT.is_trace_class htrT⟩)) :
  tr = traceₗ 𝕜 E :=
begin
  rcases tr.exists_extend with ⟨tr', htr⟩,
  rcases (traceₗ 𝕜 E).exists_extend with ⟨trace', htrace⟩,
  rw [← htr, ← htrace] at *,
  ext S,
  rcases S with ⟨S, hS⟩,
  change tr' S = trace' S,
  refine eq_on_span _ hS,
  rintros T ⟨hTpos, htrT⟩,
  split_ifs at htrT,
  rcases H T hTpos htrT with ⟨H₁, H₂, H₃⟩,
  have H₁' := hTpos.re_traceₗ htrT,
  have H₂' := hTpos.traceₗ_nonneg htrT,
  have H₃' := hTpos.traceₗ_eq_positive_trace htrT,
  rw [← htrace] at H₁' H₂' H₃',
  rw [linear_map.comp_apply, submodule.subtype_apply, subtype.coe_mk] at H₁ H₂ H₃ H₁' H₂' H₃',
  rw [H₁, ← H₁', is_R_or_C.of_real_inj, ← ennreal.inj_on_of_real.eq_iff H₂ H₂', ← H₃, H₃']
end

lemma _root_.hilbert_basis.trace_map_eq_traceₗ {ι : Type*} (e : hilbert_basis ι 𝕜 E) :
  e.trace_map = traceₗ 𝕜 E :=
traceₗ_spec (λ T hTpos htrT, ⟨(e.re_trace_map_of_is_positive hTpos htrT).symm,
  e.nonneg_trace_map_of_is_positive hTpos htrT,
  (e.trace_map_eq_is_positive_trace hTpos htrT).symm⟩)

noncomputable def trace (T : E →L[𝕜] E) : 𝕜 :=
if hT : T.is_trace_class then traceₗ 𝕜 E ⟨T, hT⟩ else 0

lemma is_trace_class.has_sum_trace_of_hilbert_basis {ι : Type*} (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_trace_class) : has_sum (λ i, ⟪e i, T (e i)⟫) (trace T) :=
begin
  rw [(hT.summable_of_hilbert_basis e).has_sum_iff, trace],
  split_ifs,
  change e.trace_map ⟨T, hT⟩ = traceₗ 𝕜 E ⟨T, hT⟩,
  rw e.trace_map_eq_traceₗ
end

end trace_class

end continuous_linear_map

section

end
