/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.l2_space
import analysis.inner_product_space.adjoint
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

noncomputable abbreviation conj_proj [complete_space E] (T : E →L[𝕜] E) (U : submodule 𝕜 E)
  [complete_space U] : E →L[𝕜] E :=
(U.subtypeL ∘L orthogonal_projection U ∘L T ∘L U.subtypeL ∘L orthogonal_projection U)

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

--lemma has_sum_trace_along_of_hilbert_basis' [complete_space E] {ι : Type*}
--  {U : submodule 𝕜 E} [finite_dimensional 𝕜 U] (T : E →L[𝕜] E)
--  (e : hilbert_basis ι 𝕜 E) :
--  has_sum (λ i, ⟪(e i : E), T (e i)⟫) (trace_along U T) :=
--begin
--  let f : orthonormal_basis (orthonormal_basis_index 𝕜 U) 𝕜 U :=
--    orthonormal_basis.mk (std_orthonormal_basis_orthonormal 𝕜 U)
--    (std_orthonormal_basis 𝕜 U).span_eq,
--  rw trace_along_eq_of_orthonormal_basis T f,
--  have key : ∀ a, has_sum (λ i, ⟪e i, f a⟫ • e i) (f a),
--  { intro a,
--    have := e.has_sum_repr (f a),
--    simpa only [hilbert_basis.repr_apply_apply] using this },
--  conv {congr, skip, congr, skip, funext,
--        rw [(key _).tsum_eq.symm, ← innerSL_apply, T.map_tsum (key _).summable,
--            (innerSL _).map_tsum ((key _).summable.mapL T)], },
--  sorry,
--  --have : ∀ a, has_sum (λ i, innerSL $ ⟪e i, f a⟫ • e i) (innerSL $ (f a : E)) :=
--  --  λ a, (this a).mapL _,
--  --have : ∀ j, has_sum (λ i, ⟪e.repr (f j) i, T (e.repr (f j) i)⟫) ⟪(f j : E), T (f j)⟫
--  --refine has_sum_sum,
--end

--#check adjoint

lemma has_sum_trace_along_of_hilbert_basis [complete_space E] {ι : Type*}
  {U : submodule 𝕜 E} [finite_dimensional 𝕜 U] (T : E →L[𝕜] E)
  (e : hilbert_basis ι 𝕜 E) :
  has_sum (λ i, ⟪(e i : E), (conj_proj T U) (e i)⟫) (trace_along U T) :=
begin
  let f : orthonormal_basis (orthonormal_basis_index 𝕜 U) 𝕜 U :=
    orthonormal_basis.mk (std_orthonormal_basis_orthonormal 𝕜 U)
    (std_orthonormal_basis 𝕜 U).span_eq,
  rw trace_along_eq_of_orthonormal_basis T f,
  have : ∀ a, has_sum (λ i, ⟪(conj_proj (T†) U) (f a : E), e i⟫ * ⟪e i, f a⟫)
    ⟪(conj_proj (T†) U) (f a : E), f a⟫ :=
    λ a, e.has_sum_inner_mul_inner _ _,
  convert has_sum_sum (λ a (_ : a ∈ finset.univ), this a),
  { ext i,
    change ⟪e i, orthogonal_projection U (T (orthogonal_projection U $ e i))⟫ = _,
    rw [← inner_orthogonal_projection_left_eq_right],
    nth_rewrite 0 ← orthogonal_projection_mem_subspace_eq_self (orthogonal_projection U (e i)),
    rw [inner_orthogonal_projection_left_eq_right, ← coe_inner, ← f.sum_inner_mul_inner],
    congr,
    ext j,
    rw [coe_inner, coe_inner, inner_orthogonal_projection_left_eq_right,
        orthogonal_projection_mem_subspace_eq_self, ← inner_orthogonal_projection_left_eq_right,
        ← T.adjoint_inner_left, ← inner_orthogonal_projection_left_eq_right, mul_comm],
    refl },
  { ext j,
    change _ = ⟪orthogonal_projection U (T† (orthogonal_projection U $ f j)), _⟫,
    rw [coe_inner, inner_orthogonal_projection_left_eq_right, T.adjoint_inner_left,
        orthogonal_projection_mem_subspace_eq_self] }
end

--lemma foo [complete_space E] {ι : Type*} {e : ι → E}
--  (he : orthonormal 𝕜 e) (s : finset ι) :
--  (span 𝕜 (s.image e : set E)).subtypeL ∘L orthogonal_projection (span 𝕜 (s.image e : set E)) =
--  ∑ i in s, (𝕜 ∙ e i).subtypeL ∘L orthogonal_projection (𝕜 ∙ e i) :=
--sorry

lemma trace_along_span_eq_of_orthonormal [complete_space E] {ι : Type*} (T : E →L[𝕜] E) {e : ι → E}
  (he : orthonormal 𝕜 e) (s : finset ι) :
  trace_along (span 𝕜 (s.image e : set E)) T = ∑ i in s, ⟪(e i : E), T (e i)⟫ :=
begin
  have : span 𝕜 (s.image e : set E) = span 𝕜 (set.range $ e ∘ (coe : s → ι)),
  { rw [finset.coe_image, set.range_comp, subtype.range_coe],
    refl },
  haveI : finite_dimensional 𝕜 (span 𝕜 (set.range $ e ∘ (coe : s → ι))),
  { rw [← this],
    apply_instance },
  simp_rw this,
  let e' : basis s 𝕜 _ := basis.span (he.linear_independent.comp (coe : s → ι)
    subtype.coe_injective),
  have heq : ∀ i : s, (e' i : E) = e i :=
    λ i, by simp only [e', basis.span, function.comp_app, basis.coe_mk, submodule.coe_mk],
  have hortho : orthonormal 𝕜 e',
  { split,
    { intro i,
      rw [coe_norm, heq i],
      exact he.1 i },
    { intros i j hij,
      rw [coe_inner, heq i, heq j],
      exact he.2 (subtype.coe_injective.ne hij) } },
  let e'' := orthonormal_basis.mk hortho e'.span_eq,
  have heq' : ∀ i : s, (e'' i : E) = e i :=
    λ i, by simp only [orthonormal_basis.coe_mk, heq i],
  simp_rw [T.trace_along_eq_of_orthonormal_basis e'', heq', s.sum_coe_sort (λ i, ⟪e i, T (e i)⟫)]
end

lemma trace_along_continuous [complete_space E] (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] :
  continuous (trace_along U) :=
begin
  let f : orthonormal_basis (orthonormal_basis_index 𝕜 U) 𝕜 U :=
    orthonormal_basis.mk (std_orthonormal_basis_orthonormal 𝕜 U)
    (std_orthonormal_basis 𝕜 U).span_eq,
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

def is_positive (T : E →L[𝕜] E) : Prop :=
  is_self_adjoint (T : E →ₗ[𝕜] E) ∧ ∀ x, 0 ≤ T.re_apply_inner_self x

lemma is_positive_zero : is_positive (0 : E →L[𝕜] E) :=
begin
  split,
  { exact λ x y, (inner_zero_right : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left : ⟪0, y⟫ = 0) },
  { intro x,
    change 0 ≤ re ⟪_, _⟫,
    rw [zero_apply, inner_zero_left, zero_hom_class.map_zero] }
end

lemma is_positive_id : is_positive (1 : E →L[𝕜] E) :=
⟨λ x y, rfl, λ x, inner_self_nonneg⟩

lemma is_positive.add [complete_space E] {T S : E →L[𝕜] E} (hT : T.is_positive)
  (hS : S.is_positive) : (T + S).is_positive :=
begin
  rw [is_positive, is_self_adjoint_iff_eq_adjoint] at *,
  split,
  { rw [map_add, ← hT.1, ← hS.1] },
  { intro x,
    rw [re_apply_inner_self, add_apply, inner_add_left, map_add],
    exact add_nonneg (hT.2 x) (hS.2 x) }
end

lemma is_positive.proj_comp [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U : submodule 𝕜 E) [complete_space U] :
  (orthogonal_projection U ∘L T ∘L U.subtypeL).is_positive :=
begin
  split,
  { intros x y,
    rw [coe_coe, comp_apply, coe_inner, inner_orthogonal_projection_left_eq_right,
        comp_apply, ← coe_coe, hT.1, orthogonal_projection_mem_subspace_eq_self,
        coe_subtypeL', U.subtype_apply],
    nth_rewrite 0 ← orthogonal_projection_mem_subspace_eq_self x,
    rw inner_orthogonal_projection_left_eq_right,
    refl },
  { intros x,
    rw [re_apply_inner_self, coe_inner, comp_apply, inner_orthogonal_projection_left_eq_right,
        orthogonal_projection_mem_subspace_eq_self],
    exact hT.2 x }
end

lemma is_positive.conj [complete_space E] [complete_space F] {T : E →L[𝕜] E} (hT : T.is_positive)
  (S : E →L[𝕜] F) : (S ∘L T ∘L S†).is_positive :=
begin
  split,
  { intros x y,
    rw [coe_coe, comp_apply, comp_apply, ← adjoint_inner_right, ← coe_coe, hT.1, coe_coe,
        adjoint_inner_left],
    refl },
  { intro x,
    rw [re_apply_inner_self, comp_apply, ← adjoint_inner_right],
    exact hT.2 _ }
end

lemma is_positive.conj_proj [complete_space E] (U : submodule 𝕜 E) {T : E →L[𝕜] E}
  (hT : T.is_positive) [complete_space U] :
  (conj_proj T U).is_positive :=
begin
  have := hT.conj (U.subtypeL ∘L orthogonal_projection U),
  rwa ← (orthogonal_projection_is_self_adjoint U).eq_adjoint at this
end

lemma is_positive.trace_along_eq_re [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] : trace_along U T = re (trace_along U T) :=
begin
  let e : orthonormal_basis (orthonormal_basis_index 𝕜 U) 𝕜 U :=
    orthonormal_basis.mk (std_orthonormal_basis_orthonormal 𝕜 U)
    (std_orthonormal_basis 𝕜 U).span_eq,
  rw [trace_along_eq_of_orthonormal_basis _ e, _root_.map_sum, of_real_sum],
  congr,
  ext i,
  rw [← coe_coe, ← hT.1],
  exact (hT.1.coe_re_apply_inner_self_apply (e i)).symm
end

lemma is_positive.trace_along_nonneg [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] : 0 ≤ re (trace_along U T) :=
begin
  let e : orthonormal_basis (orthonormal_basis_index 𝕜 U) 𝕜 U :=
    orthonormal_basis.mk (std_orthonormal_basis_orthonormal 𝕜 U)
    (std_orthonormal_basis 𝕜 U).span_eq,
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
  sorry -- This should be easy thanks to has_sum_trace_along_of_hilbert_basis
end

noncomputable def is_positive.trace_along_nnreal [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {T : E →L[𝕜] E} (hT : T.is_positive) : ℝ≥0 :=
⟨re $ trace_along U T, hT.trace_along_nonneg U⟩

noncomputable def is_positive.trace_along_ennreal [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {T : E →L[𝕜] E} (hT : T.is_positive) : ℝ≥0∞ :=
hT.trace_along_nnreal U

lemma is_positive.trace_along_ennreal_conj_proj_le [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive)
  (U V : submodule 𝕜 E) [finite_dimensional 𝕜 U] [finite_dimensional 𝕜 V] :
    (hT.conj_proj V).trace_along_ennreal U ≤
    hT.trace_along_ennreal V :=
begin
  sorry -- This should be easy thanks to is_positive.trace_along_conj_proj_le
end

noncomputable def is_positive.trace [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive) :
  ℝ≥0∞ :=
⨆ (U : findim_subspace 𝕜 E), hT.trace_along_ennreal (U : submodule 𝕜 E)

lemma is_positive.has_sum_trace {ι : Type*} [complete_space E] (e : hilbert_basis ι 𝕜 E)
  {T : E →L[𝕜] E} (hT : T.is_positive) :
  has_sum (λ i : ι, ennreal.of_real (re ⟪e i, T (e i)⟫)) hT.trace :=
begin
  rw [ennreal.summable.has_sum_iff],
  refine le_antisymm _ _,
  { rw [ennreal.tsum_eq_supr_sum],
    refine supr_mono' (λ J, ⟨⟨span 𝕜 (J.image e : set E), infer_instance⟩, _⟩),
    change _ ≤ (hT.trace_along_ennreal (span 𝕜 (J.image e : set E)) : ℝ≥0∞),
    rw [is_positive.trace_along_ennreal, is_positive.trace_along_nnreal,
        ← ennreal.of_real_eq_coe_nnreal, T.trace_along_span_eq_of_orthonormal e.orthonormal J,
        _root_.map_sum, ennreal.of_real_sum_of_nonneg sorry], -- easy sorry
    exact le_rfl },
  { refine supr_le (λ U, _),
    haveI : finite_dimensional 𝕜 (U : submodule 𝕜 E) := U.finite_dimensional,
    let f : orthonormal_basis _ 𝕜 (U : submodule 𝕜 E) :=
      orthonormal_basis.mk (std_orthonormal_basis_orthonormal 𝕜 (U : submodule 𝕜 E))
      (basis.span_eq _),
    --have : ∑ i, ennreal.of_real (re ⟪(f i : E), T (f i)⟫) ≤ hT.trace,
    --{ sorry },
    let V : finset ι → submodule 𝕜 E := λ J, span 𝕜 (J.image e),
    suffices : tendsto (λ J : finset ι, (hT.conj_proj (V J)).trace_along_ennreal U) at_top
      (𝓝 $ hT.trace_along_ennreal U),
    { refine le_of_tendsto_of_tendsto' this ennreal.summable.has_sum (λ J, _),
      rw [← ennreal.of_real_sum_of_nonneg sorry, ← _root_.map_sum,
          ← T.trace_along_span_eq_of_orthonormal e.orthonormal J, ennreal.of_real_eq_coe_nnreal (hT.trace_along_nonneg _)],
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
    sorry } -- hard part
end

end positive

section trace_class



end trace_class

end continuous_linear_map
