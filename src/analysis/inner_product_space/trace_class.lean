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

noncomputable def trace_along (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] :
  (E →L[𝕜] E) →ₗ[𝕜] 𝕜 :=
{ to_fun := λ T, linear_map.trace 𝕜 U (dom_restrict ((orthogonal_projection U).comp T) U),
  map_add' := λ S T,
  begin
    rw [comp_add, coe_add, dom_restrict, linear_map.add_comp, map_add],
    refl
  end,
  map_smul' := λ c T,
  begin
    rw [comp_smul, coe_smul, dom_restrict, linear_map.smul_comp,
        smul_hom_class.map_smul],
    refl
  end }

@[simp] lemma trace_along_apply (U : submodule 𝕜 E) [finite_dimensional 𝕜 U] (T : E →L[𝕜] E) :
  trace_along U T = linear_map.trace 𝕜 U (dom_restrict ((orthogonal_projection U).comp T) U) :=
rfl

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

lemma trace_along_span_eq_of_orthonormal [complete_space E] {ι : Type*} (T : E →L[𝕜] E) {e : ι → E}
  (he : orthonormal 𝕜 e) (s : finset ι) :
  trace_along (span 𝕜 (s.image e : set E)) T = ∑ i in s, ⟪(e i : E), T (e i)⟫ :=
begin
  let e'' : basis s 𝕜 _ := basis.span (he.linear_independent.comp (coe : s → ι)
    subtype.coe_injective),
  have : span 𝕜 (s.image e : set E) = span 𝕜 (set.range $ e ∘ (coe : s → ι)),
  { rw [finset.coe_image, set.range_comp, subtype.range_coe],
    refl },
  let e' : basis s 𝕜 (span 𝕜 (s.image e : set E)) := e''.map (linear_equiv.of_eq _ _ this.symm),
  --have eq : ∀ i : s, (e'' i : E) = e' i := λ i, rfl,
  --have : orthonormal 𝕜 (he.linear_independent.comp (coe : s → ι) subtype.coe_injective) :=
  --  he.comp _ subtype.coe_injective,
  sorry
end

end trace_along

section positive

def is_positive (T : E →L[𝕜] E) : Prop :=
  is_self_adjoint (T : E →ₗ[𝕜] E) ∧ ∀ x, 0 ≤ T.re_apply_inner_self x

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

noncomputable def is_positive.trace_along_nnreal [complete_space E] (U : submodule 𝕜 E)
  [finite_dimensional 𝕜 U] {T : E →L[𝕜] E} (hT : T.is_positive) : ℝ≥0 :=
⟨re $ trace_along U T, hT.trace_along_nonneg U⟩

noncomputable def is_positive.trace [complete_space E] {T : E →L[𝕜] E} (hT : T.is_positive) :
  ℝ≥0∞ :=
⨆ (U : findim_subspace 𝕜 E), hT.trace_along_nnreal (U : submodule 𝕜 E)

end positive

end continuous_linear_map
