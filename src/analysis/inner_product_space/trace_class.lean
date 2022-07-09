/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.adjoint
import linear_algebra.trace

/-!
# Trace-Class operators

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

open linear_map filter
open_locale topological_space classical

abbreviation findim_subspace (R E : Type*) [division_ring R] [add_comm_group E] [module R E] :=
{U : submodule R E // finite_dimensional R U}

lemma findim_subspace.finite_dimensional {R E : Type*} [division_ring R] [add_comm_group E]
  [module R E] (U : findim_subspace R E) : finite_dimensional R (U : submodule R E) := U.2

local attribute [instance] findim_subspace.finite_dimensional

namespace continuous_linear_map

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]

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

def is_trace_class (T : E →L[𝕜] E) : Prop :=
∃ x : 𝕜, tendsto (λ U : findim_subspace 𝕜 E, trace_along (U : submodule 𝕜 E) T) at_top (𝓝 x)

def is_trace_class.add {S T : E →L[𝕜] E} (hS : S.is_trace_class) (hT : T.is_trace_class) :
  (S + T).is_trace_class :=
let ⟨trS, htrS⟩ := hS, ⟨trT, htrT⟩ := hT in ⟨trS + trT, by {simp_rw map_add, exact htrS.add htrT}⟩

def is_trace_class.const_smul {T : E →L[𝕜] E} (c : 𝕜) (hT : T.is_trace_class) :
  (c • T).is_trace_class :=
let ⟨trT, htrT⟩ := hT in ⟨c • trT, by {simp_rw smul_hom_class.map_smul, exact htrT.const_smul c}⟩

noncomputable def trace (T : E →L[𝕜] E) : 𝕜 :=
if h : is_trace_class T then classical.some h else 0

lemma trace_spec {T : E →L[𝕜] E} (hT : T.is_trace_class) :
  tendsto (λ U : findim_subspace 𝕜 E, trace_along (U : submodule 𝕜 E) T) at_top (𝓝 $ T.trace) :=
by {rw trace, split_ifs, exact classical.some_spec hT}

end continuous_linear_map
