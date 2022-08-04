/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.trace_class

/-!
# Hilbert-Schmidt operators

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

open is_R_or_C submodule filter
open_locale inner_product topological_space

namespace continuous_linear_map

variables {ι 𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
  [complete_space E] [complete_space F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

section is_HS

def is_HS (T : E →L[𝕜] F) : Prop := (T† ∘L T).is_trace_class

@[simp] lemma is_HS_def {T : E →L[𝕜] F} : T.is_HS ↔ (T† ∘L T).is_trace_class := iff.rfl

lemma is_HS_iff_trace_lt_top (T : E →L[𝕜] F) :
  T.is_HS ↔ (is_positive_adjoint_comp T).trace < ⊤ :=
by rw [is_HS_def, ← (is_positive_adjoint_comp T).is_trace_class_iff]

lemma is_HS_iff_summable (T : E →L[𝕜] F) (e : hilbert_basis ι 𝕜 E) :
  T.is_HS ↔ summable (λ i, ⟪T (e i), T (e i)⟫) :=
by simp_rw [is_HS_def, (is_positive_adjoint_comp T).is_trace_class_iff_summable e, comp_apply,
            adjoint_inner_right]

-- Should I keep this ?
lemma foo (S T : E →L[𝕜] F) :
  (S + T)† ∘L (S + T) = S† ∘L S + T† ∘L S + S† ∘L T + T† ∘L T :=
begin
  simp only [linear_isometry_equiv.map_add, add_comp, comp_add],
  rw ← add_assoc
end

--lemma is_HS.add_aux₁ {S T : E →L[𝕜] F} (V : submodule 𝕜 E) [finite_dimensional 𝕜 V] :
--  re (trace_along V (S† ∘L T + T† ∘L S)) ≤ re (trace_along V (S† ∘L S + T† ∘L T)) :=
--begin
--  rw [← sub_nonneg, ← map_sub, ← map_sub],
--  convert (is_positive_adjoint_comp (S - T)).trace_along_nonneg V,
--  -- Lack of `simp` lemmas
--  sorry --simp [sub_eq_add_neg, comp_neg],
--end

private lemma add_aux₁ {S T : E →L[𝕜] F} :
  (S + T)† ∘L (S + T) = S† ∘L S + T† ∘L T + S† ∘L S + T† ∘L T - (S - T)† ∘L (S - T) :=
begin
  sorry -- API holes
end

private lemma add_aux₂ (S T : E →L[𝕜] F) (V : submodule 𝕜 E) [finite_dimensional 𝕜 V] :
  re (trace_along V ((S + T)† ∘L (S + T))) ≤
  re (trace_along V (S† ∘L S + T† ∘L T + S† ∘L S + T† ∘L T)) :=
begin
  rw [add_aux₁, map_sub, map_sub],
  exact sub_le_self _ ((is_positive_adjoint_comp _).trace_along_nonneg V)
end

lemma is_HS.add {S T : E →L[𝕜] F} (hT : T.is_HS) (hS : S.is_HS) :
  (S + T).is_HS :=
begin
  rw is_HS_iff_trace_lt_top at *,
  refine lt_of_le_of_lt _
    (ennreal.mul_lt_top ennreal.two_ne_top (ennreal.add_lt_top.mpr ⟨hS, hT⟩).ne),
  refine le_of_tendsto_of_tendsto'
    (is_positive_adjoint_comp $ S + T).trace_along_tendsto_at_top
    (ennreal.tendsto.const_mul ((is_positive_adjoint_comp S).trace_along_tendsto_at_top.add
      (is_positive_adjoint_comp T).trace_along_tendsto_at_top) (or.inr ennreal.two_ne_top))
    (λ V, _),
  haveI : finite_dimensional 𝕜 (V : submodule 𝕜 E) := V.2,
  have hSpos := (is_positive_adjoint_comp S).trace_along_nonneg V,
  have hTpos := (is_positive_adjoint_comp T).trace_along_nonneg V,
  rw [is_positive.trace_along_eq_of_real, is_positive.trace_along_eq_of_real,
      is_positive.trace_along_eq_of_real, ← ennreal.of_real_add, two_mul, ← ennreal.of_real_add,
      ← add_assoc, ← map_add, ← map_add, ← map_add, ← map_add, ← map_add, ← map_add];
  exact ennreal.of_real_le_of_real (add_aux₂ S T V) <|> refine add_nonneg _ _ <|> skip;
  exact (is_positive_adjoint_comp _).trace_along_nonneg V
end

end is_HS

end continuous_linear_map
