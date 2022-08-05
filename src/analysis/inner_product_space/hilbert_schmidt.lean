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

universes u₁ u₂ u₃ u₄

variables {ι : Type u₁} {𝕜 : Type u₂} {E : Type u₃} {F : Type u₄} [is_R_or_C 𝕜]
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 F] [complete_space E] [complete_space F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

section is_HS

def is_HS (T : E →L[𝕜] F) : Prop := (is_positive_adjoint_comp T).trace < ⊤

@[simp] lemma is_HS_def {T : E →L[𝕜] F} : T.is_HS ↔ (is_positive_adjoint_comp T).trace < ⊤ :=
iff.rfl

lemma is_HS_iff_summable (T : E →L[𝕜] F) (e : hilbert_basis ι 𝕜 E) :
  T.is_HS ↔ summable (λ i, ⟪T (e i), T (e i)⟫) :=
sorry

lemma is_HS_zero : (0 : E →L[𝕜] F).is_HS :=
begin
  -- Feels wrong
  let e := std_hilbert_basis 𝕜 E,
  rw is_HS_iff_summable _ e,
  simp_rw [zero_apply, inner_zero_left],
  exact summable_zero
end

private lemma add_aux₁ {S T : E →L[𝕜] F} :
  (S + T)† ∘L (S + T) = S† ∘L S + T† ∘L T + S† ∘L S + T† ∘L T - (S - T)† ∘L (S - T) :=
begin
  sorry,
  --simp only [linear_isometry_equiv.map_add, add_comp, comp_add, linear_isometry_equiv.map_sub,
  --            sub_comp, comp_sub],
  --abel
end

private lemma add_aux₂ (S T : E →L[𝕜] F) (V : submodule 𝕜 E) [finite_dimensional 𝕜 V] :
  re (trace_along V ((S + T)† ∘L (S + T))) ≤
  re (trace_along V (S† ∘L S + T† ∘L T + S† ∘L S + T† ∘L T)) :=
begin
  rw [add_aux₁, map_sub, map_sub],
  exact sub_le_self _ ((is_positive_adjoint_comp _).trace_along_nonneg V)
end

lemma is_HS.add {S T : E →L[𝕜] F} (hS : S.is_HS) (hT : T.is_HS) :
  (S + T).is_HS :=
begin
  rw is_HS_def at *,
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

lemma is_HS.smul {T : E →L[𝕜] F} (hT : T.is_HS) (a : 𝕜) :
  (a • T).is_HS :=
begin
  let e := std_hilbert_basis 𝕜 E,
  rw is_HS_iff_summable _ e at ⊢ hT,
  simp_rw [smul_apply, inner_smul_right, inner_smul_left, ← mul_assoc, mul_conj],
  exact hT.mul_left _
end

end is_HS

variables (E F)

def hilbert_schmidt_map : Type u₃ :=
({carrier := {f | f.is_HS},
  zero_mem' := is_HS_zero,
  add_mem' := λ f g hf hg, hf.add hg,
  smul_mem' := λ a f hf, hf.smul a } : submodule 𝕜 (E →L[𝕜] E))

end continuous_linear_map
