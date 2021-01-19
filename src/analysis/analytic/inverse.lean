/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.analytic.composition

open_locale big_operators classical
open finset

namespace formal_multilinear_series

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]

(p : formal_multilinear_series 𝕜 E F)
(i : F →L[𝕜] E)

noncomputable def left_inv (p : formal_multilinear_series 𝕜 E F)
(i : E ≃L[𝕜] F) : formal_multilinear_series 𝕜 F E
| 0 := 0
| 1 := (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm
| (n+2) := - ∑ c : {c : composition (n+2) // c.length < n + 2},
    (have (c : composition (n+2)).length < n+2 := c.2,
      (left_inv (c : composition (n+2)).length).comp_along_composition
        (p.comp_continuous_linear_map i.symm) c)

lemma left_inv_comp (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) :
  (left_inv p i).comp p = id 𝕜 E :=
begin
  ext n v,
  cases n,
  { simp only [left_inv, continuous_multilinear_map.zero_apply, id_apply_ne_one, ne.def,
      not_false_iff, zero_ne_one, comp_coeff_zero']},
  cases n,
  { simp only [left_inv, comp_coeff_one, h, id_apply_one, continuous_linear_equiv.coe_apply,
      continuous_linear_equiv.symm_apply_apply, continuous_multilinear_curry_fin1_symm_apply] },
  have A : (finset.univ : finset (composition (n+2)))
    = {c | composition.length c < n + 2}.to_finset ∪ {composition.ones (n+2)},
  { refine subset.antisymm (λ c hc, _) (subset_univ _),
    by_cases h : c.length < n + 2,
    { simp [h] },
    { simp [composition.eq_ones_iff_le_length.2 (not_lt.1 h)] } },
  have B : disjoint ({c | composition.length c < n + 2} : set (composition (n + 2))).to_finset
    {composition.ones (n+2)}, by simp,
  have C : (p.left_inv i (composition.ones (n + 2)).length)
    (λ (j : fin (composition.ones n.succ.succ).length), p 1 (λ (k : fin 1),
      v ((fin.cast_le (composition.length_le _)) j)))
    = p.left_inv i (n+2) (λ (j : fin (n+2)), p 1 (λ k, v j)),
  { apply formal_multilinear_series.congr _ (composition.ones_length _) (λ j hj1 hj2, _),
    exact formal_multilinear_series.congr _ rfl (λ k hk1 hk2, by congr) },
  have D : p.left_inv i (n+2) (λ (j : fin (n+2)), p 1 (λ k, v j)) =
    - ∑ (c : composition (n + 2)) in {c : composition (n + 2) | c.length < n + 2}.to_finset,
        (p.left_inv i c.length) (p.apply_composition c v),
  { simp only [left_inv, continuous_multilinear_map.neg_apply, neg_inj,
      continuous_multilinear_map.sum_apply],
    convert (sum_subtype_to_finset (λ (c : composition (n+2)), c.length < n+2)
      (λ (c : composition (n+2)), (continuous_multilinear_map.comp_along_composition
        (p.comp_continuous_linear_map ↑(i.symm)) c (p.left_inv i c.length))
          (λ (j : fin (n + 2)), p 1 (λ (k : fin 1), v j)))).symm.trans _,
    simp only [comp_continuous_linear_map_apply_composition,
      continuous_multilinear_map.comp_along_composition_apply],
    congr,
    ext c,
    congr,
    ext k,
    simp [h] },


  simp [formal_multilinear_series.comp, show n + 2 ≠ 1, by dec_trivial, A, finset.sum_union B,
    apply_composition_ones, C, D],
end


end formal_multilinear_series
