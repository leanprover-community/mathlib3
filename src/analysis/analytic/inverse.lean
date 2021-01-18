/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.analytic.composition

open_locale big_operators

namespace formal_multilinear_series

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]

(p : formal_multilinear_series 𝕜 E F)
(i : F →L[𝕜] E)

noncomputable def my_inv (p : formal_multilinear_series 𝕜 E F)
(i : E ≃L[𝕜] F) : formal_multilinear_series 𝕜 F E
| 0 := 0
| 1 := (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm
| (n+2) := - ∑ c : {c : composition (n+2) // c.length < n + 2},
    (have c.1.length < n+2 := c.2,
      (my_inv c.1.length).comp_along_composition (p.comp_continuous_linear_map i.symm) c)

lemma glouk (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) :
  (my_inv p i).comp p = id 𝕜 E :=
begin
  ext n v,
  cases n,
  { simp only [my_inv, continuous_multilinear_map.zero_apply, id_apply_ne_one, ne.def,
      not_false_iff, zero_ne_one, comp_coeff_zero']},
  cases n,
  { simp only [my_inv, comp_coeff_one, h, id_apply_one, continuous_linear_equiv.coe_apply,
      continuous_linear_equiv.symm_apply_apply, continuous_multilinear_curry_fin1_symm_apply] },
  have : n + 2 ≠ 1, by dec_trivial,
  simp [formal_multilinear_series.comp, this],
end


end formal_multilinear_series
