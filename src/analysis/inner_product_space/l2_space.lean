/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.basic
import analysis.normed_space.lp_space

/-!
# Inner product space structure on `lp 2`

Given a family `(G : ι → Type*) [Π i, inner_product_space 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑ i, ∥f i∥ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the Hilbert sum of the family `G`.

The space `lp G 2` already held a normed space structure, `lp.normed_space`, so the work in this
file is to define the inner product and show it is compatible.

If each `G i` is a Hilbert space (i.e., complete), then the Hilbert sum `lp G 2` is also a Hilbert
space; again this follows from `lp.complete_space`, the case of general `p`.

By choosing `G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this
construction.

## Keywords

Hilbert space, Hilbert sum, l2
-/

open is_R_or_C
open_locale ennreal complex_conjugate

local attribute [instance] fact_one_le_two_ennreal

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace lp

lemma summable_inner (f g : lp G 2) : summable (λ i, ⟪f i, g i⟫) :=
begin
  -- Apply the Direct Comparison Test, comparing with ∑' i, ∥f i∥ * ∥g i∥ (summable by Hölder)
  refine summable_of_norm_bounded (λ i, ∥f i∥ * ∥g i∥) (lp.summable_mul _ f g) _,
  { rw real.is_conjugate_exponent_iff;
    norm_num },
  intros i,
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm _ _,
end

instance : inner_product_space 𝕜 (lp G 2) :=
{ inner := λ f g, ∑' i, ⟪f i, g i⟫,
  norm_sq_eq_inner := λ f, begin
    calc ∥f∥ ^ 2 = ∥f∥ ^ (2:ℝ≥0∞).to_real : by norm_cast
    ... = ∑' i, ∥f i∥ ^ (2:ℝ≥0∞).to_real : lp.norm_rpow_eq_tsum _ f
    ... = ∑' i, ∥f i∥ ^ 2 : by norm_cast
    ... = ∑' i, re ⟪f i, f i⟫ : by simp only [norm_sq_eq_inner]
    ... = re (∑' i, ⟪f i, f i⟫) : (is_R_or_C.re_clm.map_tsum _).symm
    ... = _ : by congr,
    { norm_num },
    { exact summable_inner f f },
  end,
  conj_sym := λ f g, begin
    calc conj _ = conj ∑' i, ⟪g i, f i⟫ : by congr
    ... = ∑' i, conj ⟪g i, f i⟫ : is_R_or_C.conj_cle.map_tsum
    ... = ∑' i, ⟪f i, g i⟫ : by simp only [inner_conj_sym]
    ... = _ : by congr,
  end,
  add_left := λ f₁ f₂ g, begin
    calc _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ : _
    ... = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) :
          by simp only [inner_add_left, pi.add_apply, coe_fn_add]
    ... = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ : tsum_add _ _
    ... = _ : by congr,
    { congr, },
    { exact summable_inner f₁ g },
    { exact summable_inner f₂ g }
  end,
  smul_left := λ f g c, begin
    calc _ = ∑' i, ⟪c • f i, g i⟫ : _
    ... = ∑' i, conj c * ⟪f i, g i⟫ : by simp only [inner_smul_left]
    ... = conj c * ∑' i, ⟪f i, g i⟫ : tsum_mul_left
    ... = _ : _,
    { simp only [coe_fn_smul, pi.smul_apply] },
    { congr },
  end,
  .. lp.normed_space }

lemma inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ := rfl

lemma has_sum_inner (f g : lp G 2) : has_sum (λ i, ⟪f i, g i⟫) ⟪f, g⟫ :=
(summable_inner f g).has_sum

end lp
