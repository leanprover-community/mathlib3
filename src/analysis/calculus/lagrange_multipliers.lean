/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.inverse
import linear_algebra.dual

/-!
# Lagrange multipliers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we formalize the
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) method of solving
conditional extremum problems: if a function `φ` has a local extremum at `x₀` on the set
`f ⁻¹' {f x₀}`, `f x = (f₀ x, ..., fₙ₋₁ x)`, then the differentials of `fₖ` and `φ` are linearly
dependent. First we formulate a geometric version of this theorem which does not rely on the
target space being `ℝⁿ`, then restate it in terms of coordinates.

## TODO

Formalize Karush-Kuhn-Tucker theorem

## Tags

lagrange multiplier, local extremum

-/

open filter set
open_locale topology filter big_operators
variables {E F : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {f : E → F} {φ : E → ℝ} {x₀ : E} {f' : E →L[ℝ] F} {φ' : E →L[ℝ] ℝ}

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then the linear map `x ↦ (f' x, φ' x)` is not surjective. -/
lemma is_local_extr_on.range_ne_top_of_has_strict_fderiv_at
  (hextr : is_local_extr_on φ {x | f x = f x₀} x₀) (hf' : has_strict_fderiv_at f f' x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  linear_map.range (f'.prod φ') ≠ ⊤ :=
begin
  intro htop,
  set fφ := λ x, (f x, φ x),
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀),
  { change map (prod.snd ∘ fφ) (𝓝[fφ ⁻¹' {p | p.1 = f x₀}] x₀) = 𝓝 (φ x₀),
    rw [← map_map, nhds_within, map_inf_principal_preimage,
      (hf'.prod hφ').map_nhds_eq_of_surj htop],
    exact map_snd_nhds_within _ },
  exact hextr.not_nhds_le_map A.ge
end

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then there exist `Λ : dual ℝ F` and `Λ₀ : ℝ` such that `(Λ, Λ₀) ≠ 0` and
`Λ (f' x) + Λ₀ • φ' x = 0` for all `x`. -/
lemma is_local_extr_on.exists_linear_map_of_has_strict_fderiv_at
  (hextr : is_local_extr_on φ {x | f x = f x₀} x₀) (hf' : has_strict_fderiv_at f f' x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ∃ (Λ : module.dual ℝ F) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∀ x, Λ (f' x) + Λ₀ • φ' x = 0 :=
begin
  rcases submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.2 $ hextr.range_ne_top_of_has_strict_fderiv_at hf' hφ') with ⟨Λ', h0, hΛ'⟩,
  set e : ((F →ₗ[ℝ] ℝ) × ℝ) ≃ₗ[ℝ] (F × ℝ →ₗ[ℝ] ℝ) :=
    ((linear_equiv.refl ℝ (F →ₗ[ℝ] ℝ)).prod (linear_map.ring_lmap_equiv_self ℝ ℝ ℝ).symm).trans
      (linear_map.coprod_equiv ℝ),
  rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩,
  refine ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, λ x, _⟩,
  convert linear_map.congr_fun (linear_map.range_le_ker_iff.1 hΛ') x using 1,
  -- squeezed `simp [mul_comm]` to speed up elaboration
  simp only [mul_comm, algebra.id.smul_eq_mul, linear_equiv.trans_apply, linear_equiv.prod_apply,
             linear_equiv.refl_apply, linear_map.ring_lmap_equiv_self_symm_apply,
             linear_map.coprod_equiv_apply, continuous_linear_map.to_linear_map_eq_coe,
             continuous_linear_map.coe_prod, linear_map.coprod_comp_prod, linear_map.add_apply,
             linear_map.coe_comp, continuous_linear_map.coe_coe, linear_map.coe_smul_right,
             linear_map.one_apply]
end

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, and both `f : E → ℝ` and `φ` are strictly differentiable at `x₀`, then there exist
`a b : ℝ` such that `(a, b) ≠ 0` and `a • f' + b • φ' = 0`. -/
lemma is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d
  {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  (hextr : is_local_extr_on φ {x | f x = f x₀} x₀) (hf' : has_strict_fderiv_at f f' x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ∃ (a b : ℝ), (a, b) ≠ 0 ∧ a • f' + b • φ' = 0 :=
begin
  obtain ⟨Λ, Λ₀, hΛ, hfΛ⟩ := hextr.exists_linear_map_of_has_strict_fderiv_at hf' hφ',
  refine ⟨Λ 1, Λ₀, _, _⟩,
  { contrapose! hΛ,
    simp only [prod.mk_eq_zero] at ⊢ hΛ,
    refine ⟨linear_map.ext (λ x, _), hΛ.2⟩,
    simpa [hΛ.1] using Λ.map_smul x 1 },
  { ext x,
    have H₁ : Λ (f' x) = f' x * Λ 1,
    { simpa only [mul_one, algebra.id.smul_eq_mul] using Λ.map_smul (f' x) 1 },
    have H₂ : f' x * Λ 1  + Λ₀ * φ' x = 0,
    { simpa only [algebra.id.smul_eq_mul, H₁] using hfΛ x },
    simpa [mul_comm] using H₂ }
end

/-- Lagrange multipliers theorem, 1d version. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : E →L[ℝ] ℝ` are linearly dependent:
there exist `Λ : ι → ℝ` and `Λ₀ : ℝ`, `(Λ, Λ₀) ≠ 0`, such that `∑ i, Λ i • f' i + Λ₀ • φ' = 0`.

See also `is_local_extr_on.linear_dependent_of_has_strict_fderiv_at` for a version that
states `¬linear_independent ℝ _` instead of existence of `Λ` and `Λ₀`. -/
lemma is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at {ι : Type*} [fintype ι]
  {f : ι → E → ℝ} {f' : ι → E →L[ℝ] ℝ}
  (hextr : is_local_extr_on φ {x | ∀ i, f i x = f i x₀} x₀)
  (hf' : ∀ i, has_strict_fderiv_at (f i) (f' i) x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ∃ (Λ : ι → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∑ i, Λ i • f' i + Λ₀ • φ' = 0 :=
begin
  letI := classical.dec_eq ι,
  replace hextr : is_local_extr_on φ {x | (λ i, f i x) = (λ i, f i x₀)} x₀,
    by simpa only [function.funext_iff] using hextr,
  rcases hextr.exists_linear_map_of_has_strict_fderiv_at
    (has_strict_fderiv_at_pi.2 (λ i, hf' i)) hφ'
    with ⟨Λ, Λ₀, h0, hsum⟩,
  rcases (linear_equiv.pi_ring ℝ ℝ ι ℝ).symm.surjective Λ with ⟨Λ, rfl⟩,
  refine ⟨Λ, Λ₀, _, _⟩,
  { simpa only [ne.def, prod.ext_iff, linear_equiv.map_eq_zero_iff, prod.fst_zero] using h0 },
  { ext x, simpa [mul_comm] using hsum x }
end

/-- Lagrange multipliers theorem. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : E →L[ℝ] ℝ` are linearly dependent.

See also `is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at` for a version that
that states existence of Lagrange multipliers `Λ` and `Λ₀` instead of using
`¬linear_independent ℝ _` -/
lemma is_local_extr_on.linear_dependent_of_has_strict_fderiv_at {ι : Type*} [finite ι]
  {f : ι → E → ℝ} {f' : ι → E →L[ℝ] ℝ}
  (hextr : is_local_extr_on φ {x | ∀ i, f i x = f i x₀} x₀)
  (hf' : ∀ i, has_strict_fderiv_at (f i) (f' i) x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ¬linear_independent ℝ (option.elim φ' f' : option ι → E →L[ℝ] ℝ) :=
begin
  casesI nonempty_fintype ι,
  rw [fintype.linear_independent_iff], push_neg,
  rcases hextr.exists_multipliers_of_has_strict_fderiv_at hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩,
  refine ⟨option.elim Λ₀ Λ, _, _⟩,
  { simpa [add_comm] using hΛf },
  { simpa [function.funext_iff, not_and_distrib, or_comm, option.exists] using hΛ }
end
