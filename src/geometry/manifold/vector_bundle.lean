/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.cont_mdiff

/-! # Smooth vector bundles

This file will eventually contain the definition of a smooth vector bundle.  For now, it contains
preliminaries regarding an associated `structure_groupoid`, the groupoid of `smooth_fibrewise_linear`
functions. -/

noncomputable theory

open set
open_locale manifold topological_space

/-! ### The groupoid of smooth, fibrewise-linear maps -/

variables {𝕜 B F : Type*} [topological_space B]
variables [nontrivially_normed_field 𝕜] [normed_add_comm_group F] [normed_space 𝕜 F]

/-- For `B` a topological space and `F` a `𝕜`-normed space, a map from `U : set B` to `F ≃L[𝕜] F`
determines a local homeomorphism from `B × F` to itself by its action fibrewise. -/
def fiberwise_linear.local_homeomorph (φ : B → F ≃L[𝕜] F) {U : set B} (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U) :
  local_homeomorph (B × F) (B × F) :=
{ to_fun := λ x, (x.1, φ x.1 x.2),
  inv_fun := λ x, (x.1, (φ x.1).symm x.2),
  source := U ×ˢ univ,
  target := U ×ˢ univ,
  map_source' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  map_target' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  left_inv' := sorry,
  right_inv' := sorry,
  open_source := hU.prod is_open_univ,
  open_target := hU.prod is_open_univ,
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry }

lemma fiberwise_linear.source_trans_local_homeomorph {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U') :
  (fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ').source = (U ∩ U') ×ˢ univ :=
begin
  sorry,
end

lemma fiberwise_linear.trans_local_homeomorph_apply {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U')
  {b : B}
  (hb : b ∈ U ∩ U')
  (v : F) :
  (fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ') ⟨b, v⟩ = ⟨b, φ' b (φ b v)⟩ :=
begin
  sorry,
end

variables (F B) {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
   [charted_space HB B] [smooth_manifold_with_corners IB B]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] (IM : model_with_corners 𝕜 EM HM)

/-- For `B` a manifold and `F` a normed space, the groupoid on `B × F` consisting of local
homeomorphisms which are bi-smooth and fibrewise linear. -/
def smooth_fiberwise_linear : structure_groupoid (B × F) :=
{ members := ⋃ (φ : B → F ≃L[𝕜] F) (U : set B) (hU : is_open U)
  (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x).symm : B → F →L[𝕜] F) U),
  {e | e.eq_on_source (fiberwise_linear.local_homeomorph φ hU hφ.continuous_on h2φ.continuous_on)},
  trans' := begin
    simp_rw [mem_Union],
    rintros e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ ⟨φ', U', hU', hφ', h2φ', heφ'⟩,
    refine ⟨λ b, (φ b).trans (φ' b), _, hU.inter hU', _, _, setoid.trans (heφ.trans' heφ') ⟨_, _⟩⟩,
    { sorry },
    { sorry }, -- two smoothness checks
    { apply fiberwise_linear.source_trans_local_homeomorph },
    { rintros ⟨b, v⟩ hb,
      apply fiberwise_linear.trans_local_homeomorph_apply,
      rw fiberwise_linear.source_trans_local_homeomorph at hb,
      simpa [-mem_inter] using hb }
  end,
  symm' := begin
    simp_rw [mem_Union],
    rintros e ⟨φ, U, hU, hφ, h2φ, heφ⟩,
    refine ⟨λ b, (φ b).symm, U, hU, h2φ, _, heφ.symm'⟩,
    simp_rw continuous_linear_equiv.symm_symm,
    exact hφ
  end,
  id_mem' := begin
    simp_rw [mem_Union],
    refine ⟨λ b, continuous_linear_equiv.refl 𝕜 F, univ, is_open_univ, _, _, ⟨_, λ b hb, _⟩⟩,
    { apply cont_mdiff_on_const },
    { apply cont_mdiff_on_const },
    { simp [fiberwise_linear.local_homeomorph] },
    { simp [fiberwise_linear.local_homeomorph] },
  end,
  locality' := sorry, -- a bit tricky, need to glue together a family of `φ`
  eq_on_source' := begin
    simp_rw [mem_Union],
    rintros e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee',
    exact ⟨φ, U, hU, hφ, h2φ, setoid.trans hee' heφ⟩,
  end }
