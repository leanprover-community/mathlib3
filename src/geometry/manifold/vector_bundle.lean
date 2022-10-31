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

open set topological_space
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

variables {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] {IB : model_with_corners 𝕜 EB HB}
   [charted_space HB B] [smooth_manifold_with_corners IB B]

lemma smooth_fibrewise_linear.locality_aux (e : local_homeomorph (B × F) (B × F))
  (h : ∀ p ∈ e.source, ∃ s : set (B × F), is_open s ∧ p ∈ s ∧
    ∃ (φ : B → (F ≃L[𝕜] F)) (u : set B) (hu : is_open u)
      (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x : F →L[𝕜] F)) u)
      (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((φ x).symm : F →L[𝕜] F)) u),
      (e.restr s).eq_on_source
            (fiberwise_linear.local_homeomorph φ hu hφ.continuous_on h2φ.continuous_on)) :
  ∃ (Φ : B → (F ≃L[𝕜] F)) (U : set B) (hU : is_open U)
    (hΦ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (Φ x : F →L[𝕜] F)) U)
    (h2Φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((Φ x).symm : F →L[𝕜] F)) U),
    e.eq_on_source (fiberwise_linear.local_homeomorph Φ hU hΦ.continuous_on h2Φ.continuous_on) :=
begin
  classical,
  rw set_coe.forall' at h,
  choose! s hs hsp φ u hu hφ h2φ heφ using h,
  have H₀ : ∀ p : e.source, e.source ∩ s p = u p ×ˢ univ,
  { intros p,
    rw ← e.restr_source' (s _) (hs _),
    exact (heφ p).1 },
  have H₀'' : ∀ p : e.source, (p : B × F).fst ∈ u p,
  { intros p,
    suffices : (p : B × F) ∈ (u p : set B) ×ˢ (univ : set F),
    { simpa only with mfld_simps using this },
    rw ← H₀,
    exact ⟨p.prop, hsp p⟩ },
  have H₀' : ∀ p : e.source, eq_on e (λ q, (q.1, φ p q.1 q.2)) (e.source ∩ s p),
  { intros p,
    rw ← e.restr_source' (s _) (hs _),
    exact (heφ p).2 },
  have H₁ : ∀ (p p' : e.source) (y : B) (hyp : y ∈ u p) (hyp' : y ∈ u p'),
    φ p y = φ p' y,
  { intros p p' y hyx hyx',
    ext v,
    have h1 : e (y, v) = (y, φ p y v) := H₀' _ (by simp only [H₀, hyx] with mfld_simps),
    have h2 : e (y, v) = (y, φ p' y v) := H₀' _ (by simp only [H₀, hyx'] with mfld_simps),
    exact congr_arg prod.snd (h1.symm.trans h2) },
  let U : set B := sorry, --prod.fst '' e.source,
  have hU : is_open U := sorry,
  have H₂ : U ⊆ prod.fst '' e.source := sorry,
  have H₂' : prod.fst '' e.source ⊆ U := sorry,
  have H₃ : U ⊆ ⋃ i, u i := sorry,
  have H₄ : e.source = U ×ˢ univ := sorry,
  let Φ₀ : U → F ≃L[𝕜] F := Union_lift u (λ x, (φ x) ∘ coe) H₁ U H₃,
  let Φ : B → F ≃L[𝕜] F := λ y, if hy : y ∈ U then Φ₀ ⟨y, hy⟩ else continuous_linear_equiv.refl 𝕜 F,
  have hΦφ : ∀ x : e.source, ∀ y ∈ U ∩ u x, Φ y = φ x y,
  { rintros x y ⟨hyU, hyu⟩,
    refine (dif_pos hyU).trans _,
    exact Union_lift_mk ⟨y, hyu⟩ _ },
  have hΦ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, (Φ y : F →L[𝕜] F)) U,
  sorry { apply cont_mdiff_on_of_locally_cont_mdiff_on,
    intros x hx,
    obtain ⟨p, hp, rfl⟩ := H₂ hx,
    refine ⟨u ⟨p, hp⟩, hu ⟨p, hp⟩, H₀'' _, _⟩,
    refine cont_mdiff_on.congr ((hφ ⟨p, hp⟩).mono _) _,
    { mfld_set_tac },
    intros y hy,
    rw hΦφ ⟨p, hp⟩ y hy },
  have h2Φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, ((Φ y).symm : F →L[𝕜] F)) U,
  { sorry },
  have heΦ : e.eq_on_source (fiberwise_linear.local_homeomorph Φ hU hΦ.continuous_on h2Φ.continuous_on),
  { refine ⟨H₄, _⟩,
    intros p hp,
    rw H₀' ⟨p, hp⟩ ⟨hp, hsp _⟩,
    congrm (_, _),
    rw hΦφ,
    refine ⟨H₂' (mem_image_of_mem _ hp), H₀'' _⟩ },
  exact ⟨Φ, U, hU, hΦ, h2Φ, heΦ⟩,
end

variables (F B IB)

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
  locality' := begin
    simp_rw [mem_Union],
    exact smooth_fibrewise_linear.locality_aux,
  end, -- a bit tricky, need to glue together a family of `φ`
  eq_on_source' := begin
    simp_rw [mem_Union],
    rintros e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee',
    exact ⟨φ, U, hU, hφ, h2φ, setoid.trans hee' heφ⟩,
  end }
