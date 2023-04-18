/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import geometry.manifold.mfderiv

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `mdifferentiable`, `cont_mdiff`, `mfderiv`, `tangent_map`
and related notions.

## Main statements

* `cont_mdiff_on.cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `cont_mdiff.cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/

open set function filter charted_space smooth_manifold_with_corners bundle
open_locale topology manifold bundle

/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- declare some additional normed spaces, used for fibers of vector bundles
{F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
{F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
-- declare functions, sets, points and smoothness indices
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : ℕ∞}

/-! ### Deducing differentiability from smoothness -/

lemma cont_mdiff_within_at.mdifferentiable_within_at
  (hf : cont_mdiff_within_at I I' n f s x) (hn : 1 ≤ n) :
  mdifferentiable_within_at I I' f s x :=
begin
  suffices h : mdifferentiable_within_at I I' f (s ∩ (f ⁻¹' (ext_chart_at I' (f x)).source)) x,
  { rwa mdifferentiable_within_at_inter' at h,
    apply (hf.1).preimage_mem_nhds_within,
    exact ext_chart_at_source_mem_nhds I' (f x) },
  rw mdifferentiable_within_at_iff,
  exact ⟨hf.1.mono (inter_subset_left _ _),
    (hf.2.differentiable_within_at hn).mono (by mfld_set_tac)⟩,
end

lemma cont_mdiff_at.mdifferentiable_at (hf : cont_mdiff_at I I' n f x) (hn : 1 ≤ n) :
  mdifferentiable_at I I' f x :=
mdifferentiable_within_at_univ.1 $ cont_mdiff_within_at.mdifferentiable_within_at hf hn

lemma cont_mdiff_on.mdifferentiable_on (hf : cont_mdiff_on I I' n f s) (hn : 1 ≤ n) :
  mdifferentiable_on I I' f s :=
λ x hx, (hf x hx).mdifferentiable_within_at hn

lemma cont_mdiff.mdifferentiable (hf : cont_mdiff I I' n f) (hn : 1 ≤ n) :
  mdifferentiable I I' f :=
λ x, (hf x).mdifferentiable_at hn

lemma smooth_within_at.mdifferentiable_within_at
  (hf : smooth_within_at I I' f s x) : mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_within_at le_top

lemma smooth_at.mdifferentiable_at (hf : smooth_at I I' f x) : mdifferentiable_at I I' f x :=
hf.mdifferentiable_at le_top

lemma smooth_on.mdifferentiable_on (hf : smooth_on I I' f s) : mdifferentiable_on I I' f s :=
hf.mdifferentiable_on le_top

lemma smooth.mdifferentiable (hf : smooth I I' f) : mdifferentiable I I' f :=
cont_mdiff.mdifferentiable hf le_top

lemma smooth.mdifferentiable_at (hf : smooth I I' f) : mdifferentiable_at I I' f x :=
hf.mdifferentiable x

lemma smooth.mdifferentiable_within_at (hf : smooth I I' f) :
  mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_at.mdifferentiable_within_at

/-! ### The derivative of a smooth function is smooth -/

section mfderiv

include Is I's Js

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` is `C^n` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
`cont_mdiff_at.mfderiv_id` and `cont_mdiff_at.mfderiv_const` are special cases of this.

This lemma should be generalized to a `cont_mdiff_within_at` for `mfderiv_within`. If we do that, we
can deduce `cont_mdiff_on.cont_mdiff_on_tangent_map_within` from this.
-/
lemma cont_mdiff_at.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x₀, g x₀))
  (hg : cont_mdiff_at J I m g x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) x₀ :=
begin
  have h4f : continuous_at (λ x, f x (g x)) x₀,
  { apply continuous_at.comp (by apply hf.continuous_at) (continuous_at_id.prod hg.continuous_at) },
  have h4f := h4f.preimage_mem_nhds (ext_chart_at_source_mem_nhds I' (f x₀ (g x₀))),
  have h3f := cont_mdiff_at_iff_cont_mdiff_at_nhds.mp (hf.of_le $ (self_le_add_left 1 m).trans hmn),
  have h2f : ∀ᶠ x₂ in 𝓝 x₀, cont_mdiff_at I I' 1 (f x₂) (g x₂),
  { refine ((continuous_at_id.prod hg.continuous_at).tendsto.eventually h3f).mono (λ x hx, _),
    exact hx.comp (g x) (cont_mdiff_at_const.prod_mk cont_mdiff_at_id) },
  have h2g := hg.continuous_at.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x₀)),
  have : cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜
    (ext_chart_at I' (f x₀ (g x₀)) ∘ f ((ext_chart_at J x₀).symm x) ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g ((ext_chart_at J x₀).symm x))))
    (range J) (ext_chart_at J x₀ x₀),
  { rw [cont_mdiff_at_iff] at hf hg,
    simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm,
      model_with_corners.range_prod] at hf ⊢,
    refine cont_diff_within_at.fderiv_within _ hg.2 I.unique_diff hmn (mem_range_self _) _,
    { simp_rw [ext_chart_at_to_inv], exact hf.2 },
    { rw [← image_subset_iff],
      rintros _ ⟨x, hx, rfl⟩,
      exact mem_range_self _ } },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ f x ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g x))) x₀,
  { simp_rw [cont_mdiff_at_iff_source_of_mem_source (mem_chart_source G x₀),
      cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
    exact this },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x (g x))).symm ∘
      written_in_ext_chart_at I I' (g x) (f x) ∘ ext_chart_at I (g x) ∘
      (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x))) x₀,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f],
    intros x₂ hx₂ h2x₂,
    have : ∀ x ∈ (ext_chart_at I (g x₀)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
        (ext_chart_at I (g x₀)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
      (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
      written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
      (ext_chart_at I (g x₀)).symm) x =
      ext_chart_at I' (f x₀ (g x₀)) (f x₂ ((ext_chart_at I (g x₀)).symm x)),
    { rintro x ⟨hx, h2x⟩,
      simp_rw [written_in_ext_chart_at, function.comp_apply],
      rw [(ext_chart_at I (g x₂)).left_inv hx, (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x] },
    refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
    refine eventually_of_mem (inter_mem _ _) this,
    { exact ext_chart_at_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
    refine ext_chart_at_preimage_mem_nhds' _ _ hx₂ _,
    exact (h2x₂.continuous_at).preimage_mem_nhds (ext_chart_at_source_mem_nhds _ _) },
  /- The conclusion is equal to the following, when unfolding coord_change of
    `tangent_bundle_core` -/
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, (fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x (g x))).symm)
        (range I') (ext_chart_at I' (f x (g x)) (f x (g x)))).comp
        ((mfderiv I I' (f x) (g x)).comp (fderiv_within 𝕜 (ext_chart_at I (g x) ∘
        (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x))))) x₀,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f, h4f],
    intros x₂ hx₂ h2x₂ h3x₂,
    symmetry,
    rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
    have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x₀) $
      local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
      .differentiable_within_at le_top,
    have hI' := (cont_diff_within_at_ext_coord_change I' (f x₀ (g x₀)) (f x₂ (g x₂)) $
      local_equiv.mem_symm_trans_source _
      (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
    have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
    refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
    { exact λ x _, mem_range_self _ },
    { exact λ x _, mem_range_self _ },
    { simp_rw [written_in_ext_chart_at, function.comp_apply,
        (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
    { simp_rw [function.comp_apply, (ext_chart_at I (g x₀)).left_inv hx₂] } },
  refine this.congr_of_eventually_eq _,
  filter_upwards [h2g, h4f] with x hx h2x,
  rw [in_tangent_coordinates_eq],
  { refl },
  { rwa [ext_chart_at_source] at hx },
  { rwa [ext_chart_at_source] at h2x },
end

omit Js

/-- The function `x ↦ D_yf(x,y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `(x₀, x₀)`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `cont_mdiff_at.mfderiv` (with `g = id`),
and `cont_mdiff_at.mfderiv_const` is a special case of this.
-/
lemma cont_mdiff_at.mfderiv_id {x₀ : M} (f : M → M → M')
  (hf : cont_mdiff_at (I.prod I) I' n (function.uncurry f) (x₀, x₀)) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (in_tangent_coordinates I I' id (λ x, f x x) (λ x, mfderiv I I' (f x) x) x₀) x₀ :=
hf.mfderiv f id cont_mdiff_at_id hmn

/-- The derivative `D_yf(y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of See `cont_mdiff_at.mfderiv_id` where `f` does not contain any parameters.
-/
lemma cont_mdiff_at.mfderiv_const {x₀ : M} {f : M → M'}
  (hf : cont_mdiff_at I I' n f x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m (in_tangent_coordinates I I' id f (mfderiv I I' f) x₀) x₀ :=
begin
  have : cont_mdiff_at (I.prod I) I' n (λ x : M × M, f x.2) (x₀, x₀) :=
  cont_mdiff_at.comp (x₀, x₀) hf cont_mdiff_at_snd,
  apply cont_mdiff_at.mfderiv_id (λ x, f) this hmn,
end

end mfderiv

/-! ### The tangent map of a smooth function is smooth -/

section tangent_map

/-- If a function is `C^n` with `1 ≤ n` on a domain with unique derivatives, then its bundled
derivative is continuous. In this auxiliary lemma, we prove this fact when the source and target
space are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.continuous_on_tangent_map_within`-/
lemma cont_mdiff_on.continuous_on_tangent_map_within_aux
  {f : H → H'} {s : set H}
  (hf : cont_mdiff_on I I' n f s) (hn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (tangent_map_within I I' f s) (π (tangent_space I) ⁻¹' s) :=
begin
  suffices h : continuous_on (λ (p : H × E), (f p.fst,
    (fderiv_within 𝕜 (written_in_ext_chart_at I I' p.fst f) (I.symm ⁻¹' s ∩ range I)
      ((ext_chart_at I p.fst) p.fst) : E →L[𝕜] E') p.snd)) (prod.fst ⁻¹' s),
  { have A := (tangent_bundle_model_space_homeomorph H I).continuous,
    rw continuous_iff_continuous_on_univ at A,
    have B := ((tangent_bundle_model_space_homeomorph H' I').symm.continuous.comp_continuous_on h)
      .comp' A,
    have : (univ ∩ ⇑(tangent_bundle_model_space_homeomorph H I) ⁻¹' (prod.fst ⁻¹' s)) =
      π (tangent_space I) ⁻¹' s,
      by { ext ⟨x, v⟩, simp only with mfld_simps },
    rw this at B,
    apply B.congr,
    rintros ⟨x, v⟩ hx,
    dsimp [tangent_map_within],
    ext, { refl },
    simp only with mfld_simps,
    apply congr_fun,
    apply congr_arg,
    rw mdifferentiable_within_at.mfderiv_within (hf.mdifferentiable_on hn x hx),
    refl },
  suffices h : continuous_on (λ (p : H × E), (fderiv_within 𝕜 (I' ∘ f ∘ I.symm)
    (I.symm ⁻¹' s ∩ range I) (I p.fst) : E →L[𝕜] E') p.snd) (prod.fst ⁻¹' s),
  { dsimp [written_in_ext_chart_at, ext_chart_at],
    apply continuous_on.prod
      (continuous_on.comp hf.continuous_on continuous_fst.continuous_on (subset.refl _)),
    apply h.congr,
    assume p hp,
    refl },
  suffices h : continuous_on (fderiv_within 𝕜 (I' ∘ f ∘ I.symm)
                     (I.symm ⁻¹' s ∩ range I)) (I '' s),
  { have C := continuous_on.comp h I.continuous_to_fun.continuous_on (subset.refl _),
    have A : continuous (λq : (E →L[𝕜] E') × E, q.1 q.2) :=
      is_bounded_bilinear_map_apply.continuous,
    have B : continuous_on (λp : H × E,
      (fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
                       (I p.1), p.2)) (prod.fst ⁻¹' s),
    { apply continuous_on.prod _ continuous_snd.continuous_on,
      refine (continuous_on.comp C continuous_fst.continuous_on _ : _),
      exact preimage_mono (subset_preimage_image _ _) },
    exact A.comp_continuous_on B },
  rw cont_mdiff_on_iff at hf,
  let x : H := I.symm (0 : E),
  let y : H' := I'.symm (0 : E'),
  have A := hf.2 x y,
  simp only [I.image_eq, inter_comm] with mfld_simps at A ⊢,
  apply A.continuous_on_fderiv_within _ hn,
  convert hs.unique_diff_on_target_inter x using 1,
  simp only [inter_comm] with mfld_simps
end

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative is
`C^m` when `m+1 ≤ n`. In this auxiliary lemma, we prove this fact when the source and target space
are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.cont_mdiff_on_tangent_map_within` -/
lemma cont_mdiff_on.cont_mdiff_on_tangent_map_within_aux
  {f : H → H'} {s : set H}
  (hf : cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s) (π (tangent_space I) ⁻¹' s) :=
begin
  have m_le_n : m ≤ n,
  { apply le_trans _ hmn,
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _,
    simpa only [add_zero] using this },
  have one_le_n : 1 ≤ n,
  { apply le_trans _ hmn,
    change 0 + 1 ≤ m + 1,
    exact add_le_add_right (zero_le _) _ },
  have U': unique_diff_on 𝕜 (range I ∩ I.symm ⁻¹' s),
  { assume y hy,
    simpa only [unique_mdiff_on, unique_mdiff_within_at, hy.1, inter_comm] with mfld_simps
      using hs (I.symm y) hy.2 },
  rw cont_mdiff_on_iff,
  refine ⟨hf.continuous_on_tangent_map_within_aux one_le_n hs, λp q, _⟩,
  have A : range I ×ˢ univ ∩
      ((equiv.sigma_equiv_prod H E).symm ∘ λ (p : E × E), ((I.symm) p.fst, p.snd)) ⁻¹'
        (π (tangent_space I) ⁻¹' s)
      = (range I ∩ I.symm ⁻¹' s) ×ˢ univ,
    by { ext ⟨x, v⟩, simp only with mfld_simps },
  suffices h : cont_diff_on 𝕜 m (((λ (p : H' × E'), (I' p.fst, p.snd)) ∘
      (equiv.sigma_equiv_prod H' E')) ∘ tangent_map_within I I' f s ∘
      ((equiv.sigma_equiv_prod H E).symm) ∘ λ (p : E × E), (I.symm p.fst, p.snd))
    ((range ⇑I ∩ ⇑(I.symm) ⁻¹' s) ×ˢ univ),
    by simpa [A] using h,
  change cont_diff_on 𝕜 m (λ (p : E × E),
    ((I' (f (I.symm p.fst)), ((mfderiv_within I I' f s (I.symm p.fst)) : E → E') p.snd) : E' × E'))
    ((range I ∩ I.symm ⁻¹' s) ×ˢ univ),
  -- check that all bits in this formula are `C^n`
  have hf' := cont_mdiff_on_iff.1 hf,
  have A : cont_diff_on 𝕜 m (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) :=
    by simpa only with mfld_simps using (hf'.2 (I.symm 0) (I'.symm 0)).of_le m_le_n,
  have B : cont_diff_on 𝕜 m ((I' ∘ f ∘ I.symm) ∘ prod.fst)
           ((range I ∩ I.symm ⁻¹' s) ×ˢ univ) :=
    A.comp (cont_diff_fst.cont_diff_on) (prod_subset_preimage_fst _ _),
  suffices C : cont_diff_on 𝕜 m (λ (p : E × E),
    ((fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) p.1 : _) p.2))
    ((range I ∩ I.symm ⁻¹' s) ×ˢ univ),
  { apply cont_diff_on.prod B _,
    apply C.congr (λp hp, _),
    simp only with mfld_simps at hp,
    simp only [mfderiv_within, hf.mdifferentiable_on one_le_n _ hp.2, hp.1, if_pos]
      with mfld_simps },
  have D : cont_diff_on 𝕜 m (λ x,
    (fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) x))
    (range I ∩ I.symm ⁻¹' s),
  { have : cont_diff_on 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) :=
      by simpa only with mfld_simps using (hf'.2 (I.symm 0) (I'.symm 0)),
    simpa only [inter_comm] using this.fderiv_within U' hmn },
  have := D.comp (cont_diff_fst.cont_diff_on) (prod_subset_preimage_fst _ _),
  have := cont_diff_on.prod this (cont_diff_snd.cont_diff_on),
  exact is_bounded_bilinear_map_apply.cont_diff.comp_cont_diff_on this,
end

include Is I's

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem cont_mdiff_on.cont_mdiff_on_tangent_map_within
  (hf : cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s)
  (π (tangent_space I) ⁻¹' s) :=
begin
  /- The strategy of the proof is to avoid unfolding the definitions, and reduce by functoriality
  to the case of functions on the model spaces, where we have already proved the result.
  Let `l` and `r` be the charts to the left and to the right, so that we have
  ```
     l^{-1}      f       r
  H --------> M ---> M' ---> H'
  ```
  Then the tangent map `T(r ∘ f ∘ l)` is smooth by a previous result. Consider the composition
  ```
      Tl        T(r ∘ f ∘ l^{-1})         Tr^{-1}
  TM -----> TH -------------------> TH' ---------> TM'
  ```
  where `Tr^{-1}` and `Tl` are the tangent maps of `r^{-1}` and `l`. Writing `Tl` and `Tr^{-1}` as
  composition of charts (called `Dl` and `il` for `l` and `Dr` and `ir` in the proof below), it
  follows that they are smooth. The composition of all these maps is `Tf`, and is therefore smooth
  as a composition of smooth maps.
  -/
  have m_le_n : m ≤ n,
  { apply le_trans _ hmn,
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _,
    simpa only [add_zero] },
  have one_le_n : 1 ≤ n,
  { apply le_trans _ hmn,
    change 0 + 1 ≤ m + 1,
    exact add_le_add_right (zero_le _) _ },
  /- First step: local reduction on the space, to a set `s'` which is contained in chart domains. -/
  refine cont_mdiff_on_of_locally_cont_mdiff_on (λp hp, _),
  have hf' := cont_mdiff_on_iff.1 hf,
  simp only with mfld_simps at hp,
  let l  := chart_at H p.proj,
  set Dl := chart_at (model_prod H E) p with hDl,
  let r  := chart_at H' (f p.proj),
  let Dr := chart_at (model_prod H' E') (tangent_map_within I I' f s p),
  let il := chart_at (model_prod H E) (tangent_map I I l p),
  let ir := chart_at (model_prod H' E') (tangent_map I I' (r ∘ f) p),
  let s' := f ⁻¹' r.source ∩ s ∩ l.source,
  let s'_lift := π (tangent_space I) ⁻¹' s',
  let s'l := l.target ∩ l.symm ⁻¹' s',
  let s'l_lift := π (tangent_space I) ⁻¹' s'l,
  rcases continuous_on_iff'.1 hf'.1 r.source r.open_source with ⟨o, o_open, ho⟩,
  suffices h : cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s) s'_lift,
  { refine ⟨π (tangent_space I) ⁻¹' (o ∩ l.source), _, _, _⟩,
    show is_open (π (tangent_space I) ⁻¹' (o ∩ l.source)), from
      (is_open.inter o_open l.open_source).preimage (continuous_proj E _) ,
    show p ∈ π (tangent_space I) ⁻¹' (o ∩ l.source),
    { simp,
      have : p.proj ∈ f ⁻¹' r.source ∩ s, by simp [hp],
      rw ho at this,
      exact this.1 },
    { have : π (tangent_space I) ⁻¹' s ∩ π (tangent_space I) ⁻¹' (o ∩ l.source) = s'_lift,
      { dsimp only [s'_lift, s'], rw [ho], mfld_set_tac },
      rw this,
      exact h } },
  /- Second step: check that all functions are smooth, and use the chain rule to write the bundled
  derivative as a composition of a function between model spaces and of charts.
  Convention: statements about the differentiability of `a ∘ b ∘ c` are named `diff_abc`. Statements
  about differentiability in the bundle have a `_lift` suffix. -/
  have U' : unique_mdiff_on I s',
  { apply unique_mdiff_on.inter _ l.open_source,
    rw [ho, inter_comm],
    exact hs.inter o_open },
  have U'l : unique_mdiff_on I s'l :=
    U'.unique_mdiff_on_preimage (mdifferentiable_chart _ _),
  have diff_f : cont_mdiff_on I I' n f s' :=
    hf.mono (by mfld_set_tac),
  have diff_r : cont_mdiff_on I' I' n r r.source :=
    cont_mdiff_on_chart,
  have diff_rf : cont_mdiff_on I I' n (r ∘ f) s',
  { apply cont_mdiff_on.comp diff_r diff_f (λx hx, _),
    simp only [s'] with mfld_simps at hx, simp only [hx] with mfld_simps },
  have diff_l : cont_mdiff_on I I n l.symm s'l,
  { have A : cont_mdiff_on I I n l.symm l.target :=
      cont_mdiff_on_chart_symm,
    exact A.mono (by mfld_set_tac) },
  have diff_rfl : cont_mdiff_on I I' n (r ∘ f ∘ l.symm) s'l,
  { apply cont_mdiff_on.comp diff_rf diff_l,
    mfld_set_tac },
  have diff_rfl_lift : cont_mdiff_on I.tangent I'.tangent m
      (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    diff_rfl.cont_mdiff_on_tangent_map_within_aux hmn U'l,
  have diff_irrfl_lift : cont_mdiff_on I.tangent I'.tangent m
      (ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l)) s'l_lift,
  { have A : cont_mdiff_on I'.tangent I'.tangent m ir ir.source := cont_mdiff_on_chart,
    exact cont_mdiff_on.comp A diff_rfl_lift (λp hp, by simp only [ir] with mfld_simps) },
  have diff_Drirrfl_lift : cont_mdiff_on I.tangent I'.tangent m
    (Dr.symm ∘ (ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l))) s'l_lift,
  { have A : cont_mdiff_on I'.tangent I'.tangent m Dr.symm Dr.target :=
      cont_mdiff_on_chart_symm,
    apply cont_mdiff_on.comp A diff_irrfl_lift (λp hp, _),
    simp only [s'l_lift] with mfld_simps at hp,
    simp only [ir, hp] with mfld_simps },
  -- conclusion of this step: the composition of all the maps above is smooth
  have diff_DrirrflilDl : cont_mdiff_on I.tangent I'.tangent m
    (Dr.symm ∘ (ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l)) ∘
      (il.symm ∘ Dl)) s'_lift,
  { have A : cont_mdiff_on I.tangent I.tangent m Dl Dl.source := cont_mdiff_on_chart,
    have A' : cont_mdiff_on I.tangent I.tangent m Dl s'_lift,
    { apply A.mono (λp hp, _),
      simp only [s'_lift] with mfld_simps at hp,
      simp only [Dl, hp] with mfld_simps },
    have B : cont_mdiff_on I.tangent I.tangent m il.symm il.target :=
      cont_mdiff_on_chart_symm,
    have C : cont_mdiff_on I.tangent I.tangent m (il.symm ∘ Dl) s'_lift :=
      cont_mdiff_on.comp B A' (λp hp, by simp only [il] with mfld_simps),
    apply cont_mdiff_on.comp diff_Drirrfl_lift C (λp hp, _),
    simp only [s'_lift] with mfld_simps at hp,
    simp only [il, s'l_lift, hp, total_space.proj] with mfld_simps },
  /- Third step: check that the composition of all the maps indeed coincides with the derivative we
  are looking for -/
  have eq_comp : ∀q ∈ s'_lift, tangent_map_within I I' f s q =
      (Dr.symm ∘ ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l) ∘
      (il.symm ∘ Dl)) q,
  { assume q hq,
    simp only [s'_lift] with mfld_simps at hq,
    have U'q : unique_mdiff_within_at I s' q.1,
      by { apply U', simp only [hq, s'] with mfld_simps },
    have U'lq : unique_mdiff_within_at I s'l (Dl q).1,
      by { apply U'l, simp only [hq, s'l] with mfld_simps },
    have A : tangent_map_within I I' ((r ∘ f) ∘ l.symm) s'l (il.symm (Dl q)) =
      tangent_map_within I I' (r ∘ f) s' (tangent_map_within I I l.symm s'l (il.symm (Dl q))),
    { refine tangent_map_within_comp_at (il.symm (Dl q)) _ _ (λp hp, _) U'lq,
      { apply diff_rf.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { apply diff_l.mdifferentiable_on one_le_n,
        simp only [s'l, hq] with mfld_simps },
      { simp only with mfld_simps at hp, simp only [hp] with mfld_simps } },
    have B : tangent_map_within I I l.symm s'l (il.symm (Dl q)) = q,
    { have : tangent_map_within I I l.symm s'l (il.symm (Dl q))
        = tangent_map I I l.symm (il.symm (Dl q)),
      { refine tangent_map_within_eq_tangent_map U'lq _,
        refine mdifferentiable_at_atlas_symm _ (chart_mem_atlas _ _) _,
        simp only [hq] with mfld_simps },
      rw [this, tangent_map_chart_symm, hDl],
      { simp only [hq] with mfld_simps,
        have : q ∈ (chart_at (model_prod H E) p).source, { simp only [hq] with mfld_simps },
        exact (chart_at (model_prod H E) p).left_inv this },
      { simp only [hq] with mfld_simps } },
    have C : tangent_map_within I I' (r ∘ f) s' q
      = tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q),
    { refine tangent_map_within_comp_at q _ _ (λr hr, _) U'q,
      { apply diff_r.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { apply diff_f.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { simp only [s'] with mfld_simps at hr,
        simp only [hr] with mfld_simps } },
    have D : Dr.symm (ir (tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q)))
      = tangent_map_within I I' f s' q,
    { have A : tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q) =
             tangent_map I' I' r (tangent_map_within I I' f s' q),
      { apply tangent_map_within_eq_tangent_map,
        { apply is_open.unique_mdiff_within_at _ r.open_source, simp [hq] },
        { refine mdifferentiable_at_atlas _ (chart_mem_atlas _ _) _,
          simp only [hq] with mfld_simps } },
      have : f p.proj = (tangent_map_within I I' f s p).1 := rfl,
      rw [A],
      dsimp [r, Dr],
      rw [this, tangent_map_chart],
      { simp only [hq] with mfld_simps,
        have : tangent_map_within I I' f s' q ∈
          (chart_at (model_prod H' E') (tangent_map_within I I' f s p)).source,
            by { simp only [hq] with mfld_simps },
        exact (chart_at (model_prod H' E') (tangent_map_within I I' f s p)).left_inv this },
      { simp only [hq] with mfld_simps } },
    have E : tangent_map_within I I' f s' q = tangent_map_within I I' f s q,
    { refine tangent_map_within_subset (by mfld_set_tac) U'q _,
      apply hf.mdifferentiable_on one_le_n,
      simp only [hq] with mfld_simps },
    simp only [(∘), A, B, C, D, E.symm] },
  exact diff_DrirrflilDl.congr eq_comp,
end

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem cont_mdiff_on.continuous_on_tangent_map_within
  (hf : cont_mdiff_on I I' n f s) (hmn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (tangent_map_within I I' f s) (π (tangent_space I) ⁻¹' s) :=
begin
  have : cont_mdiff_on I.tangent I'.tangent 0 (tangent_map_within I I' f s)
         (π (tangent_space I) ⁻¹' s) :=
    hf.cont_mdiff_on_tangent_map_within hmn hs,
  exact this.continuous_on
end

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem cont_mdiff.cont_mdiff_tangent_map
  (hf : cont_mdiff I I' n f) (hmn : m + 1 ≤ n) :
  cont_mdiff I.tangent I'.tangent m (tangent_map I I' f) :=
begin
  rw ← cont_mdiff_on_univ at hf ⊢,
  convert hf.cont_mdiff_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem cont_mdiff.continuous_tangent_map
  (hf : cont_mdiff I I' n f) (hmn : 1 ≤ n) :
  continuous (tangent_map I I' f) :=
begin
  rw ← cont_mdiff_on_univ at hf,
  rw continuous_iff_continuous_on_univ,
  convert hf.continuous_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

end tangent_map

namespace tangent_bundle

include Is
variables (I M)
open bundle

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
lemma tangent_map_tangent_bundle_pure (p : tangent_bundle I M) :
  tangent_map I I.tangent (zero_section (tangent_space I)) p = ⟨⟨p.proj, 0⟩, ⟨p.2, 0⟩⟩ :=
begin
  rcases p with ⟨x, v⟩,
  have N : I.symm ⁻¹' (chart_at H x).target ∈ 𝓝 (I ((chart_at H x) x)),
  { apply is_open.mem_nhds,
    apply (local_homeomorph.open_target _).preimage I.continuous_inv_fun,
    simp only with mfld_simps },
  have A : mdifferentiable_at I I.tangent (λ x, @total_space_mk M (tangent_space I) x 0) x,
  { have : smooth I (I.prod 𝓘(𝕜, E)) (zero_section (tangent_space I : M → Type*)) :=
    bundle.smooth_zero_section 𝕜 (tangent_space I : M → Type*),
    exact this.mdifferentiable_at },
  have B : fderiv_within 𝕜 (λ (x' : E), (x', (0 : E))) (set.range ⇑I) (I ((chart_at H x) x)) v
    = (v, 0),
  { rw [fderiv_within_eq_fderiv, differentiable_at.fderiv_prod],
    { simp },
    { exact differentiable_at_id' },
    { exact differentiable_at_const _ },
    { exact model_with_corners.unique_diff_at_image I },
    { exact differentiable_at_id'.prod (differentiable_at_const _) } },
  simp only [bundle.zero_section, tangent_map, mfderiv, total_space.proj_mk, A,
    if_pos, chart_at, fiber_bundle.charted_space_chart_at, tangent_bundle.trivialization_at_apply,
    tangent_bundle_core, function.comp, continuous_linear_map.map_zero] with mfld_simps,
  rw ← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)) at B,
  rw [← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)), ← B],
  congr' 2,
  apply fderiv_within_congr _ (λ y hy, _),
  { simp only [prod.mk.inj_iff] with mfld_simps },
  { apply unique_diff_within_at.inter (I.unique_diff _ _) N,
    simp only with mfld_simps },
  { simp only with mfld_simps at hy,
    simp only [hy, prod.mk.inj_iff] with mfld_simps },
end

end tangent_bundle
