import geometry.manifold.times_cont_mdiff

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

lemma smooth_id : smooth I I (id : M → M) :=
begin
  refine ⟨continuous_id, λ x y, _⟩,
  rw [function.comp.left_id, set.preimage_id],
  unfold ext_chart_at,
  simp only [model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm, local_homeomorph.coe_coe,
    local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe],
  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ I) (chart_mem_atlas H x) (chart_mem_atlas H y)).1,
  simp only [local_homeomorph.trans_to_local_equiv, local_homeomorph.coe_trans, local_homeomorph.symm_to_local_equiv] at h1,
  convert h1 using 1,
  unfold function.comp,
  ext1 z,
  rw set.mem_inter_eq,
  fsplit;
  simp only [local_equiv.trans_source, local_equiv.trans_target, and_imp, model_with_corners.to_local_equiv_coe_symm,
    set.mem_preimage, set.mem_range, local_homeomorph.coe_coe_symm, set.mem_inter_eq, local_equiv.symm_source,
    set.preimage_univ, model_with_corners.target, model_with_corners.source_eq, exists_imp_distrib, set.inter_univ],
  { intros w hw h2 h3, exact ⟨⟨h2, h3⟩, ⟨w, hw⟩⟩, },
  { intros h2 h3 w hw, use w, exacts [hw, h2, h3], }
end

lemma smooth_const {x' : M'} : smooth I I' (λ x : M, x') :=
by { refine ⟨continuous_const, λ x y, _⟩, unfold function.comp, exact times_cont_diff_on_const, }

section composition

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']

lemma smooth_on.comp {s : set M} {t : set M'} {f : M → M'} {g : M' → M''}
  (hg : smooth_on I' I'' g t) (hf : smooth_on I I' f s)
  (st : s ⊆ f ⁻¹' t) : smooth_on I I'' (g ∘ f) s :=
times_cont_mdiff_on.comp hg hf st

lemma times_cont_mdiff.comp {n : with_top ℕ} {f : M → M'} {g : M' → M''}
  (hg : times_cont_mdiff I' I'' n g) (hf : times_cont_mdiff I I' n f) :
  times_cont_mdiff I I'' n (g ∘ f) :=
begin
  have hs : (set.univ ⊆ f ⁻¹' set.univ), by rw set.preimage_univ,
  have h := (times_cont_mdiff_on_univ.2 hg).comp (times_cont_mdiff_on_univ.2 hf) hs,
  exact times_cont_mdiff_on_univ.1 h,
end

lemma smooth.comp {f : M → M'} {g : M' → M''}
  (hg : smooth I' I'' g) (hf : smooth I I' f) :
  smooth I I'' (g ∘ f) := by exact times_cont_mdiff.comp hg hf

end composition

lemma tangent_bundle_proj_smooth : smooth I.tangent I (tangent_bundle.proj I M) :=
begin
  refine ⟨tangent_bundle_proj_continuous I M, λ x y, _⟩,
  simp only [function.comp] with mfld_simps,
  sorry,
end

section prod_maps

variables
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F' G'}
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']

lemma smooth.prod_map {f : M → M'} {g : N → N'} (hf : smooth I I' f) (hg : smooth J J' g) :
  smooth (I.prod J) (I'.prod J') (prod.map f g) :=
begin
  cases hf with f_cont f_smooth,
  cases hg with g_cont g_smooth,
  refine ⟨continuous.prod_map f_cont g_cont, λ x y, _⟩,
  simp only [function.comp, ext_chart_at, prod.map, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe],
  have f_smooth_at := f_smooth x.fst y.fst,
  have g_smooth_at := g_smooth x.snd y.snd,
  clear f_smooth g_smooth,
  have h := f_smooth_at.map_prod g_smooth_at,
  clear f_smooth_at g_smooth_at,
  simp only [function.comp, ext_chart_at, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe] at h,
  convert h using 1,
  clear h,

  ext1 z,
  simp only [local_equiv.trans_source, local_equiv.trans_target, model_with_corners.to_local_equiv_coe_symm, set.mem_preimage,
    set.mem_range, set.mem_inter_eq, set.mem_prod,
    set.preimage_univ, model_with_corners.target, model_with_corners.source_eq, prod.map_mk, prod.exists, set.inter_univ],
  split,
  { rintro ⟨⟨⟨⟨a, b⟩, rfl⟩, h1, h2⟩, h3, h4⟩,
    rw prod.map_fst at h3,
    rw prod.map_snd at h4,
    exact ⟨⟨⟨⟨a, rfl⟩, h1⟩, h3⟩, ⟨⟨b, rfl⟩, h2⟩, h4⟩, },
  { rintro ⟨⟨⟨⟨h, hh⟩, h2⟩, h3⟩, ⟨⟨⟨g, hg⟩, h5⟩, h6⟩⟩,
    sorry,
    /-refine ⟨⟨⟨h, g, _⟩, ⟨h2, h5⟩⟩, ⟨h3, h6⟩⟩,
    { ext, exacts [hh, hg], }-/ }
end

lemma smooth_fst : smooth (I.prod J) I (@prod.fst M N) :=
begin
  refine ⟨continuous_fst, λ x y, _⟩,

  simp only [function.comp, ext_chart_at, prod.map, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm,
    model_with_corners.to_local_equiv_coe],
  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ (I.prod J)) (chart_mem_atlas (H×G) x) (chart_mem_atlas (H×G) (y, x.snd))).1,
  let s := (prod.map (I.symm) (J.symm) ⁻¹'
    ((chart_at (model_prod H G) x).to_local_equiv.symm.trans (chart_at (model_prod H G) (y, x.snd)).to_local_equiv).source ∩ set.range (prod.map I J)),
  have hs : (s ⊆ (λ (x_1 : E × F), (I ((chart_at (model_prod H G) (y, x.snd)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).fst,
    J ((chart_at (model_prod H G) (y, x.snd)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).snd)) ⁻¹' (set.univ)) :=
  begin
    simp only [set.subset_univ, set.preimage_univ],
  end,
  have h2 := times_cont_diff_on.comp (times_cont_diff.times_cont_diff_on times_cont_diff_fst) h1 hs,
  simp only [function.comp, prod.map, model_with_corners_prod_coe_symm, local_homeomorph.trans_to_local_equiv,
    local_homeomorph.coe_trans, model_with_corners_prod_coe, local_homeomorph.symm_to_local_equiv] at h2,
  convert h2 using 1,
  clear h1 hs h2,

  ext1 z,
  simp only [prod.map, set.mem_preimage, set.mem_range, set.mem_inter_eq, prod.exists],
  fsplit,
  { rintro ⟨⟨⟨⟨a, h_a⟩, b, h_b⟩, h1, h2⟩, h3, h4⟩,
    simp only [model_with_corners.to_local_equiv_coe_symm, model_with_corners_prod_coe_symm, prod.map_fst] at h1 h2,
    rw local_equiv.symm_target at h3,
    simp only [set.mem_univ, set.preimage_univ, model_with_corners.source_eq] at h4,
    cases z,
    simp only [prod.map_mk] at h_a h_b h1 h2 h3,
    refine ⟨⟨⟨h1, h2⟩, _⟩, _⟩,
    { simp only [set.mem_preimage, local_homeomorph.coe_coe_symm, local_equiv.symm_symm, prod.map_mk],
      refine ⟨h3, _⟩,
      apply local_homeomorph.map_target, /- WHY DID NOT SIMP DO IT BY ITSELF? IT TOOK ME TWO DAYS-/
      exact h2, },
    { use [a, b], ext1, exacts [h_a, h_b], } },
  { rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, w, g, rfl⟩,
    repeat {rw model_with_corners.left_inv at h1 h2},
    simp only [local_homeomorph.coe_coe_symm, local_equiv.symm_symm, model_with_corners.left_inv] at h3 h4,
    refine ⟨⟨_, _⟩,_⟩,
    { /-use [w.1, g],-/ sorry, },
    { simp only [model_with_corners.to_local_equiv_coe_symm, set.mem_preimage, model_with_corners_prod_coe_symm,
        model_with_corners.left_inv, prod.map_mk],
      exact ⟨h1, h2⟩, },
    { simp only [local_equiv.trans_source, local_homeomorph.prod_coe, local_homeomorph.prod_symm, prod_charted_space_chart_at,
 model_with_corners_prod_coe_symm, set.preimage_univ, model_with_corners.left_inv, model_with_corners.source_eq,
 prod.map_mk, set.inter_univ],
      exact h3, } }
end

lemma smooth_snd : smooth (I.prod J) J (@prod.snd M N) :=
begin
  refine ⟨continuous_snd, λ x y, _⟩,

  simp only [function.comp, ext_chart_at, prod.map, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, model_with_corners_prod_coe_symm, local_equiv.coe_trans, local_equiv.coe_trans_symm,
    model_with_corners.to_local_equiv_coe],
  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ (I.prod J)) (chart_mem_atlas (H×G) x) (chart_mem_atlas (H×G) (x.fst, y))).1,
  let s := (prod.map (I.symm) (J.symm) ⁻¹'
    ((chart_at (model_prod H G) x).to_local_equiv.symm.trans (chart_at (model_prod H G) (x.fst, y)).to_local_equiv).source ∩
  set.range (prod.map I J)),
  have hs : (s ⊆ (λ (x_1 : E × F), (I ((chart_at (model_prod H G) (x.fst, y)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).fst,
    J ((chart_at (model_prod H G) (x.fst, y)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).snd)) ⁻¹' (set.univ)) :=
  by simp only [set.subset_univ, set.preimage_univ],
  have h2 := times_cont_diff_on.comp (times_cont_diff.times_cont_diff_on times_cont_diff_snd) h1 hs,
  simp only [function.comp, prod.map, model_with_corners_prod_coe_symm, local_homeomorph.trans_to_local_equiv,
    local_homeomorph.coe_trans, model_with_corners_prod_coe, local_homeomorph.symm_to_local_equiv] at h2,
  convert h2 using 1,
  clear h1 hs h2,

  ext1 z,
  simp only [prod.map, set.mem_preimage, set.mem_range, set.mem_inter_eq, prod.exists],
  split,
  { rintro ⟨⟨⟨⟨a, h_a⟩, b, h_b⟩, h1, h2⟩, h3, h4⟩,
    simp only [model_with_corners.to_local_equiv_coe_symm, model_with_corners_prod_coe_symm, prod.map_fst] at h1 h2,
    rw local_equiv.symm_target at h3,
    simp only [set.mem_univ, set.preimage_univ, model_with_corners.source_eq] at h4,
    cases z,
    simp only [prod.map_mk] at h_a h_b h1 h2 h3,
    refine ⟨⟨⟨h1, h2⟩, ⟨_, h3⟩⟩, _⟩,
    { simp only [local_homeomorph.coe_coe_symm, local_equiv.symm_symm, prod.map_mk],
      apply local_homeomorph.map_target,
      exact h1, },
    { use [a, b], ext1, exacts [h_a, h_b], } },
  { rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, w, g, rfl⟩,
    repeat {rw model_with_corners.left_inv at h1 h2},
    simp only [local_homeomorph.coe_coe_symm, local_equiv.symm_symm, model_with_corners.left_inv] at h3 h4,
    sorry,
    /-refine ⟨⟨⟨⟨w, rfl⟩, ⟨g, rfl⟩⟩, _⟩, _⟩,
    { simp only [model_with_corners.to_local_equiv_coe_symm, set.mem_preimage, model_with_corners_prod_coe_symm,
        model_with_corners.left_inv, prod.map_mk],
        exact ⟨h1, h2⟩, },
    { cases x,
      simp only [model_with_corners.left_inv],
      refine ⟨h4, _⟩,
      simp only [model_with_corners.source_eq], }-/ }
end

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']

lemma smooth.prod_mk {f : M → M'} {g : M → N'} (hf : smooth I I' f) (hg : smooth I J' g) :
  smooth I (I'.prod J') (λx, (f x, g x)) :=
begin
  cases hf with f_cont f_smooth,
  cases hg with g_cont g_smooth,
  refine ⟨continuous.prod_mk f_cont g_cont, λ x y, _⟩,

  simp only [function.comp, model_with_corners_prod_to_local_equiv] with mfld_simps,
  let s := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹' (f ⁻¹' (ext_chart_at I' y.fst).source)),
  let t := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹' (g ⁻¹' (ext_chart_at J' y.snd).source)),
  let inter := s ∩ t,
  have hs : (inter ⊆ s) := by exact set.inter_subset_left s t,
  have ht : (inter ⊆ t) := by exact set.inter_subset_right s t,
  have f_smooth_at := times_cont_diff_on.mono (f_smooth x y.fst) hs,
  have g_smooth_at := times_cont_diff_on.mono (g_smooth x y.snd) ht,
  clear f_smooth g_smooth,
  have h := times_cont_diff_on.prod f_smooth_at g_smooth_at,
  clear f_smooth_at g_smooth_at,
  simp only [function.comp, ext_chart_at, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe] at h,

  convert h using 1,
  clear h,
  /- Why does unfold s not work? I don't want to use change. -/
  simp only [inter, s, t, function.comp] with mfld_simps,

  ext1 z,
  fsplit,
  { rintro ⟨⟨⟨w, rfl⟩, h1⟩, h2, h3⟩, exact ⟨⟨⟨⟨w, rfl⟩, h1⟩, h2⟩, ⟨⟨w, rfl⟩, h1⟩, h3⟩, },
  { rintro ⟨⟨⟨⟨w, rfl⟩, h1⟩, h2⟩, ⟨⟨v, h_v⟩, h3⟩, h4⟩, refine ⟨⟨⟨w, rfl⟩, h1⟩, h2, h4⟩, }
end

lemma smooth_iff_proj_smooth {f : M → M' × N'} :
  (smooth I (I'.prod J') f) ↔ (smooth I I' (prod.fst ∘ f)) ∧ (smooth I J' (prod.snd ∘ f)) :=
begin
  split,
  { intro h, exact ⟨smooth.comp smooth_fst h, smooth.comp smooth_snd h⟩ },
  { rintro ⟨h_fst, h_snd⟩,
    have h := smooth.prod_mk h_fst h_snd,
    simp only [prod.mk.eta] at h, /- What is simp doing? I would like to find a way to replace it. -/
    exact h, }
end

end prod_maps
