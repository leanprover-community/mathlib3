/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.times_cont_mdiff

noncomputable theory

/-!
This file proves smoothness of standard maps arising from standard constructions on smooth
manifolds.
-/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']

lemma smooth_id : smooth I I (id : M → M) := times_cont_mdiff_id

lemma smooth_const {x' : M'} : smooth I I' (λ x : M, x') := times_cont_mdiff_const

section composition

/- I am copying the structure of continuous_on file, because since most concepts in geometry have
a topological counterpart with the same proof, I like the idea that people do not need to think
to different processes to prove things, and can just replace continuous with smooth. -/

lemma smooth_on.comp {s : set M} {t : set M'} {f : M → M'} {g : M' → M''}
  (hg : smooth_on I' I'' g t) (hf : smooth_on I I' f s)
  (st : s ⊆ f ⁻¹' t) : smooth_on I I'' (g ∘ f) s := times_cont_mdiff_on.comp hg hf st

lemma smooth.comp {f : M → M'} {g : M' → M''}
  (hg : smooth I' I'' g) (hf : smooth I I' f) :
  smooth I I'' (g ∘ f) := times_cont_mdiff.comp hg hf

lemma smooth.smooth_on {f : M → M'} {s : set M} (h : smooth I I' f) :
  smooth_on I I' f s :=
begin
  delta smooth at h,
  rw ← times_cont_mdiff_on_univ at h,
  exact h.mono (set.subset_univ _)
end

lemma smooth.comp_smooth_on {f : M → M'} {g : M' → M''} {s : set M}
  (hg : smooth I' I'' g) (hf : smooth_on I I' f s) :
  smooth_on I I'' (g ∘ f) s :=
hg.smooth_on.comp hf set.subset_preimage_univ

end composition

lemma smooth_within_at.prod {f : M → M'} {g : M → M''} {s : set M} {x : M}
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at I I'' g s x) :
  smooth_within_at I (I'.prod I'') (λx, (f x, g x)) s x := sorry

lemma smooth_on.prod {f : M → M'} {g : M → M''} {s : set M}
  (hf : smooth_on I I' f s) (hg : smooth_on I I'' g s) :
  smooth_on I (I'.prod I'') (λx, (f x, g x)) s :=
λ x hx, smooth_within_at.prod (hf x hx) (hg x hx)

/- I do not know enough of Sebastien's tangent bundle to do this proof and in any case I am
building my own tangent bundle but I'd be happy if this proof were there. -/
lemma tangent_bundle_proj_smooth : smooth I.tangent I (tangent_bundle.proj I M) :=
begin
  delta smooth,
  rw times_cont_mdiff_iff,
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
  delta smooth at hf hg ⊢,
  rw times_cont_mdiff_iff at hf hg ⊢,
  refine ⟨continuous.prod_map hf.1 hg.1, λ x y, _⟩,

  have h := (hf.2 x.fst y.fst).map_prod (hg.2 x.snd y.snd),
  simp only with mfld_simps at h,
  convert h using 1,

  ext1 z,
  simp only [set.mem_range, prod.map_mk] with mfld_simps,
  fsplit; { rintro ⟨⟨h1, h2⟩, h3, h4⟩, refine ⟨⟨h1, h3⟩, h2, h4⟩, }
end

lemma smooth_fst : smooth (I.prod J) I (@prod.fst M N) :=
begin
  delta smooth,
  rw times_cont_mdiff_iff,
  refine ⟨continuous_fst, λ x y, _⟩,

  /- I am copying stuff fromt the goal because I do not want to bother spending time to find
  shorter names, but I'd be happy to have tips on how to find shorter names. -/
  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ (I.prod J))
    (chart_mem_atlas (H×G) x) (chart_mem_atlas (H×G) (y, x.snd))).1,
  let s := (prod.map (I.symm) (J.symm) ⁻¹'
    ((chart_at (model_prod H G) x).to_local_equiv.symm.trans
    (chart_at (model_prod H G) (y, x.snd)).to_local_equiv).source ∩ set.range (prod.map I J)),
  have hs : (s ⊆ (λ (x_1 : E × F), (I ((chart_at (model_prod H G) (y, x.snd))
    (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).fst,
    J ((chart_at (model_prod H G) (y, x.snd)) (((chart_at (model_prod H G) x).symm)
    ((I.symm) x_1.fst, (J.symm) x_1.snd))).snd)) ⁻¹' (set.univ)) :=
  by simp only [set.subset_univ, set.preimage_univ],
  have h2 := times_cont_diff_on.comp (times_cont_diff.times_cont_diff_on times_cont_diff_fst) h1 hs,
  convert h2 using 1,
  clear h1 hs h2,

  ext1 z,
  simp only [set.mem_range, prod_map] with mfld_simps,
  fsplit,
  { rintro ⟨⟨⟨⟨a, ha⟩, h1⟩, ⟨b, hb⟩, h2⟩, h3⟩, refine ⟨⟨⟨h1, h3⟩, ⟨h2, _⟩⟩, ⟨a, b⟩, _⟩,
    { apply local_homeomorph.map_target, /- simp is not working here!!! Why? -/
      exact h2, },
    { ext, exacts [ha, hb], } },
  { rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨a, b⟩, rfl⟩, refine ⟨⟨⟨⟨a, rfl⟩, h1⟩, ⟨⟨b, rfl⟩, h3⟩⟩, h2⟩, }
end

lemma smooth_snd : smooth (I.prod J) J (@prod.snd M N) :=
begin
  delta smooth,
  rw times_cont_mdiff_iff,
  refine ⟨continuous_snd, λ x y, _⟩,

  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ (I.prod J))
  (chart_mem_atlas (H×G) x) (chart_mem_atlas (H×G) (x.fst, y))).1,
  let s := (prod.map (I.symm) (J.symm) ⁻¹'
    ((chart_at (model_prod H G) x).to_local_equiv.symm.trans
    (chart_at (model_prod H G) (x.fst, y)).to_local_equiv).source ∩  set.range (prod.map I J)),
  have hs : (s ⊆ (λ (x_1 : E × F), (I ((chart_at (model_prod H G) (x.fst, y))
  (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).fst,
    J ((chart_at (model_prod H G) (x.fst, y)) (((chart_at (model_prod H G) x).symm)
    ((I.symm) x_1.fst, (J.symm) x_1.snd))).snd)) ⁻¹' (set.univ)) :=
  by simp only [set.subset_univ, set.preimage_univ],
  have h2 := times_cont_diff_on.comp (times_cont_diff.times_cont_diff_on times_cont_diff_snd) h1 hs,
  convert h2 using 1,
  clear h1 hs h2,

  ext1 z,
  simp only [set.mem_range, prod_map] with mfld_simps,
  fsplit,
  { rintro ⟨⟨⟨⟨a, ha⟩, h1⟩, ⟨b, hb⟩, h2⟩, h3⟩, refine ⟨⟨⟨h1, _⟩, ⟨h2, h3⟩⟩, _⟩,
    { apply local_homeomorph.map_target, exact h1, },
    { use ⟨a, b⟩, ext, exacts [ha, hb], } },
  { rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨a, b⟩, rfl⟩, exact ⟨⟨⟨⟨a, rfl⟩, h1⟩, ⟨⟨b, rfl⟩, h3⟩⟩, h4⟩, }
end

lemma smooth.prod_mk {f : M → M'} {g : M → N'} (hf : smooth I I' f) (hg : smooth I J' g) :
  smooth I (I'.prod J') (λx, (f x, g x)) :=
begin
  delta smooth at hf hg ⊢,
  rw times_cont_mdiff_iff at hf hg ⊢,
  refine ⟨continuous.prod_mk hf.1 hg.1, λ x y, _⟩,

  let s := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹'
  (f ⁻¹' (ext_chart_at I' y.fst).source)),
  let t := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹'
  (g ⁻¹' (ext_chart_at J' y.snd).source)),
  let inter := s ∩ t,
  have hs : (inter ⊆ s) := by exact set.inter_subset_left s t,
  have ht : (inter ⊆ t) := by exact set.inter_subset_right s t,
  have h := times_cont_diff_on.prod (times_cont_diff_on.mono (hf.2 x y.fst) hs)
  (times_cont_diff_on.mono (hg.2 x y.snd) ht),
  convert h using 1,

  ext1 z,
  simp only with mfld_simps,
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
