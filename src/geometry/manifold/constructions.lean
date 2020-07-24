/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.times_cont_mdiff

noncomputable theory

open set

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
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F' G'}
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']

section prod_mk

/- Should I generalize this to the case where f and g are smooth on different sets? It does not
seem to be the trend in the library but I think it is a good idea. -/
lemma times_cont_mdiff_on.prod_mk {f : M → M'} {g : M → N'} {n : with_top ℕ} {s : set M}
  (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on I J' n g s) :
  times_cont_mdiff_on I (I'.prod J') n (λ x, (f x, g x)) s :=
begin
  rw times_cont_mdiff_on_iff at hf hg ⊢,
  refine ⟨hf.1.prod hg.1, λ x y, _⟩,

  let s1 := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹'
  (s ∩ f ⁻¹' (ext_chart_at I' y.fst).source)),
  let t1 := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹'
  (s ∩ g ⁻¹' (ext_chart_at J' y.snd).source)),
  have h := times_cont_diff_on.prod (times_cont_diff_on.mono (hf.2 x y.fst)
  (inter_subset_left s1 t1)) (times_cont_diff_on.mono (hg.2 x y.snd) (inter_subset_right s1 t1)),
  convert h using 1,

  ext1 z,
  simp only with mfld_simps,
  fsplit,
  { rintro ⟨⟨⟨a, rfl⟩, h1⟩, h2, h3, h4⟩, exact ⟨⟨⟨⟨a, rfl⟩, h1⟩, ⟨h2, h3⟩⟩, ⟨⟨⟨a, rfl⟩, h1⟩, ⟨h2, h4⟩⟩⟩, },
  { rintro ⟨⟨⟨⟨a, rfl⟩, h1⟩, h2, h3⟩, ⟨⟨b, hb⟩, h4⟩, h5, h6⟩, exact ⟨⟨⟨a, rfl⟩, h1⟩, ⟨h2, ⟨h3, h6⟩⟩⟩, }
end

lemma times_cont_mdiff_within_at.prod_mk {f : M → M'} {g : M → N'} {s : set M} {x : M} {n : ℕ}
  (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at I J' n g s x) :
  times_cont_mdiff_within_at I (I'.prod J') n (λ x, (f x, g x)) s x :=
begin
  rw times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds at hf hg ⊢,
  rcases hg with ⟨ug, hug1, hug2⟩, rcases hf with ⟨uf, huf1, huf2⟩,
  exact ⟨ug ∩ uf, (nhds_within x (insert x s)).inter_sets hug1 huf1,
  (times_cont_mdiff_on.mono huf2 (set.inter_subset_right ug uf)).prod_mk
    (times_cont_mdiff_on.mono hug2 (set.inter_subset_left ug uf))⟩,
end

/- Not a particular case of previous lemma. -/
lemma smooth_within_at.prod_mk {f : M → M'} {g : M → N'} {s : set M} {x : M}
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at I J' g s x) :
  smooth_within_at I (I'.prod J') (λ x, (f x, g x)) s x :=
begin
  rw times_cont_mdiff_within_at_top at hf hg ⊢,
  intro n,
  exact (hf n).prod_mk (hg n),
end

lemma times_cont_mdiff.prod_mk {f : M → M'} {g : M → N'} {n : with_top ℕ}
  (hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff I J' n g) :
  times_cont_mdiff I (I'.prod J') n (λ x, (f x, g x)) :=
begin
  have h := hf.times_cont_mdiff_on.prod_mk hg.times_cont_mdiff_on,
  rw times_cont_mdiff_on_univ at h,
  exact h,
end

lemma times_cont_mdiff_at.prod_mk {f : M → M'} {g : M → N'} {n : ℕ} {x : M}
  (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at I J' n g x) :
  times_cont_mdiff_at I (I'.prod J') n (λ x, (f x, g x)) x :=
begin
  rw times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds at hf hg ⊢,
  rcases hg with ⟨ug, hug1, hug2⟩, rcases hf with ⟨uf, huf1, huf2⟩,
  refine ⟨uf ∩ ug, (nhds x).inter_sets huf1 hug1,
  (huf2.mono (inter_subset_left uf ug)).prod_mk (hug2.mono (inter_subset_right uf ug))⟩,
end

/- Not a particular case of previous lemma. -/
lemma smooth_at.prod_mk {f : M → M'} {g : M → N'} {x : M}
  (hf : smooth_at I I' f x) (hg : smooth_at I J' g x) :
  smooth_at I (I'.prod J') (λ x, (f x, g x)) x :=
begin
  rw times_cont_mdiff_at_top at hf hg ⊢,
  intro n,
  exact (hf n).prod_mk (hg n),
end

end prod_mk

section prod_map

variables {f : M → M'} {g : N → N'} {s : set M} {t : set N} {x : M} {y : N}

lemma times_cont_mdiff_on.prod_map {n : with_top ℕ}
  (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on J J' n g t) :
  times_cont_mdiff_on (I.prod J) (I'.prod J') n (prod.map f g) (s.prod t) :=
begin
  rw times_cont_mdiff_on_iff at hf hg ⊢,
  refine ⟨hf.1.prod_map hg.1, λ x y, _⟩,
  convert (hf.2 x.1 y.1).prod_map (hg.2 x.2 y.2) using 1,
  mfld_set_tac,
end

lemma times_cont_mdiff_within_at.prod_map {n : ℕ}
  (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at J J' n g t y) :
  times_cont_mdiff_within_at (I.prod J) (I'.prod J') n (prod.map f g) (s.prod t) (x, y) :=
begin
  rw times_cont_mdiff_within_at_iff at *,
  refine ⟨hf.1.prod_map hg.1, _⟩,
  convert hf.2.prod_map hg.2 using 1,
  mfld_set_tac,
end

lemma smooth_within_at.prod_map
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at J J' g t y) :
  smooth_within_at (I.prod J) (I'.prod J') (prod.map f g) (s.prod t) (x, y) :=
begin
  rw times_cont_mdiff_within_at_top at hf hg ⊢,
  intro n,
  exact (hf n).prod_map (hg n),
end

lemma times_cont_mdiff.prod_map {n : with_top ℕ}
(hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff J J' n g) :
  times_cont_mdiff (I.prod J) (I'.prod J') n (prod.map f g) :=
begin
  rw ←times_cont_mdiff_on_univ at hf hg ⊢,
  have h := hf.prod_map hg, rw univ_prod_univ at h,
  exact h,
end

lemma times_cont_mdiff_at.prod_map {n : ℕ}
  (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at J J' n g y) :
  times_cont_mdiff_at (I.prod J) (I'.prod J') n (prod.map f g) (x, y) :=
begin
  rw times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds at hf hg ⊢,
  rcases hg with ⟨ug, hug1, hug2⟩, rcases hf with ⟨uf, huf1, huf2⟩,
  refine ⟨uf.prod ug, prod_mem_nhds_sets huf1 hug1, huf2.prod_map hug2⟩,
end

lemma smooth_at.prod_map
  (hf : smooth_at I I' f x) (hg : smooth_at J J' g y) :
  smooth_at (I.prod J) (I'.prod J') (prod.map f g) (x, y) :=
by {rw times_cont_mdiff_at_top at hf hg ⊢, intro n, exact (hf n).prod_map (hg n) }

end prod_map

section projections

lemma smooth_fst : smooth (I.prod J) I (@prod.fst M N) :=
begin
  rw smooth_iff,
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
  rw smooth_iff,
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

lemma smooth_iff_proj_smooth {f : M → M' × N'} :
  (smooth I (I'.prod J') f) ↔ (smooth I I' (prod.fst ∘ f)) ∧ (smooth I J' (prod.snd ∘ f)) :=
begin
  split,
  { intro h, exact ⟨smooth_fst.comp h, smooth_snd.comp h⟩ },
  { rintro ⟨h_fst, h_snd⟩,
    have h := h_fst.prod_mk h_snd,
    simp only [prod.mk.eta] at h,
    exact h, }
end

end projections
