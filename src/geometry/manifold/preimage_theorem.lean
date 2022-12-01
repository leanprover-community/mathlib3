/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import analysis.calculus.implicit
import geometry.manifold.times_cont_mdiff

noncomputable theory

open function classical set

local attribute [instance] prop_decidable

variables {𝕜 : Type*} [is_R_or_C 𝕜] -- to have that smooth implies strictly differentiable
{E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E] -- do we really need this?
{F : Type*} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F] -- do we really need this?
{H : Type*} [topological_space H]
{G : Type*} [topological_space G]
(I : model_with_corners 𝕜 E H)
(J : model_with_corners 𝕜 F G)

variables {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]

@[reducible] def regular_point (f : M → N) (p : M) := (mfderiv I J f p).range = ⊤

@[reducible] def regular_value (f : M → N) (q : N) := ∀ p : f⁻¹' {q}, regular_point I J f p

@[reducible] def regular_point.F' (f : M → N) (p : M) : E →L[𝕜] F :=
(fderiv 𝕜 (written_in_ext_chart_at I J p f) ((ext_chart_at I p) p))

variables {I J}

lemma smooth_at.has_strict_fderiv_at [I.boundaryless] {f : M → N} {p : M} (h : smooth_at I J f p) :
  has_strict_fderiv_at (written_in_ext_chart_at I J p f) (fderiv 𝕜 (written_in_ext_chart_at I J p f)
  ((ext_chart_at I p) p)) ((ext_chart_at I p) p) :=
sorry -- missing boundaryless API

lemma regular_point.written_in_ext_chart_at_range_univ [I.boundaryless] {f : M → N} {p : M}
  (hf : mdifferentiable_at I J f p) (h : regular_point I J f p) :
  (fderiv 𝕜 (written_in_ext_chart_at I J p f) ((ext_chart_at I p) p)).range = ⊤ :=
begin
  rw [←mfderiv_eq_fderiv, written_in_ext_chart_at],
  sorry -- missing boundaryless API
end

@[simp, reducible] def regular_point.pre_chart [I.boundaryless] {f : M → N} {p : M}
  (h1 : smooth_at I J f p) (h2 : regular_point I J f p) :
  local_homeomorph E (F × _) :=
(h1.has_strict_fderiv_at).implicit_to_local_homeomorph (written_in_ext_chart_at I J p f) _
  (h2.written_in_ext_chart_at_range_univ (h1.mdifferentiable_at le_top))

@[simp, reducible] def regular_point.straighted_chart [I.boundaryless] {f : M → N} {p : M}
  (h1 : smooth_at I J f p) (h2 : regular_point I J f p) :
  local_equiv M (F × _) :=
(ext_chart_at I p).trans (h2.pre_chart h1.smooth_at).to_local_equiv

lemma regular_point.straighten_preimage [I.boundaryless] {f : M → N} {p : M}
  (h1 : smooth_at I J f p)
  (h2 : regular_point I J f p) {v : F} {k : (regular_point.F' I J f p).ker}
  (hv : (v, k) ∈ (h2.straighted_chart h1.smooth_at).target) :
  ((ext_chart_at J (f p)) ∘ f ∘ (h2.straighted_chart h1.smooth_at).symm) (v, k) = v :=
begin
  simp only [local_homeomorph.coe_coe_symm, local_equiv.coe_trans_symm],
  rw [←comp.assoc, ←comp.assoc, comp.assoc _ f (ext_chart_at I p).symm, ←written_in_ext_chart_at,
    comp_app, (h1.has_strict_fderiv_at.implicit_to_local_homeomorph_right_inv
    (h2.written_in_ext_chart_at_range_univ (h1.mdifferentiable_at le_top)) hv.1)],
end

lemma regular_point.straighten_preimage' [I.boundaryless] {f : M → N} {p : M}
  (h1 : smooth_at I J f p)
  (h2 : regular_point I J f p) {q : N} {k : (regular_point.F' I J f p).ker}
  (hq1 : ((ext_chart_at J (f p)) q, k) ∈ (regular_point.straighted_chart h1 h2).target)
  (hq2 : (f (((regular_point.straighted_chart h1 h2).symm) ((ext_chart_at J (f p)) q, k))) ∈
    (ext_chart_at J (f p)).source)
  (hq3 : q ∈ (ext_chart_at J (f p)).source) : --probably hq1 → hq2 ∧ hq3
  (f ∘ (h2.straighted_chart h1.smooth_at).symm) ((ext_chart_at J (f p)) q, k) = q :=
(ext_chart_at J (f p)).inj_on hq2 hq3 (h2.straighten_preimage h1 hq1)
