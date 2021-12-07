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

/-lemma unique_diff_on.submodule (V : submodule 𝕜 E) (s : set E) (h : unique_diff_on 𝕜 s) :
  unique_diff_on 𝕜 (coe ⁻¹' s : set V) := λ v hv,
{ dense_tangent_cone := ,
  mem_closure := begin

  end,
}

def model_with_corners.submodel (I : model_with_corners 𝕜 E H) (S : submodule 𝕜 E) (r₀ : I ⁻¹' S) :
  model_with_corners 𝕜 S (I ⁻¹' S) :=
{ to_fun := λ r, ⟨I r, r.prop⟩,
  inv_fun := λ s, if h : ↑s ∈ range I then -- unknown identifier 'range'
      ⟨I.symm s, begin simp only [mem_preimage, model_with_corners.right_inv I h], exact s.prop end⟩
    else r₀,
  source := univ,
  target := coe ⁻¹' I.target,
  map_source' := λ x h, by simp only [mem_range_self, model_with_corners.target_eq, mem_preimage,
    submodule.coe_mk],
  map_target' := λ x h, mem_univ _,
  left_inv' := λ x h, by simp only [dite_eq_ite, if_true, mem_range, submodule.coe_mk,
    model_with_corners.left_inv, subtype.coe_eta, exists_apply_eq_apply],
  right_inv' := λ x h, begin sorry end,
  source_eq := rfl,
  continuous_inv_fun := begin simp only [dite_eq_ite, mem_range_self, model_with_corners.right_inv,
      if_true, model_with_corners.target_eq, mem_range, mem_univ, submodule.coe_mk, mem_preimage,
      model_with_corners.left_inv, subtype.coe_eta, exists_apply_eq_apply],

    end,
  unique_diff' := I.unique_diff'.submodule, }-/

variables {I J}

lemma smooth_at.times_cont_diff_at {f : M → N} {p : M} (h : smooth_at I J f p) :
  times_cont_diff_at 𝕜 ⊤ (written_in_ext_chart_at I J p f) ((ext_chart_at I p) p) := sorry

lemma regular_point.written_in_ext_chart_at {f : M → N} {p : M} (h : regular_point I J f p) :
  (fderiv 𝕜 (written_in_ext_chart_at I J p f) ((ext_chart_at I p) p)).range = ⊤ := sorry

@[simp, reducible] def regular_point.pre_chart {f : M → N} {p : M} (h1 : smooth_at I J f p)
  (h2 : regular_point I J f p) : local_homeomorph E (F × _) :=
(h1.times_cont_diff_at.has_strict_fderiv_at le_top).implicit_to_local_homeomorph
  (written_in_ext_chart_at I J p f) _ h2.written_in_ext_chart_at

@[simp, reducible] def regular_point.straighted_chart {f : M → N} {p : M} (h1 : smooth_at I J f p)
  (h2 : regular_point I J f p) : local_equiv M (F × _) :=
(ext_chart_at I p).trans (h2.pre_chart h1.smooth_at).to_local_equiv

lemma regular_point.straighten_preimage {f : M → N} {p : M} (h1 : smooth_at I J f p)
  (h2 : regular_point I J f p) (v : F) (k : (regular_point.F' I J f p).ker)
  (hv : (v, k) ∈ (h2.straighted_chart h1.smooth_at).target) :
  ((ext_chart_at J (f p)) ∘ f ∘ (h2.straighted_chart h1.smooth_at).symm) (v, k) = v :=
begin
  simp only [model_with_corners.to_local_equiv_coe_symm, ext_chart_at, local_homeomorph.coe_coe_symm, regular_point.pre_chart,
  local_homeomorph.coe_coe, comp_app, written_in_ext_chart_at, local_equiv.coe_trans, local_equiv.coe_trans_symm,
  model_with_corners.to_local_equiv_coe],

end

def regular_point.chart [I.boundaryless] {f : M → N} {q : N} (h1 : smooth I J f)
  (h2 : regular_value I J f q)
  (p : f⁻¹' {q}) : local_homeomorph (f⁻¹' {q}) (regular_point.F' I J f p).ker :=
{
  to_fun := λ s, ((h2 p).straighted_chart h1.smooth_at s).2,
  inv_fun := λ s, ⟨((h2 p).straighted_chart h1.smooth_at).symm ((ext_chart_at J q) q, s),
    begin
      simp only [model_with_corners.to_local_equiv_coe_symm, ext_chart_at, local_homeomorph.coe_coe_symm, mem_singleton_iff,
  regular_point.pre_chart, local_homeomorph.coe_coe, comp_app, mem_preimage, written_in_ext_chart_at,
  local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe],

    end⟩,
}
