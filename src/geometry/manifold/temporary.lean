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

  def regular_point.chart [I.boundaryless] {f : M → N} {q : N} (h1 : smooth I J f)
  (h2 : regular_value I J f q)
  (p : f⁻¹' {q}) : local_homeomorph (f⁻¹' {q}) (regular_point.F' I J f p).ker :=
{
  to_fun := λ s, ((h2 p).straighted_chart h1.smooth_at s).2,
  inv_fun := λ s, ⟨((h2 p).straighted_chart h1.smooth_at).symm ((ext_chart_at J q) q, s),
    begin
      simp only [model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm, mem_singleton_iff,
        regular_point.pre_chart, local_homeomorph.coe_coe, comp_app, mem_preimage, written_in_ext_chart_at,
        local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe],

    end⟩,
}

lemma times_cont_mdiff_at_iff :
  times_cont_mdiff_at I I' n f x ↔ continuous_at f x ∧
    times_cont_diff_at 𝕜 n ((ext_chart_at I' (f x)) ∘ f ∘ (ext_chart_at I x).symm)
    (ext_chart_at I x x) :=
begin
  rw [←times_cont_mdiff_within_at_univ, ←continuous_within_at_univ, ←times_cont_diff_within_at_univ,
    times_cont_mdiff_within_at_iff, and.congr_right_iff],
  refine λ h, ⟨_, times_cont_diff_at.times_cont_diff_within_at⟩,
  intro hh,
  refine hh.times_cont_diff_at _,
  simp only [preimage_univ, model_with_corners.to_local_equiv_coe_symm, local_equiv.trans_source, ext_chart_at,
  local_homeomorph.coe_coe_symm, local_homeomorph.coe_coe, model_with_corners.target_eq, inter_mem_iff, inter_univ,
  comp_app, local_equiv.coe_trans, local_equiv.trans_target, model_with_corners.source_eq, local_equiv.coe_trans_symm,
  model_with_corners.to_local_equiv_coe, univ_inter],
end
