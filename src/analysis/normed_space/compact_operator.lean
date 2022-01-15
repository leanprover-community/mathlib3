import analysis.normed_space.basic
import analysis.normed_space.bounded_linear_maps


variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] -- needed in factor
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]


section

/-
We only actually need submodule.indicator_id and submodule.indicator_id.continuous_on.
This could be implemented without submodule.indicator_endo easily.
-/

open_locale classical
noncomputable def submodule.indicator (V : submodule 𝕜 E) (f : E → F) : E → F :=
λ e, if h : e ∈ V then f e else 0

noncomputable def submodule.indicator_endo (V : submodule 𝕜 E) {f : E → E}
  (hf : ∀ x ∈ V, f x ∈ V) : E → V :=
λ e, if h : e ∈ V then ⟨f e, hf _ h⟩ else 0

noncomputable def submodule.indicator_id (V : submodule 𝕜 E) : E → V :=
submodule.indicator_endo V $ λ x (hx : x ∈ V), show id x ∈ V, from hx

lemma submodule.indicator_continuous_on {V : submodule 𝕜 E} {f : E → F} (hf : continuous_on f V) :
  continuous_on (submodule.indicator V f) V :=
begin
  simp only [submodule.indicator, dite_eq_ite, continuous_on_iff_continuous_restrict,
    set.restrict, set.indicator_of_mem, subtype.coe_prop] at hf ⊢,
  convert hf using 1, ext,
  simp only [if_true, submodule.coe_mem]
end

lemma submodule.indicator_id_continuous_on (V : submodule 𝕜 E) :
  continuous_on (submodule.indicator_id V) V :=
begin
  simp only [continuous_on_iff_continuous_restrict, submodule.indicator_id, set.restrict,
    submodule.indicator_endo, dite_eq_ite, if_true, id.def, submodule.coe_mem, subtype.coe_eta],
  exact continuous_id
end

lemma set.indicator.continuous_on {α β : Type*} [topological_space α] [topological_space β]
  [has_zero β] {s : set α} {f : α → β} (hf : continuous_on f s) : continuous_on (s.indicator f) s :=
by simpa only [continuous_on_iff_continuous_restrict, set.restrict, set.indicator_of_mem,
               subtype.coe_prop] using hf

end

def compact_operator (T : E → F) : Prop :=
∀ s : set E, metric.bounded s → is_compact (closure (T '' s))


lemma image_rel_compact_of_rel_compact {f : E → F}  {s : set E} (hc : continuous_on f (closure s))
  (hs : is_compact (closure s)) : is_compact (closure (f '' s)) :=
by simpa only [← image_closure_of_compact hs hc] using is_compact.image_of_continuous_on hs hc

lemma metric.bounded_image (f : E →L[𝕜] F) {s : set E} (hs : metric.bounded s) :
  metric.bounded (f '' s) :=
begin
  rw metric.bounded at hs,
  rw [set.image_eq_range, metric.bounded_range_iff],
  rcases f.is_bounded_linear_map.bound with ⟨M, hM, hMle⟩,
  cases hs with C hC,
  refine ⟨M*C, λ x y, _⟩,
  specialize hC x y x.property y.property,
  rw dist_eq_norm at hC ⊢,
  rw ← map_sub,
  refine le_trans (hMle _) _,
  nlinarith only [hC, hM]
end

lemma compact_operator_continuous_comp_compact {E' F' : Type*} [normed_group E'] [normed_space 𝕜 E']
  [normed_group F'] [normed_space 𝕜 F'] (f : E' →L[𝕜] E) (g : F → F') (u : E →ₗ[𝕜] F)
  (hu : compact_operator u) (hg :  continuous_on g (closure (u ∘ₗ f.to_linear_map).range)) :
  compact_operator (λ x, g ((u ∘ₗ f.to_linear_map) x)) :=
begin
  intros s hs,
  have ufs_cpct : is_compact (closure (u '' (f '' s))) := hu _ (metric.bounded_image _ hs),
  have g_cts_on : continuous_on g (closure (u '' (f '' s))),
  { refine hg.mono (closure_mono (fun x hx, _)),
    simp only [set.mem_image, continuous_linear_map.to_linear_map_eq_coe, function.comp_app,
      exists_exists_and_eq_and, set_like.mem_coe, linear_map.coe_comp,
      continuous_linear_map.coe_coe, linear_map.mem_range] at hx ⊢,
    cases hx with x hx,
    exact ⟨x, hx.2⟩ },
  convert image_rel_compact_of_rel_compact g_cts_on ufs_cpct using 2,
  rw [← set.image_comp, ← set.image_comp],
  refl
end

/-- If a compact operator preserves a submodule, its restriction to that submodule is compact. -/
lemma compact_operator.restrict_invariant {T : E →ₗ[𝕜] E} (hT : compact_operator T)
  {V : submodule 𝕜 E} (hV : ∀ v ∈ V, T v ∈ V) (h_closed : is_closed (V : set E)):
  compact_operator (T.restrict hV) :=
begin
  have : continuous_on V.indicator_id (closure ↑((T.comp V.subtypeL.to_linear_map).range)),
  { have : ((T.comp V.subtypeL.to_linear_map).range : set E) ⊆ V,
    { intro x,
      simp only [forall_exists_index, continuous_linear_map.to_linear_map_eq_coe,
        submodule.subtype_apply, function.comp_app, submodule.coe_subtypeL, set_like.mem_coe,
        linear_map.coe_comp, linear_map.mem_range],
      rintros y ⟨rfl⟩,
      exact hV _ y.property, },
    refine continuous_on.mono _ (closure_mono this),
    rw h_closed.closure_eq,
    exact V.indicator_id_continuous_on },
  convert compact_operator_continuous_comp_compact (V.subtypeL) _ T hT this,
  ext v,
  have htv : T v ∈ V := hV _ v.property,
  simp only [dif_pos, continuous_linear_map.to_linear_map_eq_coe, submodule.subtype_apply,
    dif_ctx_congr, submodule.coe_mk, function.comp_app, submodule.coe_subtypeL,
    linear_map.coe_comp, htv, submodule.indicator_id, submodule.indicator_endo],
 refl
end
