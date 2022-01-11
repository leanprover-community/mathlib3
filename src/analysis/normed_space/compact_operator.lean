import analysis.normed_space.basic
import analysis.normed_space.bounded_linear_maps
.

-- the real version forces ι to be in the same universe as α
lemma is_compact_iff_finite_subcover' {α} [topological_space α] (s : set α) :
  is_compact s ↔ (Π {ι : Type*} (U : ι → (set α)), (∀ i, is_open (U i)) →
    s ⊆ (⋃ i, U i) → (∃ (t : finset ι), s ⊆ (⋃ i ∈ t, U i))) :=
sorry


variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] -- sometimes needed
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]

def compact_operator (T : E →ₗ[𝕜] F) : Prop :=
∀ s : set E, metric.bounded s → is_compact (closure (T '' s))

lemma image_compact_of_compact (f : E →L[𝕜] F) {s : set E} (hs : is_compact s) : is_compact (f '' s) :=
begin
  rw is_compact_iff_finite_subcover' at hs ⊢,
  intros ι U U_open U_sset,
  let U' : ι → set E := λ i, (f ⁻¹' (U i)) ,
  have U'_open : ∀ i, is_open (U' i) := λ i, continuous.is_open_preimage f.continuous _ (U_open _),
  have h_pre : (f ⁻¹'( ⋃ i, U i)) = (⋃ i, U' i) := set.preimage_Union,
  have U'_sset : s ⊆ ⋃ i, U' i,
  { intros t ht,
    rw [← h_pre, set.mem_preimage],
    exact U_sset (set.mem_image_of_mem f ht) },
  cases hs U' U'_open U'_sset with ι' hι',
  use ι',
  simp only [set.image_subset_iff, set.preimage_Union, hι'],
end

lemma image_rel_compact_of_rel_compact (f : E →L[𝕜] F) {s : set E} (hs : is_compact (closure s)) :
  is_compact (closure (f '' s)) :=
begin
  rw ← image_closure_of_compact hs,
  { apply image_compact_of_compact _ hs, },
  { exact f.continuous.continuous_on },
  { apply_instance }
end

lemma factor {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
             {F' : Type*} [normed_group F'] [normed_space 𝕜 F']
             (f : E' →L[𝕜] E) (g : F →L[𝕜] F') (u : E →ₗ[𝕜] F) (hu : compact_operator u) :
  compact_operator (g.to_linear_map ∘ₗ u ∘ₗ f.to_linear_map) :=
begin
  intros s hs,
  have fs_bdd : metric.bounded (f '' s), -- should exist, or be factored out. requires nondiscrete 𝕜
  { rw metric.bounded at hs,
    rw [set.image_eq_range, metric.bounded_range_iff],
    rcases f.is_bounded_linear_map.bound with ⟨M, hM, hMle⟩,
    cases hs with C hC,
    use M*C,
    intros x y,
    specialize hC x y x.property y.property,
    rw dist_eq_norm at hC ⊢,
    rw ← map_sub,
    apply le_trans (hMle _),
    nlinarith only [hC, hM] },
  have ufs_cpct := hu _ fs_bdd,
  have := image_rel_compact_of_rel_compact g ufs_cpct,
  convert this using 2,
  rw [← set.image_comp, ← set.image_comp],
  refl
end

/-- If a compact operator preserves a submodule, its restriction to that submodule is compact. -/
lemma compact_operator.restrict_invariant {T : E →ₗ[𝕜] E} (hT : compact_operator T)
  {V : submodule 𝕜 E} (hV : ∀ v ∈ V, T v ∈ V) :
  compact_operator (T.restrict hV) :=
begin
  let emb := (continuous_linear_map.id 𝕜 E).to_linear_map.comp (T.comp V.subtypeL.to_linear_map),
  have hcpct : compact_operator emb := factor (submodule.subtypeL V) (continuous_linear_map.id 𝕜 E) T hT,
  have : ∀ x, emb x ∈ V,
  { intro x,
    simp only [emb, linear_map.id_comp, continuous_linear_map.to_linear_map_eq_coe, submodule.subtype_apply, function.comp_app,
  submodule.coe_subtypeL, linear_map.coe_comp, continuous_linear_map.coe_id], apply hV _ x.property },
  let emb' := emb.cod_restrict _ this,
  sorry
end
