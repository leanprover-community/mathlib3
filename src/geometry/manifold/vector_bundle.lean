import geometry.manifold.cont_mdiff
import topology.vector_bundle.basic

open bundle topological_vector_bundle set
open_locale manifold

section /-! ## move these -/

lemma topological_vector_bundle.trivialization.symm_coord_change
  {𝕜 : Type*} {B : Type*} {F : Type*} {E : B → Type*}
  [nontrivially_normed_field 𝕜]
  [Π (x : B), add_comm_monoid (E x)]
  [Π (x : B), module 𝕜 (E x)]
  [normed_add_comm_group F]
  [normed_space 𝕜 F]
  [topological_space B]
  [topological_space (total_space E)]
  [Π (x : B), topological_space (E x)]
  (e : trivialization 𝕜 F E)
  (e' : trivialization 𝕜 F E)
  {b : B}
  (hb : b ∈ e'.base_set ∩ e.base_set) :
  (e.coord_change e' b).symm = e'.coord_change e b :=
begin
  dsimp [topological_vector_bundle.trivialization.coord_change],
  sorry,
end

lemma topological_vector_bundle.trivialization.apply_symm_apply_eq_coord_change
  {𝕜 : Type*} {B : Type*} {F : Type*}
  {E : B → Type*}
  [nontrivially_normed_field 𝕜]
  [Π (x : B), add_comm_monoid (E x)]
  [Π (x : B), module 𝕜 (E x)]
  [normed_add_comm_group F]
  [normed_space 𝕜 F]
  [topological_space B]
  [topological_space (total_space E)]
  [Π (x : B), topological_space (E x)]
  (e : trivialization 𝕜 F E)
  (e' : trivialization 𝕜 F E)
  {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set)
  (v : F) :
  e' ((e.to_local_homeomorph.symm) (b, v)) =
    (b, e.coord_change e' b v) :=
begin
  admit,
end

end

/-! ## main constructions -/

variables {𝕜 B F : Type*} {E : B → Type*}
variables [nontrivially_normed_field 𝕜] [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F] [topological_space B]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [charted_space HB B] [smooth_manifold_with_corners IB B]

-- dangerous instance
instance is_topological_fiber_bundle.charted_space [topological_vector_bundle 𝕜 F E] :
  charted_space (B × F) (total_space E) :=
{ atlas := (λ e : trivialization 𝕜 F E, e.to_local_homeomorph) '' trivialization_atlas 𝕜 F E,
  chart_at := λ x, (trivialization_at 𝕜 F E x.proj).to_local_homeomorph,
  mem_chart_source := λ x, (trivialization_at 𝕜 F E x.proj).mem_source.mpr
    (mem_base_set_trivialization_at 𝕜 F E x.proj),
  chart_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas 𝕜 F E _) }

def groupoid_base.local_homeomorph (φ : B → F ≃L[𝕜] F) {U : set B} (hU : is_open U)
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

def groupoid_base : structure_groupoid (B × F) :=
{ members := ⋃ (φ : B → F ≃L[𝕜] F) (U : set B) (hU : is_open U)
  (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x).symm : B → F →L[𝕜] F) U),
  {e | e.eq_on_source (groupoid_base.local_homeomorph φ hU hφ.continuous_on h2φ.continuous_on)},
  trans' := sorry,
  symm' := sorry,
  id_mem' := sorry,
  locality' := sorry,
  eq_on_source' := sorry }

-- def groupoid_base' : structure_groupoid (B × F) :=
-- pregroupoid.groupoid
--   { property := sorry,
--     comp := sorry,
--     id_mem := sorry,
--     locality := sorry,
--     congr := sorry }

variables (IB F E)

class smooth_vector_bundle [topological_vector_bundle 𝕜 F E] : Prop :=
(smooth_transitions : ∀ e ∈ trivialization_atlas 𝕜 F E, ∀ e' ∈ trivialization_atlas 𝕜 F E,
  smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ b, trivialization.coord_change e e' b : B → F →L[𝕜] F)
  (e.base_set ∩ e'.base_set))

instance [topological_vector_bundle 𝕜 F E] [smooth_vector_bundle F E IB] :
  has_groupoid (total_space E) (groupoid_base IB : structure_groupoid (B × F)) :=
{ compatible := begin
    rintros _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩,
    dsimp,
    apply mem_Union.mpr,
    use λ b, trivialization.coord_change e e' b,
    simp_rw mem_Union,
    use e.base_set ∩ e'.base_set,
    use e.open_base_set.inter e'.open_base_set,
    use smooth_vector_bundle.smooth_transitions e he e' he',
    refine ⟨_, _, _⟩,
    { rw inter_comm,
      apply cont_mdiff_on.congr (smooth_vector_bundle.smooth_transitions e' he' e he),
      { intros b hb,
        rw topological_vector_bundle.trivialization.symm_coord_change e e' hb },
      { apply_instance },
      { apply_instance }, },
    { simp [e.symm_trans_source_eq e'.to_fiber_bundle_trivialization,
        groupoid_base.local_homeomorph] },
    { rintros ⟨b, v⟩ hb,
      have hb' : b ∈ e.base_set ∩ e'.base_set :=
        by simpa only [local_homeomorph.trans_to_local_equiv, local_homeomorph.symm_to_local_equiv,
        local_homeomorph.coe_coe_symm, e.symm_trans_source_eq e'.to_fiber_bundle_trivialization,
        prod_mk_mem_set_prod_eq, mem_univ, and_true] using hb,
      simp [groupoid_base.local_homeomorph, e.apply_symm_apply_eq_coord_change e' hb'] }
  end }
