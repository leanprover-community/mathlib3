import geometry.manifold.cont_mdiff
import topology.vector_bundle.basic

open bundle topological_vector_bundle set
open_locale manifold

section /-! ## move these -/
#check charted_space.comp
#check structure_groupoid.has_groupoid.comp

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
  e' ((e.to_local_homeomorph.symm) (b, v)) = (b, e.coord_change e' b v) :=
begin
  sorry,
end

end

/-! ## main constructions -/

variables {𝕜 B B' F M : Type*} {E : B → Type*}
variables [nontrivially_normed_field 𝕜] [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
  [topological_space B'] [charted_space HB B'] [smooth_manifold_with_corners IB B']
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] (IM : model_with_corners 𝕜 EM HM)
  [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]

-- dangerous instance
instance is_topological_fiber_bundle.charted_space [topological_vector_bundle 𝕜 F E] :
  charted_space (B × F) (total_space E) :=
{ atlas := (λ e : trivialization 𝕜 F E, e.to_local_homeomorph) '' trivialization_atlas 𝕜 F E,
  chart_at := λ x, (trivialization_at 𝕜 F E x.proj).to_local_homeomorph,
  mem_chart_source := λ x, (trivialization_at 𝕜 F E x.proj).mem_source.mpr
    (mem_base_set_trivialization_at 𝕜 F E x.proj),
  chart_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas 𝕜 F E _) }

/-- For `B` a topological space and `F` a `𝕜`-normed space, a map from `U : set B` to `F ≃L[𝕜] F`
determines a local homeomorphism from `B × F` to itself by its action fibrewise. -/
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

lemma groupoid_base.source_trans_local_homeomorph {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U') :
  (groupoid_base.local_homeomorph φ hU hφ h2φ ≫ₕ
      groupoid_base.local_homeomorph φ' hU' hφ' h2φ').source = (U ∩ U') ×ˢ univ :=
begin
  sorry,
end

lemma groupoid_base.trans_local_homeomorph_apply {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U')
  {b : B}
  (hb : b ∈ U ∩ U')
  (v : F) :
  (groupoid_base.local_homeomorph φ hU hφ h2φ ≫ₕ
      groupoid_base.local_homeomorph φ' hU' hφ' h2φ') ⟨b, v⟩ = ⟨b, φ' b (φ b v)⟩ :=
begin
  sorry,
end

variables (F B)
/-- For `B` a manifold and `F` a normed space, the groupoid on `B × F` consisting of local
homeomorphisms which are bi-smooth and fibrewise linear. -/
def smooth_fiberwise_linear : structure_groupoid (B × F) :=
{ members := ⋃ (φ : B → F ≃L[𝕜] F) (U : set B) (hU : is_open U)
  (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x).symm : B → F →L[𝕜] F) U),
  {e | e.eq_on_source (groupoid_base.local_homeomorph φ hU hφ.continuous_on h2φ.continuous_on)},
  trans' := begin
    rintros e e' ⟨-, ⟨φ, rfl⟩, -, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, -, ⟨hφ, rfl⟩, -, ⟨h2φ, rfl⟩, heφ⟩
      ⟨-, ⟨φ', rfl⟩, -, ⟨U', rfl⟩, -, ⟨hU', rfl⟩, -, ⟨hφ', rfl⟩, -, ⟨h2φ', rfl⟩, heφ'⟩,
    dsimp at heφ heφ',
    apply mem_Union.mpr,
    use λ b, (φ b).trans (φ' b),
    simp_rw mem_Union,
    refine ⟨U ∩ U', hU.inter hU', _, _, setoid.trans (heφ.trans' heφ') ⟨_, _⟩⟩,
    { sorry },
    { sorry }, -- two smoothness checks
    { apply groupoid_base.source_trans_local_homeomorph },
    { rintros ⟨b, v⟩ hb,
      apply groupoid_base.trans_local_homeomorph_apply,
      rw groupoid_base.source_trans_local_homeomorph at hb,
      simpa [-mem_inter] using hb }
  end,
  symm' := begin
    rintros e ⟨-, ⟨φ, rfl⟩, -, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, -, ⟨hφ, rfl⟩, -, ⟨h2φ, rfl⟩, heφ⟩,
    dsimp at heφ,
    apply mem_Union.mpr,
    use λ b, (φ b).symm,
    simp_rw mem_Union,
    refine ⟨U, hU, h2φ, _, heφ.symm'⟩,
    simp_rw continuous_linear_equiv.symm_symm,
    exact hφ
  end,
  id_mem' := begin
    apply mem_Union.mpr,
    use λ b, continuous_linear_equiv.refl 𝕜 F,
    simp_rw mem_Union,
    refine ⟨univ, is_open_univ, cont_mdiff_on_const, cont_mdiff_on_const, ⟨_, λ b hb, _⟩⟩,
    { simp [groupoid_base.local_homeomorph] },
    { simp [groupoid_base.local_homeomorph] },
  end,
  locality' := sorry, -- a bit tricky, need to glue together a family of `φ`
  eq_on_source' := begin
    rintros e e' ⟨-, ⟨φ, rfl⟩, -, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, -, ⟨hφ, rfl⟩, -, ⟨h2φ, rfl⟩, heφ⟩ hee',
    apply mem_Union.mpr,
    use φ,
    simp_rw mem_Union,
    refine ⟨U, hU, hφ, h2φ, setoid.trans hee' heφ⟩,
  end }

variables (IB F E) {B}

/-- Class stating that a topological vector bundle is smooth, in the sense of having smooth
transition functions. -/
class smooth_vector_bundle [topological_vector_bundle 𝕜 F E] : Prop :=
(smooth_transitions : ∀ e ∈ trivialization_atlas 𝕜 F E, ∀ e' ∈ trivialization_atlas 𝕜 F E,
  smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ b, trivialization.coord_change e e' b : B → F →L[𝕜] F)
  (e.base_set ∩ e'.base_set))

/-- For a smooth vector bundle `E` over `B` with fibre modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is smooth and
fibrewise linear. -/
instance [topological_vector_bundle 𝕜 F E] [smooth_vector_bundle F E IB] :
  has_groupoid (total_space E) (smooth_fiberwise_linear B F IB) :=
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

-- #print instances charted_space
-- #check model_prod
-- local attribute [instance] charted_space_self
section
local attribute [reducible] model_prod

instance is_topological_fiber_bundle.charted_space' [topological_vector_bundle 𝕜 F E] :
  charted_space (model_prod HB F) (total_space E) :=
charted_space.comp _ (model_prod B F) _
end

lemma lift_prop_on_cont_diff_groupoid_iff (f : local_homeomorph B B') :
  lift_prop_on (cont_diff_groupoid ⊤ IB).is_local_structomorph_within_at f f.source
  ↔ smooth_on IB IB f f.source ∧ smooth_on IB IB f.symm f.target :=
sorry

instance [topological_vector_bundle 𝕜 F E] [smooth_vector_bundle F E IB] :
  smooth_manifold_with_corners (IB.prod 𝓘(𝕜, F)) (total_space E) :=
begin
  refine { .. structure_groupoid.has_groupoid.comp (smooth_fiberwise_linear B F IB) _ },
  intros e he,
  rw [lift_prop_on_cont_diff_groupoid_iff],
  sorry
end


#lint
