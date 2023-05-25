/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import topology.vector_bundle.basic
import analysis.normed_space.alternating

/-!
# The vector bundle of continuous alternating maps

We define the (topological) vector bundle of continuous alternating maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, and normed spaces `F₁` and `F₂`, we define
`bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂ x` to be a type synonym for
`λ x, continuous_alternating_map 𝕜 (E₁ x) (E₂ x) ι`. If the `E₁` and `E₂` are vector bundles with
model fibers `F₁` and `F₂`, then this will be a vector bundle with fiber
`continuous_alternating_map 𝕜 F₁ F₂ ι`.

The topology is constructed from the trivializations for `E₁` and `E₂` and the norm-topology on the
model fiber `continuous_alternating_map 𝕜 F₁ F₂ ι` using the `vector_prebundle` construction.  This
is a bit awkward because it introduces a spurious (?) dependence on the normed space structure of
the model fiber.

Similar constructions should be possible (but are yet to be formalized) for tensor products of
topological vector bundles, exterior algebras, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.

## Main Definitions

* `bundle.continuous_alternating_map.vector_bundle`: continuous alternating maps between
  vector bundles form a vector bundle.

-/

noncomputable theory

open_locale bundle
open bundle set continuous_alternating_map

section defs
variables (𝕜 : Type*) [normed_field 𝕜] (ι : Type*)
variables {B : Type*}
variables (F₁ : Type*) (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]
variables [Π x, topological_space (E₁ x)]
variables (F₂ : Type*) (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]
variables [Π x, topological_space (E₂ x)]

include F₁ F₂

-- In this definition we require the scalar rings `𝕜` and `𝕜` to be normed fields, although
-- something much weaker (maybe `comm_semiring`) would suffice mathematically -- this is because of
-- a typeclass inference bug with pi-types:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue
/-- The bundle of continuous `ι`-slot alternating maps between the topological vector bundles `E₁` and
`E₂`. This is a type synonym for `λ x, E₁ x →SL[σ] E₂ x`.

We intentionally add `F₁` and `F₂` as arguments to this type, so that instances on this type
(that depend on `F₁` and `F₂`) actually refer to `F₁` and `F₂`. -/
@[derive inhabited, nolint unused_arguments]
protected def bundle.continuous_alternating_map (x : B) : Type* :=
continuous_alternating_map 𝕜 (E₁ x) (E₂ x) ι

variables [Π x, has_continuous_add (E₂ x)]

instance (x : B) : add_comm_monoid (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂ x) :=
by delta_instance bundle.continuous_alternating_map

variables [∀ x, has_continuous_smul 𝕜 (E₂ x)]

instance (x : B) : module 𝕜 (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂ x) :=
by delta_instance bundle.continuous_alternating_map

end defs

variables (𝕜 : Type*) [nontrivially_normed_field 𝕜] (ι : Type*) [fintype ι]

variables {B : Type*} [topological_space B]

variables (F₁ : Type*) [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
  (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]
  [topological_space (total_space E₁)]
variables (F₂ : Type*) [normed_add_comm_group F₂][normed_space 𝕜 F₂]
  (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]
  [topological_space (total_space E₂)]

variables {F₁ E₁ F₂ E₂} (e₁ e₁' : trivialization F₁ (π E₁)) (e₂ e₂' : trivialization F₂ (π E₂))

namespace pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `continuous_alternating_map_coord_change σ e₁ e₁' e₂ e₂'` is the coordinate
change function between the two induced (pre)trivializations
`pretrivialization.continuous_alternating_map σ e₁ e₂` and
`pretrivialization.continuous_alternating_map σ e₁' e₂'` of `bundle.continuous_alternating_map`. -/
def continuous_alternating_map_coord_change
  [e₁.is_linear 𝕜] [e₁'.is_linear 𝕜] [e₂.is_linear 𝕜] [e₂'.is_linear 𝕜] (b : B) :
  (continuous_alternating_map 𝕜 F₁ F₂ ι) →L[𝕜] (continuous_alternating_map 𝕜 F₁ F₂ ι) :=
sorry
-- ((e₁'.coord_changeL 𝕜 e₁ b).symm.arrow_congrSL (e₂.coord_changeL 𝕜 e₂' b) :
--   (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι) ≃L[𝕜]_root_.continuous_alternating_map 𝕜 F₁ F₂ ι)

variables {e₁ e₁' e₂ e₂'}
variables [Π x, topological_space (E₁ x)] [fiber_bundle F₁ E₁]
variables [Π x, topological_space (E₂ x)] [fiber_bundle F₂ E₂]

lemma continuous_on_continuous_alternating_map_coord_change
  [vector_bundle 𝕜 F₁ E₁] [vector_bundle 𝕜 F₂ E₂]
  [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₁']
  [mem_trivialization_atlas e₂] [mem_trivialization_atlas e₂'] :
  continuous_on (continuous_alternating_map_coord_change 𝕜 ι e₁ e₁' e₂ e₂')
    ((e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) :=
begin
  sorry
  -- have h₁ := (compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜)).continuous,
  -- have h₂ := (continuous_alternating_map.flip (compSL F₁ F₁ F₂ (ring_hom.id 𝕜) σ)).continuous,
  -- have h₃ := (continuous_on_coord_change 𝕜 e₁' e₁),
  -- have h₄ := (continuous_on_coord_change 𝕜 e₂ e₂'),
  -- refine ((h₁.comp_continuous_on (h₄.mono _)).clm_comp (h₂.comp_continuous_on (h₃.mono _))).congr _,
  -- { mfld_set_tac },
  -- { mfld_set_tac },
  -- { intros b hb, ext L v,
  --   simp only [continuous_alternating_map_coord_change, continuous_alternating_equiv.coe_coe,
  --     continuous_alternating_equiv.arrow_congrSL_apply, comp_apply, function.comp, compSL_apply,
  --     flip_apply, continuous_alternating_equiv.symm_symm] },
end

variables (e₁ e₁' e₂ e₂') [e₁.is_linear 𝕜] [e₁'.is_linear 𝕜] [e₂.is_linear 𝕜] [e₂'.is_linear 𝕜]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`pretrivialization.continuous_alternating_map σ e₁ e₂` is the induced pretrivialization for the
continuous `ι`-slot alternating maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
def continuous_alternating_map :
  pretrivialization (continuous_alternating_map 𝕜 F₁ F₂ ι)
    (π (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂)) :=
{ to_fun := λ p, ⟨p.1, (e₂.continuous_linear_map_at 𝕜 p.1).comp_continuous_alternating_map $
      p.2.comp_continuous_linear_map $ e₁.symmL 𝕜 p.1⟩,
  inv_fun := λ p, ⟨p.1, (e₂.symmL 𝕜 p.1).comp_continuous_alternating_map $
      p.2.comp_continuous_linear_map $ e₁.continuous_linear_map_at 𝕜 p.1⟩,
  source := (bundle.total_space.proj) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ set.univ,
  map_source' := λ ⟨x, L⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, f⟩ h, h.1,
  left_inv' := λ ⟨x, L⟩ ⟨h₁, h₂⟩,
  begin
    sorry,
    -- simp_rw [sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_and],
    -- ext v,
    -- simp only [comp_apply, trivialization.symmL_continuous_alternating_map_at, h₁, h₂]
  end,
  right_inv' := λ ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩,
  begin
    sorry
    -- simp_rw [prod.mk.inj_iff, eq_self_iff_true, true_and],
    -- ext v,
    -- simp only [comp_apply, trivialization.continuous_alternating_map_at_symmL, h₁, h₂]
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, f⟩ h, rfl }

instance continuous_alternating_map.is_linear
  [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜 (E₂ x)] :
  (pretrivialization.continuous_alternating_map 𝕜 ι e₁ e₂).is_linear 𝕜 :=
{ linear := λ x h,
  { map_add := λ L L',
    -- show (e₂.continuous_alternating_map_at 𝕜 x).comp ((L + L').comp (e₁.symmL 𝕜 x)) = _,
    begin
      sorry
      -- simp_rw [add_comp, comp_add],
      -- refl
    end,
    map_smul := λ c L,
    -- show (e₂.continuous_alternating_map_at 𝕜 x).comp ((c • L).comp (e₁.symmL 𝕜 x)) = _,
    begin
      sorry
      -- simp_rw [smul_comp, comp_smulₛₗ, ring_hom.id_apply],
      -- refl
    end, } }

lemma continuous_alternating_map_apply
  (p : total_space (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂)) :
  (continuous_alternating_map 𝕜 ι e₁ e₂) p =
  ⟨p.1, (e₂.continuous_linear_map_at 𝕜 p.1).comp_continuous_alternating_map $
      p.2.comp_continuous_linear_map $ e₁.symmL 𝕜 p.1⟩ :=
rfl

lemma continuous_alternating_map_symm_apply (p : B × (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι)) :
  (continuous_alternating_map 𝕜 ι e₁ e₂).to_local_equiv.symm p =
  ⟨p.1, (e₂.symmL 𝕜 p.1).comp_continuous_alternating_map $
      p.2.comp_continuous_linear_map $ e₁.continuous_linear_map_at 𝕜 p.1⟩ :=
rfl

variables [Π x, has_continuous_add (E₂ x)]

lemma continuous_alternating_map_symm_apply' {b : B} (hb : b ∈ e₁.base_set ∩ e₂.base_set)
  (L : _root_.continuous_alternating_map 𝕜 F₁ F₂ ι) :
  (continuous_alternating_map 𝕜 ι e₁ e₂).symm b L =
  (e₂.symmL 𝕜 b).comp_continuous_alternating_map
  (L.comp_continuous_linear_map $ e₁.continuous_linear_map_at 𝕜 b) :=
begin
  rw [symm_apply], refl, exact hb
end

lemma continuous_alternating_map_coord_change_apply (b : B)
  (hb : b ∈ (e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set))
  (L : _root_.continuous_alternating_map 𝕜 F₁ F₂ ι) :
  continuous_alternating_map_coord_change 𝕜 ι e₁ e₁' e₂ e₂' b L =
  (continuous_alternating_map 𝕜 ι e₁' e₂'
    (total_space_mk b ((continuous_alternating_map 𝕜 ι e₁ e₂).symm b L))).2 :=
begin
  sorry
  -- ext v,
  -- simp_rw [continuous_alternating_map_coord_change, continuous_alternating_equiv.coe_coe,
  --   continuous_alternating_equiv.arrow_congrSL_apply,
  --   continuous_alternating_map_apply, continuous_alternating_map_symm_apply' σ e₁ e₂ hb.1,
  --   comp_apply, continuous_alternating_equiv.coe_coe, continuous_alternating_equiv.symm_symm,
  --   trivialization.continuous_alternating_map_at_apply, trivialization.symmL_apply],
  -- dsimp only [total_space_mk],
  -- rw [e₂.coord_changeL_apply e₂', e₁'.coord_changeL_apply e₁, e₁.coe_linear_map_at_of_mem hb.1.1,
  --   e₂'.coe_linear_map_at_of_mem hb.2.2],
  -- exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]
end

end pretrivialization

open pretrivialization
variables (F₁ E₁ F₂ E₂)
variables [Π x : B, topological_space (E₁ x)] [fiber_bundle F₁ E₁] [vector_bundle 𝕜 F₁ E₁]
variables [Π x : B, topological_space (E₂ x)] [fiber_bundle F₂ E₂] [vector_bundle 𝕜 F₂ E₂]
variables [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜 (E₂ x)]

/-- The continuous `ι`-slot alternating maps between two topological vector bundles form a
`vector_prebundle` (this is an auxiliary construction for the
`vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.bundle.continuous_alternating_map.vector_prebundle :
  vector_prebundle 𝕜 (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι)
  (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂) :=
{ pretrivialization_atlas :=
    {e |  ∃ (e₁ : trivialization F₁ (π E₁)) (e₂ : trivialization F₂ (π E₂))
    [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₂], by exactI
    e = pretrivialization.continuous_alternating_map 𝕜 ι e₁ e₂},
  pretrivialization_linear' := begin
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩,
    apply_instance
  end,
  pretrivialization_at := λ x, pretrivialization.continuous_alternating_map 𝕜 ι
    (trivialization_at F₁ E₁ x) (trivialization_at F₂ E₂ x),
  mem_base_pretrivialization_at := λ x,
    ⟨mem_base_set_trivialization_at F₁ E₁ x, mem_base_set_trivialization_at F₂ E₂ x⟩,
  pretrivialization_mem_atlas := λ x,
    ⟨trivialization_at F₁ E₁ x, trivialization_at F₂ E₂ x, _, _, rfl⟩,
  exists_coord_change := by { rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩,
    resetI,
    exact ⟨continuous_alternating_map_coord_change 𝕜 ι e₁ e₁' e₂ e₂',
    continuous_on_continuous_alternating_map_coord_change 𝕜 ι,
    continuous_alternating_map_coord_change_apply 𝕜 ι e₁ e₁' e₂ e₂'⟩ } }

/-- Topology on the continuous `ι`-slot alternating_maps between the respective fibers at a point of two
"normable" vector bundles over the same base. Here "normable" means that the bundles have fibers
modelled on normed spaces `F₁`, `F₂` respectively.  The topology we put on the continuous
`ι`-slot alternating_maps is the topology coming from the operator norm on maps from `F₁` to `F₂`. -/
instance (x : B) : topological_space (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂ x) :=
(bundle.continuous_alternating_map.vector_prebundle 𝕜 ι F₁ E₁ F₂ E₂).fiber_topology x

/-- Topology on the total space of the continuous `ι`-slot alternating_maps between two "normable" vector
bundles over the same base. -/
instance bundle.continuous_alternating_map.topological_space_total_space :
  topological_space (total_space (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂)) :=
(bundle.continuous_alternating_map.vector_prebundle
  𝕜 ι F₁ E₁ F₂ E₂).total_space_topology

/-- The continuous `ι`-slot alternating_maps between two vector bundles form a fiber bundle. -/
instance _root_.bundle.continuous_alternating_map.fiber_bundle :
  fiber_bundle (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι) (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂) :=
(bundle.continuous_alternating_map.vector_prebundle
  𝕜 ι F₁ E₁ F₂ E₂).to_fiber_bundle

/-- The continuous `ι`-slot alternating_maps between two vector bundles form a vector bundle. -/
instance _root_.bundle.continuous_alternating_map.vector_bundle :
  vector_bundle 𝕜 (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι) (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂) :=
(bundle.continuous_alternating_map.vector_prebundle
  𝕜 ι F₁ E₁ F₂ E₂).to_vector_bundle

variables (e₁ e₂) [he₁ : mem_trivialization_atlas e₁] [he₂ : mem_trivialization_atlas e₂]
  {F₁ E₁ F₂ E₂}

include he₁ he₂

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `ι`-slot alternating maps from `E₁` to `E₂`,
whose base set is `e₁.base_set ∩ e₂.base_set`. -/
def trivialization.continuous_alternating_map :
  trivialization (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι)
  (π (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂)) :=
vector_prebundle.trivialization_of_mem_pretrivialization_atlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance _root_.bundle.continuous_alternating_map.mem_trivialization_atlas :
  mem_trivialization_atlas (e₁.continuous_alternating_map 𝕜 ι e₂ :
    trivialization (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι)
    (π (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂))) :=
{ out := ⟨_, ⟨e₁, e₂, by apply_instance, by apply_instance, rfl⟩, rfl⟩ }

variables {e₁ e₂}

@[simp] lemma trivialization.base_set_continuous_alternating_map :
  (e₁.continuous_alternating_map 𝕜 ι e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

lemma trivialization.continuous_alternating_map_apply
  (p : total_space (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂)) :
  e₁.continuous_alternating_map 𝕜 ι e₂ p =
  ⟨p.1, (e₂.continuous_linear_map_at 𝕜 p.1).comp_continuous_alternating_map $
      p.2.comp_continuous_linear_map $ e₁.symmL 𝕜 p.1⟩ :=
rfl

omit he₁ he₂

-- lemma hom_trivialization_at_apply (x₀ : B)
--   (x : total_space (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂)) :
--   trivialization_at (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι) (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂) x₀ x =
--   ⟨x.1, in_coordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩ :=
-- rfl

@[simp, mfld_simps]
lemma hom_trivialization_at_source (x₀ : B) :
  (trivialization_at (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι) (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂) x₀).source =
  π (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂) ⁻¹'
    ((trivialization_at F₁ E₁ x₀).base_set ∩ (trivialization_at F₂ E₂ x₀).base_set) :=
rfl

@[simp, mfld_simps]
lemma hom_trivialization_at_target (x₀ : B) :
  (trivialization_at (_root_.continuous_alternating_map 𝕜 F₁ F₂ ι) (bundle.continuous_alternating_map 𝕜 ι F₁ E₁ F₂ E₂) x₀).target =
  ((trivialization_at F₁ E₁ x₀).base_set ∩ (trivialization_at F₂ E₂ x₀).base_set) ×ˢ set.univ :=
rfl
