/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import topology.vector_bundle.basic
import geometry.manifold.fiber_bundle

/-!
# Smooth vector bundles

In this file we define smooth vector bundles.

-/

noncomputable theory

open bundle set
open_locale classical manifold

variables {𝕜 : Type*} {B V V' H H' : Type*}

variables [nondiscrete_normed_field 𝕜]
variables [normed_group V] [normed_space 𝕜 V] [normed_group V'] [normed_space 𝕜 V']
variables [topological_space H] [topological_space H']
variables (I : model_with_corners 𝕜 V H) (I' : model_with_corners 𝕜 V' H')
variables (F : Type*) (E : B → Type*)
variables [∀ x, normed_group (E x)] [∀ x, normed_space 𝕜 (E x)]
variables [normed_group F] [normed_space 𝕜 F]
variables [topological_space B] [charted_space H B] -- [smooth_manifold_with_corners I B]

variables [topological_space (total_space E)] [charted_space H' (total_space E)]
-- variables [smooth_manifold_with_corners I' (total_space E)]

/-- Local trivialization for smooth vector bundles. -/
@[nolint has_inhabited_instance]
structure smooth_vector_bundle.trivialization extends to_fiber_bundle :
  smooth_fiber_bundle.trivialization I 𝓘(𝕜, F) I' F (@total_space.proj B E) :=
(linear' : ∀ x ∈ base_set, is_linear_map 𝕜 (λ y : E x, (to_fun y).2))

open smooth_vector_bundle

namespace smooth_vector_bundle.trivialization

variables {𝕜 I I' F E} (e : trivialization I I' F E) {x : total_space E} {b : B} {y : E b}

/-- Natural identification as a `trivialization` of a topological vector bundle. -/
def to_topological : topological_vector_bundle.trivialization 𝕜 F E :=
{ ..e.to_fiber_bundle.to_topological, ..e }

/-- The local homeomorph defined by the trivialization. -/
def to_local_homeomorph : local_homeomorph (total_space E) (B × F) :=
e.to_topological.to_local_homeomorph

instance : has_coe_to_fun (trivialization I I' F E) (λ _, total_space E → B × F) := ⟨λ e, e.to_fun⟩

instance : has_coe (trivialization I I' F E) (topological_vector_bundle.trivialization 𝕜 F E) :=
⟨smooth_vector_bundle.trivialization.to_topological⟩

instance : has_coe (trivialization I I' F E)
  (smooth_fiber_bundle.trivialization I 𝓘(𝕜, F) I' F (@total_space.proj B E)) :=
⟨smooth_vector_bundle.trivialization.to_fiber_bundle⟩

-- protected lemma linear : ∀ x ∈ e.base_set, is_linear_map 𝕜 (λ y : (E x), (e y).2) := e.linear'
protected lemma smooth_on : smooth_on I' (I.prod 𝓘(𝕜, F)) e e.source :=
e.to_fiber_bundle.smooth_on

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_fiber_bundle = e := rfl
@[simp, mfld_simps] lemma coe_coe2 : e.to_topological.to_local_homeomorph = e.to_local_homeomorph :=
rfl
@[simp, mfld_simps] lemma coe_coe3 : e.to_local_homeomorph.to_local_equiv = e.to_local_equiv :=
rfl

@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = x.proj := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ x.proj ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_mem_source : ↑y ∈ e.source ↔ b ∈ e.base_set := e.mem_source
lemma coe_fst' (ex : x.proj ∈ e.base_set) : (e x).1 = x.proj :=
e.coe_fst (e.mem_source.2 ex)

protected lemma eq_on : eq_on (prod.fst ∘ e) total_space.proj e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : x.proj ∈ e.base_set) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

@[simp, mfld_simps] lemma coe_coe_fst (hb : b ∈ e.base_set) : (e y).1 = b :=
e.coe_fst (e.mem_source.2 hb)

lemma source_inter_preimage_target_inter (s : set (B × F)) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_local_homeomorph.source_inter_preimage_target_inter s

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_topological.mem_target

lemma mk_mem_target {y : F} : (b, y) ∈ e.target ↔ b ∈ e.base_set :=
e.to_topological.mem_target

lemma map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
e.to_local_homeomorph.map_target hx

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) :
  (e.to_local_homeomorph.symm x).proj = x.1 :=
e.to_topological.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F}
  (hx : b ∈ e.base_set) : (e.to_local_homeomorph.symm (b, x)).proj = b :=
e.to_topological.proj_symm_apply' hx

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply'
  {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_topological.apply_symm_apply' hx

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e.source) :
  e.to_local_homeomorph.symm (e x) = x :=
e.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_coe_fst' {x : B} {y : F}
  (e : trivialization I I' F E) (h : x ∈ e.base_set) :
  ((e.to_local_homeomorph.symm) (x, y)).fst = x := e.proj_symm_apply' h

/-- A fiberwise inverse to `e`. The function `F → E x` that induces a local inverse
  `B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (e : trivialization I I' F E) (b : B) (y : F) : E b :=
e.to_topological.symm b y

lemma symm_apply (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.symm_coe_fst' hb)) (e.to_local_homeomorph.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem (e : trivialization I I' F E) {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma mk_symm (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_homeomorph.symm (b, y) :=
e.to_topological.mk_symm hb y

lemma symm_proj_apply (e : trivialization I I' F E) (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
e.to_topological.symm_proj_apply z hz

lemma symm_apply_apply_mk (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
e.to_topological.apply_mk_symm hb y

lemma continuous_on_symm (e : trivialization I I' F E) :
  continuous_on (λ z : B × F, total_space_mk z.1 (e.symm z.1 z.2))
    (e.base_set ×ˢ (univ : set F)) :=
begin
  have : ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : set F)),
    total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z,
  { rintro x ⟨hx : x.1 ∈ e.base_set, _⟩, simp_rw [e.mk_symm hx, prod.mk.eta] },
  refine continuous_on.congr _ this,
  rw [← e.target_eq],
  exact e.to_local_homeomorph.continuous_on_symm
end

end smooth_vector_bundle.trivialization

section

variables (B)

-- /-- The valid transition functions for a topological vector bundle over `B` modelled on
-- a normed space `F`: a transition function must be a local homeomorphism of `B × F` with source and
-- target both `s ×ˢ univ`, which on this set is of the form `λ (b, v), (b, ε b v)` for some continuous
-- map `ε` from `s` to `F ≃L[𝕜] F`.  Here continuity is with respect to the operator norm on
-- `F →L[𝕜] F`. -/
-- def continuous_transitions (e : local_equiv (B × F) (B × F)) : Prop :=
-- ∃ s : set B, e.source = s ×ˢ (univ : set F) ∧ e.target = s ×ˢ (univ : set F)
--     ∧ ∃ ε : B → (F ≃L[𝕜] F), continuous_on (λ b, (ε b : F →L[𝕜] F)) s
--       ∧ ∀ b ∈ s, ∀ v : F, e (b, v) = (b, ε b v)

variables {B}

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`smooth_vector_bundle 𝕜 F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class smooth_vector_bundle :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization I I' F E))
(trivialization_at [] : B → trivialization I I' F E)
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)
(continuous_coord_change : ∀ e e' ∈ trivialization_atlas,
  continuous_transitions 𝕜 B F (e.to_local_equiv.symm.trans e'.to_local_equiv : _))

export smooth_vector_bundle (trivialization_atlas trivialization_at
  mem_base_set_trivialization_at trivialization_mem_atlas)

variable [smooth_vector_bundle I I' F E]

namespace smooth_vector_bundle

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at I I' F E z.1).source :=
by { rw smooth_fiber_bundle.trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {𝕜 I I' F E}

/-- The co-ordinate change (transition function) between two trivializations of a vector bundle
over `B` modelled on `F`: this is a function from `B` to `F ≃L[𝕜] F` (of course, only meaningful
on the intersection of the domains of definition of the two trivializations). -/
def coord_change {e e' : trivialization I I' F E} (he : e ∈ trivialization_atlas I I' F E)
  (he' : e' ∈ trivialization_atlas I I' F E) :
  B → F ≃L[𝕜] F :=
(smooth_vector_bundle.continuous_coord_change e he e' he').some_spec.2.2.some

lemma continuous_on_coord_change {e e' : trivialization I I' F E} (he : e ∈ trivialization_atlas I I' F E)
  (he' : e' ∈ trivialization_atlas I I' F E) :
  continuous_on (λ b, (coord_change he he' b : F →L[𝕜] F)) (e.base_set ∩ e'.base_set) :=
begin
  let s := (continuous_coord_change e he e' he').some,
  let hs := (continuous_coord_change e he e' he').some_spec.1,
  have hs : s = e.base_set ∩ e'.base_set,
  { have : s ×ˢ (univ : set F) = (e.base_set ∩ e'.base_set) ×ˢ (univ : set F) :=
      hs.symm.trans (topological_fiber_bundle.trivialization.symm_trans_source_eq e e'),
    have hF : (univ : set F).nonempty := univ_nonempty,
      rwa prod_eq_iff_eq hF at this },
  rw ← hs,
  exact (continuous_coord_change e he e' he').some_spec.2.2.some_spec.1
end

lemma trans_eq_coord_change {e e' : trivialization I I' F E} (he : e ∈ trivialization_atlas I I' F E)
  (he' : e' ∈ trivialization_atlas I I' F E) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  e' (e.to_local_homeomorph.symm (b, v)) = (b, coord_change he he' b v) :=
begin
  let s := (continuous_coord_change e he e' he').some,
  let hs := (continuous_coord_change e he e' he').some_spec.1,
  have hs : s = e.base_set ∩ e'.base_set,
  { have : s ×ˢ (univ : set F) = (e.base_set ∩ e'.base_set) ×ˢ (univ : set F) :=
      hs.symm.trans (topological_fiber_bundle.trivialization.symm_trans_source_eq e e'),
    have hF : (univ : set F).nonempty := univ_nonempty,
      rwa prod_eq_iff_eq hF at this },
  rw ← hs at hb,
  exact (continuous_coord_change e he e' he').some_spec.2.2.some_spec.2 b hb v
end

attribute [irreducible] coord_change

namespace trivialization

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def continuous_linear_equiv_at (e : trivialization I I' F E) (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[𝕜] F :=
{ to_fun := λ y, (e ⟨b, y⟩).2,
  inv_fun := e.symm b,
  continuous_to_fun := continuous_snd.comp (e.to_local_homeomorph.continuous_on.comp_continuous
    (total_space_mk_inducing 𝕜 F E b).continuous (λ x, e.mem_source.mpr hb)),
  continuous_inv_fun := begin
    rw (smooth_vector_bundle.total_space_mk_inducing 𝕜 F E b).continuous_iff,
    exact e.continuous_on_symm.comp_continuous (continuous_const.prod_mk continuous_id)
      (λ x, mk_mem_prod hb (mem_univ x)),
  end,
  .. e.to_pretrivialization.linear_equiv_at b hb }

@[simp] lemma continuous_linear_equiv_at_apply (e : trivialization I I' F E) (b : B)
  (hb : b ∈ e.base_set) (y : E b) : e.continuous_linear_equiv_at b hb y = (e ⟨b, y⟩).2 := rfl

@[simp] lemma continuous_linear_equiv_at_apply' (e : trivialization I I' F E)
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at (x.proj) (e.mem_source.1 hx) x.2 = (e x).2 := by { cases x, refl }

lemma apply_eq_prod_continuous_linear_equiv_at (e : trivialization I I' F E) (b : B)
  (hb : b ∈ e.base_set) (z : E b) :
  e.to_local_homeomorph ⟨b, z⟩ = (b, e.continuous_linear_equiv_at b hb z) :=
begin
  ext,
  { refine e.coe_fst _,
    rw e.source_eq,
    exact hb },
  { simp only [coe_coe, continuous_linear_equiv_at_apply] }
end

lemma symm_apply_eq_mk_continuous_linear_equiv_at_symm (e : trivialization I I' F E) (b : B)
  (hb : b ∈ e.base_set) (z : F) :
  e.to_local_homeomorph.symm ⟨b, z⟩
  = total_space_mk b ((e.continuous_linear_equiv_at b hb).symm z) :=
begin
  have h : (b, z) ∈ e.to_local_homeomorph.target,
  { rw e.target_eq,
    exact ⟨hb, mem_univ _⟩ },
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h),
  { simp only [e.source_eq, hb, mem_preimage]},
  simp_rw [e.apply_eq_prod_continuous_linear_equiv_at b hb, e.to_local_homeomorph.right_inv h,
    continuous_linear_equiv.apply_symm_apply],
end

lemma comp_continuous_linear_equiv_at_eq_coord_change {e e' : trivialization I I' F E}
  (he : e ∈ trivialization_atlas I I' F E) (he' : e' ∈ trivialization_atlas I I' F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  (e.continuous_linear_equiv_at b hb.1).symm.trans (e'.continuous_linear_equiv_at b hb.2)
  = coord_change he he' b :=
begin
  ext v,
  suffices :
    (b, e'.continuous_linear_equiv_at b hb.2 ((e.continuous_linear_equiv_at b hb.1).symm v))
    = (b, coord_change he he' b v),
  { simpa only [prod.mk.inj_iff, eq_self_iff_true, true_and] using this },
  rw [← trans_eq_coord_change he he' hb, ← apply_eq_prod_continuous_linear_equiv_at,
    symm_apply_eq_mk_continuous_linear_equiv_at_symm],
  refl,
end

end trivialization

section
local attribute [reducible] bundle.trivial

instance {B : Type*} {F : Type*} [add_comm_monoid F] (b : B) :
  add_comm_monoid (bundle.trivial B F b) := ‹add_comm_monoid F›

instance {B : Type*} {F : Type*} [add_comm_group F] (b : B) :
  add_comm_group (bundle.trivial B F b) := ‹add_comm_group F›

instance {B : Type*} {F : Type*} [add_comm_monoid F] [module 𝕜 F] (b : B) :
  module 𝕜 (bundle.trivial B F b) := ‹module 𝕜 F›

end

variables (𝕜 B F)
/-- Local trivialization for trivial bundle. -/
def trivial_smooth_vector_bundle.trivialization : trivialization 𝕜 F (bundle.trivial B F) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := univ,
  target := univ,
  map_source' := λ x h, mem_univ (x.fst, x.snd),
  map_target' := λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_rfl, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_rfl, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear' := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

@[simp]
lemma trivial_smooth_vector_bundle.trivialization_source :
  (trivial_smooth_vector_bundle.trivialization 𝕜 B F).source = univ := rfl

@[simp]
lemma trivial_smooth_vector_bundle.trivialization_target :
  (trivial_smooth_vector_bundle.trivialization 𝕜 B F).target = univ := rfl

instance trivial_bundle.smooth_vector_bundle :
  smooth_vector_bundle 𝕜 F (bundle.trivial B F) :=
{ trivialization_atlas := {trivial_smooth_vector_bundle.trivialization 𝕜 B F},
  trivialization_at := λ x, trivial_smooth_vector_bundle.trivialization 𝕜 B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp, proj,
      induced_const, top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this,
      induced_id],
  end⟩,
  continuous_coord_change := begin
    intros e he e' he',
    rw [mem_singleton_iff.mp he, mem_singleton_iff.mp he'],
    exact ⟨univ, by simp, by simp, λb, continuous_linear_equiv.refl 𝕜 F,
           continuous_const.continuous_on, λ b hb v, rfl⟩
  end }

variables {𝕜 B F}

/- Not registered as an instance because of a metavariable. -/
lemma is_smooth_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨(trivialization_at 𝕜 F E x).to_fiber_bundle_trivialization,
  mem_base_set_trivialization_at 𝕜 F E x⟩

include 𝕜 F

lemma continuous_total_space_mk (x : B) : continuous (total_space_mk x) :=
(smooth_vector_bundle.total_space_mk_inducing 𝕜 F E x).continuous

variables (𝕜 B F)

@[continuity] lemma continuous_proj : continuous (proj E) :=
begin
  apply @is_topological_fiber_bundle.continuous_proj B F,
  apply @is_smooth_vector_bundle_is_topological_fiber_bundle 𝕜,
end

end smooth_vector_bundle

/-! ### Constructing topological vector bundles -/

variables (B)

/-- Analogous construction of `topological_fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure smooth_vector_bundle_core (ι : Type*) :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → (F →L[𝕜] F))
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(coord_change_continuous : ∀ i j, continuous_on (coord_change i j) (base_set i ∩ base_set j))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

/-- The trivial topological vector bundle core, in which all the changes of coordinates are the
identity. -/
def trivial_smooth_vector_bundle_core (ι : Type*) [inhabited ι] :
  smooth_vector_bundle_core 𝕜 B F ι :=
{ base_set := λ ι, univ,
  is_open_base_set := λ i, is_open_univ,
  index_at := λ x, default,
  mem_base_set_at := λ x, mem_univ x,
  coord_change := λ i j x, continuous_linear_map.id 𝕜 F,
  coord_change_self := λ i x hx v, rfl,
  coord_change_comp := λ i j k x hx v, rfl,
  coord_change_continuous := λ i j, continuous_on_const, }

instance (ι : Type*) [inhabited ι] : inhabited (smooth_vector_bundle_core 𝕜 B F ι) :=
⟨trivial_smooth_vector_bundle_core 𝕜 B F ι⟩

namespace smooth_vector_bundle_core

variables {𝕜 B F} {ι : Type*} (Z : smooth_vector_bundle_core 𝕜 B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def to_smooth_vector_bundle_core : topological_fiber_bundle_core ι B F :=
{ coord_change := λ i j b, Z.coord_change i j b,
  coord_change_continuous := λ i j, is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((Z.coord_change_continuous i j).prod_map continuous_on_id),
  ..Z }

instance to_smooth_vector_bundle_core_coe : has_coe (smooth_vector_bundle_core 𝕜 B F ι)
  (topological_fiber_bundle_core ι B F) := ⟨to_smooth_vector_bundle_core⟩

include Z

lemma coord_change_linear_comp (i j k : ι): ∀ x ∈ (Z.base_set i) ∩ (Z.base_set j) ∩ (Z.base_set k),
  (Z.coord_change j k x).comp (Z.coord_change i j x) = Z.coord_change i k x :=
λ x hx, by { ext v, exact Z.coord_change_comp i j k x hx v }

/-- The index set of a topological vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def index := ι

/-- The base space of a topological vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a topological vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def fiber (x : B) := F

section fiber_instances

local attribute [reducible] fiber --just to record instances

instance topological_space_fiber (x : B) : topological_space (Z.fiber x) := by apply_instance
instance add_comm_monoid_fiber : ∀ (x : B), add_comm_monoid (Z.fiber x) := λ x, by apply_instance
instance module_fiber : ∀ (x : B), module 𝕜 (Z.fiber x) := λ x, by apply_instance

variable [add_comm_group F]

instance add_comm_group_fiber : ∀ (x : B), add_comm_group (Z.fiber x) := λ x, by apply_instance

end fiber_instances

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : total_space Z.fiber → B := bundle.proj Z.fiber

/-- The total space of the topological vector bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
topological_fiber_bundle_core.triv_change ↑Z i j

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
topological_fiber_bundle_core.mem_triv_change_source ↑Z i j p

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (Z.total_space) :=
topological_fiber_bundle_core.to_topological_space ι ↑Z

variables {ι} (b : B) (a : F)

@[simp, mfld_simps] lemma coe_coord_change (i j : ι) :
  topological_fiber_bundle_core.coord_change ↑Z i j b = Z.coord_change i j b := rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : smooth_vector_bundle.trivialization 𝕜 F Z.fiber :=
{ linear' := λ x hx,
  { map_add := λ v w, by simp only [continuous_linear_map.map_add] with mfld_simps,
    map_smul := λ r v, by simp only [continuous_linear_map.map_smul] with mfld_simps},
  ..topological_fiber_bundle_core.local_triv ↑Z i }

variable (i : ι)

@[simp, mfld_simps] lemma mem_local_triv_source (p : Z.total_space) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i := iff.rfl

@[simp, mfld_simps] lemma base_set_at : Z.base_set i = (Z.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : Z.total_space) :
  (Z.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (Z.local_triv i).target ↔ p.1 ∈ (Z.local_triv i).base_set :=
topological_fiber_bundle_core.mem_local_triv_target Z i p

@[simp, mfld_simps] lemma local_triv_symm_apply (p : B × F) :
  (Z.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : smooth_vector_bundle.trivialization 𝕜 F Z.fiber :=
Z.local_triv (Z.index_at b)

@[simp, mfld_simps] lemma local_triv_at_def :
  Z.local_triv (Z.index_at b) = Z.local_triv_at b := rfl

@[simp, mfld_simps] lemma mem_source_at : (⟨b, a⟩ : Z.total_space) ∈ (Z.local_triv_at b).source :=
by { rw [local_triv_at, mem_local_triv_source], exact Z.mem_base_set_at b }

@[simp, mfld_simps] lemma local_triv_at_apply : ((Z.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
topological_fiber_bundle_core.local_triv_at_apply Z b a

@[simp, mfld_simps] lemma mem_local_triv_at_base_set :
  b ∈ (Z.local_triv_at b).base_set :=
topological_fiber_bundle_core.mem_local_triv_at_base_set Z b

instance : smooth_vector_bundle 𝕜 F Z.fiber :=
{ total_space_mk_inducing := λ b, ⟨ begin refine le_antisymm _ (λ s h, _),
    { rw ←continuous_iff_le_induced,
      exact topological_fiber_bundle_core.continuous_total_space_mk ↑Z b, },
    { refine is_open_induced_iff.mpr ⟨(Z.local_triv_at b).source ∩ (Z.local_triv_at b) ⁻¹'
        ((Z.local_triv_at b).base_set ×ˢ s), (continuous_on_open_iff
        (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
        ((Z.local_triv_at b).open_base_set.prod h), _⟩,
      rw [preimage_inter, ←preimage_comp, function.comp],
      simp only [total_space_mk],
      refine ext_iff.mpr (λ a, ⟨λ ha, _, λ ha, ⟨Z.mem_base_set_at b, _⟩⟩),
      { simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply] at ha,
        exact ha.2.2, },
      { simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply],
        exact ⟨Z.mem_base_set_at b, ha⟩, } } end⟩,
  trivialization_atlas := set.range Z.local_triv,
  trivialization_at := Z.local_triv_at,
  mem_base_set_trivialization_at := Z.mem_base_set_at,
  trivialization_mem_atlas := λ b, ⟨Z.index_at b, rfl⟩,
  continuous_coord_change := begin
    classical,
    rintros _ ⟨i, rfl⟩ _ ⟨i', rfl⟩,
    refine ⟨Z.base_set i ∩ Z.base_set i', _, _,
      λ b, if h : b ∈ Z.base_set i ∩ Z.base_set i' then continuous_linear_equiv.equiv_of_inverse
        (Z.coord_change i i' b) (Z.coord_change i' i b) _ _ else continuous_linear_equiv.refl 𝕜 F,
      _, _⟩,
    { ext ⟨b, f⟩,
      simp },
    { ext ⟨b, f⟩,
      simp [and_comm] },
    { intro f,
      rw [Z.coord_change_comp _ _ _ _ ⟨h, h.1⟩, Z.coord_change_self _ _ h.1] },
    { intro f,
      rw [Z.coord_change_comp _ _ _ _ ⟨⟨h.2, h.1⟩, h.2⟩, Z.coord_change_self _ _ h.2] },
    { apply continuous_on.congr (Z.coord_change_continuous i i'),
      intros b hb,
      simp [hb],
      ext v,
      refl },
    { intros b hb v,
      have : b ∈ Z.base_set i ∩ Z.base_set (Z.index_at b) ∩ Z.base_set i',
      { simp only [base_set_at, local_triv_at_def, mem_inter_eq, mem_local_triv_at_base_set] at *,
        tauto },
      simp [hb, Z.coord_change_comp _ _ _ _ this] }
  end }

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity] lemma continuous_proj : continuous Z.proj :=
topological_fiber_bundle_core.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj :=
topological_fiber_bundle_core.is_open_map_proj Z

end smooth_vector_bundle_core

end

/-! ### Topological vector prebundle -/

section
variables [nondiscrete_normed_field 𝕜] [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_group F] [normed_space 𝕜 F] [topological_space B]
  [∀ x, topological_space (E x)]

open topological_space

/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphisms and hence vector bundle trivializations. -/
@[nolint has_inhabited_instance]
structure topological_vector_prebundle :=
(pretrivialization_atlas : set (smooth_vector_bundle.pretrivialization I I' F E))
(pretrivialization_at : B → smooth_vector_bundle.pretrivialization I I' F E)
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas)
(continuous_coord_change : ∀ e e' ∈ pretrivialization_atlas,
  continuous_transitions 𝕜 B F (e'.to_local_equiv.symm.trans e.to_local_equiv : _))
(total_space_mk_inducing : ∀ (b : B), inducing ((pretrivialization_at b) ∘ (total_space_mk b)))

namespace topological_vector_prebundle

variables {𝕜 E F}

/-- Natural identification of `topological_vector_prebundle` as a `topological_fiber_prebundle`. -/
def to_topological_fiber_prebundle (a : topological_vector_prebundle 𝕜 F E) :
  topological_fiber_prebundle F (proj E) :=
{ pretrivialization_atlas :=
    pretrivialization.to_fiber_bundle_pretrivialization '' a.pretrivialization_atlas,
  pretrivialization_at := λ x, (a.pretrivialization_at x).to_fiber_bundle_pretrivialization,
  pretrivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_triv_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    obtain ⟨s, hs, hs', ε, hε, heε⟩ := a.continuous_coord_change e he e' he',
    have H : e'.to_fiber_bundle_pretrivialization.to_local_equiv.target ∩
      (e'.to_fiber_bundle_pretrivialization.to_local_equiv.symm) ⁻¹'
      e.to_fiber_bundle_pretrivialization.to_local_equiv.source = s ×ˢ (univ : set F),
    { simpa using hs },
    rw H,
    have : continuous_on (λ p : B × F, (p.1, (ε p.1) p.2)) (s ×ˢ (univ : set F)),
    { apply continuous_on_fst.prod,
      exact is_bounded_bilinear_map_apply.continuous.comp_continuous_on
        (hε.prod_map continuous_on_id) },
    apply this.congr,
    rintros ⟨b, f⟩ ⟨hb : b ∈ s, -⟩,
    exact heε _ hb _,
  end,
  .. a }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : topological_vector_prebundle 𝕜 F E) :
  topological_space (total_space E) :=
a.to_topological_fiber_prebundle.total_space_topology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `smooth_vector_bundle.trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (a : topological_vector_prebundle 𝕜 F E)
  {e : smooth_vector_bundle.pretrivialization I I' F E} (he : e ∈ a.pretrivialization_atlas) :
  @smooth_vector_bundle.trivialization 𝕜 _ F E _ _ _ _ _ _ _ a.total_space_topology :=
begin
  letI := a.total_space_topology,
  exact { linear' := e.linear,
  ..a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas ⟨e, he, rfl⟩ }
end

variable (a : topological_vector_prebundle 𝕜 F E)

lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk b x ∈ (a.pretrivialization_at b).source :=
begin
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, proj],
  exact a.mem_base_pretrivialization_at b,
end

@[simp] lemma total_space_mk_preimage_source (b : B) :
  (total_space_mk b) ⁻¹' (a.pretrivialization_at b).source = univ :=
begin
  apply eq_univ_of_univ_subset,
  rw [(a.pretrivialization_at b).source_eq, ←preimage_comp, function.comp],
  simp only [proj],
  rw preimage_const_of_mem _,
  exact a.mem_base_pretrivialization_at b,
end

@[continuity] lemma continuous_total_space_mk (b : B) :
  @continuous _ _ _ a.total_space_topology (total_space_mk b) :=
begin
  letI := a.total_space_topology,
  let e := a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas b),
  rw e.to_local_homeomorph.continuous_iff_continuous_comp_left
    (a.total_space_mk_preimage_source b),
  exact continuous_iff_le_induced.mpr (le_antisymm_iff.mp (a.total_space_mk_inducing b).induced).1,
end

lemma inducing_total_space_mk_of_inducing_comp (b : B)
  (h : inducing ((a.pretrivialization_at b) ∘ (total_space_mk b))) :
  @inducing _ _ _ a.total_space_topology (total_space_mk b) :=
begin
  letI := a.total_space_topology,
  rw ←restrict_comp_cod_restrict (a.mem_trivialization_at_source b) at h,
  apply inducing.of_cod_restrict (a.mem_trivialization_at_source b),
  refine inducing_of_inducing_compose _ (continuous_on_iff_continuous_restrict.mp
    (a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas b)).continuous_to_fun) h,
  exact (a.continuous_total_space_mk b).cod_restrict (a.mem_trivialization_at_source b),
end

/-- Make a `smooth_vector_bundle` from a `topological_vector_prebundle`.  Concretely this means
that, given a `topological_vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`topological_vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def to_smooth_vector_bundle :
  @smooth_vector_bundle 𝕜 _ F E _ _ _ _ _ _ a.total_space_topology _ :=
{ total_space_mk_inducing := λ b, a.inducing_total_space_mk_of_inducing_comp b
    (a.total_space_mk_inducing b),
  trivialization_atlas := {e | ∃ e₀ (he₀ : e₀ ∈ a.pretrivialization_atlas),
    e = a.trivialization_of_mem_pretrivialization_atlas he₀},
  trivialization_at := λ x, a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas x),
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at,
  trivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_coord_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    exact a.continuous_coord_change e' he' e he,
  end }

end topological_vector_prebundle

end

/-! ### Direct sum of two vector bundles over the same base -/

namespace smooth_vector_bundle

section defs
variables (E₁ : B → Type*) (E₂ : B → Type*)
variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]

/-- Equip the total space of the fibrewise product of two topological vector bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `(total_space E₁) × (total_space E₂)`. -/
instance prod.topological_space :
  topological_space (total_space (E₁ ×ᵇ E₂)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space ((total_space E₁) × (total_space E₂)))

/-- The diagonal map from the total space of the fibrewise product of two topological vector bundles
`E₁`, `E₂` into `(total_space E₁) × (total_space E₂)` is `inducing`. -/
lemma prod.inducing_diag : inducing
  (λ p, (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
    total_space (E₁ ×ᵇ E₂) → (total_space E₁) × (total_space E₂)) :=
⟨rfl⟩

end defs

variables [nondiscrete_normed_field 𝕜] [topological_space B]

variables (F₁ : Type*) [normed_group F₁] [normed_space 𝕜 F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]
  [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]

variables (F₂ : Type*) [normed_group F₂] [normed_space 𝕜 F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]
  [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]

namespace trivialization
variables (e₁ : trivialization 𝕜 F₁ E₁) (e₂ : trivialization 𝕜 F₂ E₂)
include e₁ e₂
variables {𝕜 F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `smooth_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def prod.to_fun' : total_space (E₁ ×ᵇ E₂) → B × (F₁ × F₂) :=
λ ⟨x, v₁, v₂⟩, ⟨x, (e₁ ⟨x, v₁⟩).2, (e₂ ⟨x, v₂⟩).2⟩

variables {e₁ e₂}

lemma prod.continuous_to_fun :
  continuous_on (prod.to_fun' e₁ e₂) (proj (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :=
begin
  let f₁ : total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂ :=
    λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)),
  let f₂ : total_space E₁ × total_space E₂ → (B × F₁) × (B × F₂) := λ p, ⟨e₁ p.1, e₂ p.2⟩,
  let f₃ : (B × F₁) × (B × F₂) → B × F₁ × F₂ := λ p, ⟨p.1.1, p.1.2, p.2.2⟩,
  have hf₁ : continuous f₁ := (prod.inducing_diag E₁ E₂).continuous,
  have hf₂ : continuous_on f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.to_local_homeomorph.continuous_on.prod_map e₂.to_local_homeomorph.continuous_on,
  have hf₃ : continuous f₃ :=
    (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd),
  refine ((hf₃.comp_continuous_on hf₂).comp hf₁.continuous_on _).congr _,
  { rw [e₁.source_eq, e₂.source_eq],
    exact maps_to_preimage _ _ },
  rintros ⟨b, v₁, v₂⟩ ⟨hb₁, hb₂⟩,
  simp only [prod.to_fun', prod.mk.inj_iff, eq_self_iff_true, and_true],
  rw e₁.coe_fst,
  rw [e₁.source_eq, mem_preimage],
  exact hb₁,
end

variables (e₁ e₂)

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [smooth_vector_bundle 𝕜 F₁ E₁] [smooth_vector_bundle 𝕜 F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `smooth_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def prod.inv_fun' (p : B × (F₁ × F₂)) : total_space (E₁ ×ᵇ E₂) :=
begin
  obtain ⟨x, w₁, w₂⟩ := p,
  refine ⟨x, _, _⟩,
  { by_cases h : x ∈ e₁.base_set,
    { exact (e₁.continuous_linear_equiv_at x h).symm w₁ },
    { exact 0 } },
  { by_cases h : x ∈ e₂.base_set,
    { exact (e₂.continuous_linear_equiv_at x h).symm w₂ },
    { exact 0 } },
end

variables {e₁ e₂}

lemma prod.inv_fun'_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (w₁ : F₁) (w₂ : F₂) :
  prod.inv_fun' e₁ e₂ ⟨x, w₁, w₂⟩
  = ⟨x, ((e₁.continuous_linear_equiv_at x hx₁).symm w₁,
    (e₂.continuous_linear_equiv_at x hx₂).symm w₂)⟩ :=
begin
  dsimp [prod.inv_fun'],
  rw [dif_pos, dif_pos],
end

lemma prod.left_inv {x : total_space (E₁ ×ᵇ E₂)}
  (h : x ∈ proj (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :
  prod.inv_fun' e₁ e₂ (prod.to_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, v₁, v₂⟩ := x,
  simp only [prod.to_fun', prod.inv_fun', sigma.mk.inj_iff, true_and, eq_self_iff_true,
    prod.mk.inj_iff, heq_iff_eq],
  split,
  { rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1,
      continuous_linear_equiv.symm_apply_apply] },
  { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
      continuous_linear_equiv.symm_apply_apply] },
end

lemma prod.right_inv {x : B × F₁ × F₂}
  (h : x ∈ (e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))) :
  prod.to_fun' e₁ e₂ (prod.inv_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, w₁, w₂⟩ := x,
  obtain ⟨h, -⟩ := h,
  dsimp only [prod.to_fun', prod.inv_fun'],
  simp only [prod.mk.inj_iff, eq_self_iff_true, true_and],
  split,
  { rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1,
      continuous_linear_equiv.apply_symm_apply] },
  { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
      continuous_linear_equiv.apply_symm_apply] },
end

lemma prod.continuous_inv_fun :
  continuous_on (prod.inv_fun' e₁ e₂) ((e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))) :=
begin
  rw (prod.inducing_diag E₁ E₂).continuous_on_iff,
  suffices : continuous_on (λ p : B × F₁ × F₂,
    (e₁.to_local_homeomorph.symm ⟨p.1, p.2.1⟩, e₂.to_local_homeomorph.symm ⟨p.1, p.2.2⟩))
    ((e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))),
  { refine this.congr _,
    rintros ⟨b, v₁, v₂⟩ ⟨⟨h₁, h₂⟩, _⟩,
    dsimp at ⊢ h₁ h₂,
    rw [prod.inv_fun'_apply h₁ h₂, e₁.symm_apply_eq_mk_continuous_linear_equiv_at_symm b h₁,
      e₂.symm_apply_eq_mk_continuous_linear_equiv_at_symm b h₂] },
  have H₁ : continuous (λ p : B × F₁ × F₂, ((p.1, p.2.1), (p.1, p.2.2))) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd),
  have H₂ := e₁.to_local_homeomorph.symm.continuous_on.prod_map
    e₂.to_local_homeomorph.symm.continuous_on,
  refine H₂.comp H₁.continuous_on (λ x h, ⟨_, _⟩),
  { dsimp,
    rw e₁.target_eq,
    exact ⟨h.1.1, mem_univ _⟩ },
  { dsimp,
    rw e₂.target_eq,
    exact ⟨h.1.2, mem_univ _⟩ }
end

variables (e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
def prod : trivialization 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ to_fun := prod.to_fun' e₁ e₂,
  inv_fun := prod.inv_fun' e₁ e₂,
  source := (proj (λ x, E₁ x × E₂ x)) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ × F₂)),
  map_source' := λ ⟨x, v₁, v₂⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, w₁, w₂⟩ h, h.1,
  left_inv' := λ x, prod.left_inv,
  right_inv' := λ x, prod.right_inv,
  open_source := begin
    refine (e₁.open_base_set.inter e₂.open_base_set).preimage _,
    have : continuous (proj E₁) := continuous_proj 𝕜 B F₁,
    exact this.comp (continuous_fst.comp (prod.inducing_diag E₁ E₂).continuous),
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  continuous_to_fun := prod.continuous_to_fun,
  continuous_inv_fun := prod.continuous_inv_fun,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, v₁, v₂⟩ h, rfl,
  linear' := λ x ⟨h₁, h₂⟩,
  { map_add := λ ⟨v₁, v₂⟩ ⟨v₁', v₂'⟩,
      congr_arg2 prod.mk ((e₁.linear x h₁).map_add v₁ v₁') ((e₂.linear x h₂).map_add v₂ v₂'),
    map_smul := λ c ⟨v₁, v₂⟩,
      congr_arg2 prod.mk ((e₁.linear x h₁).map_smul c v₁) ((e₂.linear x h₂).map_smul c v₂), } }

@[simp] lemma base_set_prod : (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

variables {e₁ e₂}

lemma prod_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (v₁ : E₁ x)
  (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at x hx₁ v₁, e₂.continuous_linear_equiv_at x hx₂ v₂⟩ :=
rfl

lemma prod_symm_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (w₁ : F₁) (w₂ : F₂) :
  (prod e₁ e₂).to_local_equiv.symm (x, (w₁, w₂))
  = ⟨x, ((e₁.continuous_linear_equiv_at x hx₁).symm w₁,
      (e₂.continuous_linear_equiv_at x hx₂).symm w₂)⟩ :=
prod.inv_fun'_apply hx₁ hx₂ w₁ w₂

end trivialization

open trivialization

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [smooth_vector_bundle 𝕜 F₁ E₁] [smooth_vector_bundle 𝕜 F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.smooth_vector_bundle :
  smooth_vector_bundle 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ total_space_mk_inducing := λ b,
  begin
    rw (prod.inducing_diag E₁ E₂).inducing_iff,
    exact (total_space_mk_inducing 𝕜 F₁ E₁ b).prod_mk (total_space_mk_inducing 𝕜 F₂ E₂ b),
  end,
  trivialization_atlas := (λ (p : trivialization 𝕜 F₁ E₁ × trivialization 𝕜 F₂ E₂), p.1.prod p.2) ''
    (trivialization_atlas I I' F₁ E₁ ×ˢ trivialization_atlas I I' F₂ E₂),
  trivialization_at := λ b, (trivialization_at 𝕜 F₁ E₁ b).prod (trivialization_at 𝕜 F₂ E₂ b),
  mem_base_set_trivialization_at :=
    λ b, ⟨mem_base_set_trivialization_at 𝕜 F₁ E₁ b, mem_base_set_trivialization_at 𝕜 F₂ E₂ b⟩,
  trivialization_mem_atlas := λ b,
    ⟨(_, _), ⟨trivialization_mem_atlas 𝕜 F₁ E₁ b, trivialization_mem_atlas 𝕜 F₂ E₂ b⟩, rfl⟩,
  continuous_coord_change := begin
    rintros _ ⟨⟨e₁, e₂⟩, ⟨he₁, he₂⟩, rfl⟩ _ ⟨⟨e'₁, e'₂⟩, ⟨he'₁, he'₂⟩, rfl⟩,
    let s := e₁.base_set ∩ e'₁.base_set,
    let t := e₂.base_set ∩ e'₂.base_set,
    let ε := coord_change he₁ he'₁,
    let η := coord_change he₂ he'₂,
    have fact : (s ∩ t) ×ˢ (univ : set $ F₁ × F₂) =
        (e₁.base_set ∩ e₂.base_set ∩  (e'₁.base_set ∩ e'₂.base_set)) ×ˢ (univ : set $ F₁ × F₂),
      by mfld_set_tac,
    refine ⟨s ∩ t, _, _, λ b, (ε b).prod (η b), _, _⟩,
    { rw fact,
      apply topological_fiber_bundle.trivialization.symm_trans_source_eq },
    { rw fact,
      apply topological_fiber_bundle.trivialization.symm_trans_target_eq },
    { have hε := (continuous_on_coord_change he₁ he'₁).mono (inter_subset_left s t),
      have hη := (continuous_on_coord_change he₂ he'₂).mono (inter_subset_right s t),
      exact hε.prod_map_equivL 𝕜 hη },
    { rintros b ⟨hbs, hbt⟩ ⟨u, v⟩,
      have h : (e₁.prod e₂).to_local_homeomorph.symm _ = _ := prod_symm_apply hbs.1 hbt.1 u v,
      simp only [ε, η, h, prod_apply hbs.2 hbt.2,
        ← comp_continuous_linear_equiv_at_eq_coord_change he₁ he'₁ hbs,
        ← comp_continuous_linear_equiv_at_eq_coord_change he₂ he'₂ hbt,
        eq_self_iff_true, function.comp_app, local_equiv.coe_trans, local_homeomorph.coe_coe,
        local_homeomorph.coe_coe_symm, prod.mk.inj_iff,
        smooth_vector_bundle.trivialization.coe_coe, true_and,
        continuous_linear_equiv.prod_apply, continuous_linear_equiv.trans_apply] },
  end }

variables {𝕜 F₁ E₁ F₂ E₂}

@[simp] lemma trivialization.continuous_linear_equiv_at_prod {e₁ : trivialization 𝕜 F₁ E₁}
  {e₂ : trivialization 𝕜 F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) :
  (e₁.prod e₂).continuous_linear_equiv_at x ⟨hx₁, hx₂⟩
  = (e₁.continuous_linear_equiv_at x hx₁).prod (e₂.continuous_linear_equiv_at x hx₂) :=
begin
  ext1,
  funext v,
  obtain ⟨v₁, v₂⟩ := v,
  rw [(e₁.prod e₂).continuous_linear_equiv_at_apply, trivialization.prod],
  exact congr_arg prod.snd (prod_apply hx₁ hx₂ v₁ v₂),
end

end smooth_vector_bundle
