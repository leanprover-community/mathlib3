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

variables {𝕜 : Type*} {B V V' V'' H H' H'' : Type*}

variables [nondiscrete_normed_field 𝕜]
variables [normed_group V] [normed_space 𝕜 V] [normed_group V'] [normed_space 𝕜 V']
variables [normed_group V''] [normed_space 𝕜 V'']
variables [topological_space H] [topological_space H'] [topological_space H'']
variables (I : model_with_corners 𝕜 V H) (I' : model_with_corners 𝕜 V' H')
variables (I'' : model_with_corners 𝕜 V'' H'')
variables (F F' : Type*) (E E' : B → Type*)
variables [∀ x, normed_group (E x)] [∀ x, normed_space 𝕜 (E x)]
variables [∀ x, normed_group (E' x)] [∀ x, normed_space 𝕜 (E' x)]
variables [normed_group F] [normed_space 𝕜 F]
variables [normed_group F'] [normed_space 𝕜 F']
variables [topological_space B] [charted_space H B] -- [smooth_manifold_with_corners I B]

variables [topological_space (total_space E)] [charted_space H' (total_space E)]
variables [topological_space (total_space E')] [charted_space H'' (total_space E')]
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

protected lemma smooth_on_symm' :
  smooth_on (I.prod 𝓘(𝕜, F)) I' e.to_local_homeomorph.symm e.target :=
e.smooth_on_inv_fun

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_equiv = e := rfl
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

lemma open_target : is_open e.target :=
by { rw e.target_eq, exact e.open_base_set.prod is_open_univ }

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

lemma proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  (e.to_local_homeomorph.symm (b, x)).proj  = b :=
e.to_topological.proj_symm_apply' hx

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_topological.apply_symm_apply' hx

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e.source) :
  e.to_local_homeomorph.symm (e x) = x :=
e.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_coe_proj {x : B} {y : F} (h : x ∈ e.base_set) :
  (e.to_local_homeomorph.symm (x, y)).1 = x := e.proj_symm_apply' h

/-- A fiberwise inverse to `e`. The function `F → E x` that induces a local inverse
  `B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (e : trivialization I I' F E) (b : B) (y : F) : E b :=
e.to_topological.symm b y

lemma symm_apply (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.to_local_homeomorph.symm (b, y)).2 :=
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

lemma smooth_on_symm (e : trivialization I I' F E) :
  smooth_on (I.prod 𝓘(𝕜, F)) I' (λ z : B × F, total_space_mk z.1 (e.symm z.1 z.2))
    (e.base_set ×ˢ (univ : set F)) :=
begin
  have : ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : set F)),
    total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z,
  { rintro x ⟨hx : x.1 ∈ e.base_set, _⟩, simp_rw [e.mk_symm hx, prod.mk.eta] },
  refine cont_mdiff_on.congr _ this,
  rw [← e.target_eq],
  exact e.smooth_on_symm'
end

/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coord_change (e e' : trivialization I I' F E) (b : B) : F ≃L[𝕜] F :=
e.to_topological.coord_change e'.to_topological b

lemma coord_change_apply (e e' : trivialization I I' F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change e e' b y = (e' (total_space_mk b (e.symm b y))).2 :=
congr_arg (λ f, linear_equiv.to_fun f y) (dif_pos hb)

lemma mk_coord_change (e e' : trivialization I I' F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  (b, coord_change e e' b y) = e' (total_space_mk b (e.symm b y)) :=
begin
  ext,
  { rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1],
    rw [e.proj_symm_apply' hb.1], exact hb.2 },
  { exact e.coord_change_apply e' hb y }
end

/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
lemma coord_change_apply' (e e' : trivialization I I' F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change e e' b y = (e' (e.to_local_homeomorph.symm (b, y))).2 :=
by rw [e.coord_change_apply e' hb, e.mk_symm hb.1]

end smooth_vector_bundle.trivialization

open smooth_vector_bundle

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`smooth_vector_bundle 𝕜 F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class smooth_vector_bundle :=
-- does this also need to induce the manifold structure?
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization I I' F E))
(trivialization_at [] : B → trivialization I I' F E)
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)
(smooth_on_coord_change [] : ∀ (e e' ∈ trivialization_atlas), smooth_on I 𝓘(𝕜, F →L[𝕜] F)
  (λ b, trivialization.coord_change e e' b : B → F →L[𝕜] F) (e.base_set ∩ e'.base_set))

export smooth_vector_bundle (trivialization_atlas trivialization_at
  mem_base_set_trivialization_at trivialization_mem_atlas smooth_on_coord_change)

variable [smooth_vector_bundle I I' F E]

namespace smooth_vector_bundle

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at I I' F E z.1).source :=
by { rw smooth_fiber_bundle.trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {𝕜 I I' F E}

-- dangerous as instance
def to_topological : topological_vector_bundle 𝕜 F E :=
{ total_space_mk_inducing := total_space_mk_inducing I I' F E,
  trivialization_atlas := trivialization.to_topological '' trivialization_atlas I I' F E,
  trivialization_at := λ b, (trivialization_at I I' F E b).to_topological,
  mem_base_set_trivialization_at := mem_base_set_trivialization_at I I' F E,
  trivialization_mem_atlas := λ b, mem_image_of_mem _ (trivialization_mem_atlas I I' F E b),
  continuous_on_coord_change := by { rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    exact (smooth_on_coord_change e he e' he').continuous_on } }

section

instance {B : Type*} {F : Type*} [normed_group F] (b : B) :
  normed_group (bundle.trivial B F b) := ‹normed_group F›

instance {B : Type*} {F : Type*} [normed_group F] [normed_space 𝕜 F] (b : B) :
  normed_space 𝕜 (bundle.trivial B F b) := ‹normed_space 𝕜 F›

instance : charted_space (model_prod H F) (total_space (trivial B F)) :=
sorry

end

variables (B F)
namespace trivial_smooth_vector_bundle

/-- Local trivialization for trivial bundle. -/
def trivialization : trivialization I (I.prod 𝓘(𝕜, F)) F (bundle.trivial B F) :=
{ smooth_on_to_fun := sorry,
  smooth_on_inv_fun := sorry,
  ..topological_vector_bundle.trivial_topological_vector_bundle.trivialization 𝕜 B F }


lemma trivialization.coord_change (b : B) :
  (trivialization B I F).coord_change (trivialization B I F) b = continuous_linear_equiv.refl 𝕜 F :=
topological_vector_bundle.trivial_topological_vector_bundle.trivialization.coord_change 𝕜 B F b

instance trivial_bundle.smooth_vector_bundle :
  smooth_vector_bundle I (I.prod 𝓘(𝕜, F)) F (bundle.trivial B F) :=
{ trivialization_atlas := {trivial_smooth_vector_bundle.trivialization B I F},
  trivialization_at := λ x, trivial_smooth_vector_bundle.trivialization B I F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
      total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
      trivial.topological_space, this, induced_id],
  end⟩,
  smooth_on_coord_change := begin
    intros e he e' he',
    rw [mem_singleton_iff.mp he, mem_singleton_iff.mp he'],
    simp_rw [trivialization.coord_change],
    exact smooth_on_const
  end }

end trivial_smooth_vector_bundle

/- Not registered as an instance because of a metavariable. -/
lemma is_smooth_vector_bundle_is_smooth_fiber_bundle :
  is_smooth_fiber_bundle I 𝓘(𝕜, F) I' F (@total_space.proj B E) :=
λ x, ⟨(trivialization_at I I' F E x).to_fiber_bundle, mem_base_set_trivialization_at I I' F E x⟩


variables {B F}

include 𝕜 F

lemma smooth_total_space_mk (x : B) : smooth 𝓘(𝕜, E x) I' (@total_space_mk B E x) :=
sorry

variables (𝕜 B F)

lemma smooth_proj : smooth I' I (@total_space.proj B E) :=
is_smooth_fiber_bundle.smooth_proj (is_smooth_vector_bundle_is_smooth_fiber_bundle B I I' F)

end smooth_vector_bundle
