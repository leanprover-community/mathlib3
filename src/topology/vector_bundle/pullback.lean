/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Floris van Doorn
-/

import topology.vector_bundle.basic

/-!
# Pullbacks of fiber and vector bundles

We construct the pullback bundle for a map `f : B' → B` whose fiber map is given simply by
`f *ᵖ E = E ∘ f` (the type synonym is there for typeclass instance problems).
-/

noncomputable theory

open bundle set topological_space
open_locale classical bundle

variables (R 𝕜 : Type*) {B : Type*} (F : Type*) (E E' : B → Type*)
variables {B' : Type*} (f : B' → B)

instance [∀ (x : B), topological_space (E' x)] : ∀ (x : B'), topological_space ((f *ᵖ E') x) :=
by delta_instance bundle.pullback
instance [∀ (x : B), add_comm_monoid (E' x)] : ∀ (x : B'), add_comm_monoid ((f *ᵖ E') x) :=
by delta_instance bundle.pullback
instance [semiring R] [∀ (x : B), add_comm_monoid (E' x)] [∀ x, module R (E' x)] :
  ∀ (x : B'), module R ((f *ᵖ E') x) :=
by delta_instance bundle.pullback

variables [topological_space B'] [topological_space (total_space E)]

/-- Definition of `pullback.total_space.topological_space`, which we make irreducible. -/
@[irreducible] def pullback_topology : topological_space (total_space (f *ᵖ E)) :=
induced total_space.proj ‹topological_space B'› ⊓
induced (pullback.lift f) ‹topological_space (total_space E)›

/-- The topology on the total space of a pullback bundle is the coarsest topology for which both
the projections to the base and the map to the original bundle are continuous. -/
instance pullback.total_space.topological_space :
  topological_space (total_space (f *ᵖ E)) :=
pullback_topology E f

lemma pullback.continuous_proj (f : B' → B) :
  continuous (@total_space.proj _ (f *ᵖ E)) :=
begin
  rw [continuous_iff_le_induced, pullback.total_space.topological_space, pullback_topology],
  exact inf_le_left,
end

lemma pullback.continuous_lift (f : B' → B) :
  continuous (@pullback.lift B E B' f) :=
begin
  rw [continuous_iff_le_induced, pullback.total_space.topological_space, pullback_topology],
  exact inf_le_right,
end

lemma inducing_pullback_total_space_embedding (f : B' → B) :
  inducing (@pullback_total_space_embedding B E B' f) :=
begin
  constructor,
  simp_rw [prod.topological_space, induced_inf, induced_compose,
    pullback.total_space.topological_space, pullback_topology],
  refl
end

section fiber_bundle
variables (F) [topological_space F] [topological_space B]

lemma pullback.continuous_total_space_mk [∀ x, topological_space (E x)]
  [fiber_bundle F E] {f : B' → B} {x : B'} :
  continuous (@total_space_mk _ (f *ᵖ E) x) :=
begin
  simp only [continuous_iff_le_induced, pullback.total_space.topological_space, induced_compose,
    induced_inf, function.comp, total_space_mk, total_space.proj, induced_const, top_inf_eq,
    pullback_topology],
  exact le_of_eq (fiber_bundle.total_space_mk_inducing F E (f x)).induced,
end

variables {E F} [∀ b, has_zero (E b)] {K : Type*} [continuous_map_class K B' B]

/-- A fiber bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
def trivialization.pullback (e : trivialization F (π E)) (f : K) :
  trivialization F (π ((f : B' → B) *ᵖ E)) :=
{ to_fun := λ z, (z.proj, (e (pullback.lift f z)).2),
  inv_fun := λ y, @total_space_mk _ (f *ᵖ E) y.1 (e.symm (f y.1) y.2),
  source := pullback.lift f ⁻¹' e.source,
  base_set := f ⁻¹' e.base_set,
  target := (f ⁻¹' e.base_set) ×ˢ univ,
  map_source' := λ x h, by { simp_rw [e.source_eq, mem_preimage, pullback.proj_lift] at h,
    simp_rw [prod_mk_mem_set_prod_eq, mem_univ, and_true, mem_preimage, h] },
  map_target' := λ y h, by { rw [mem_prod, mem_preimage] at h,
    simp_rw [e.source_eq, mem_preimage, pullback.proj_lift, h.1] },
  left_inv' := λ x h, by { simp_rw [mem_preimage, e.mem_source, pullback.proj_lift] at h,
    simp_rw [pullback.lift, e.symm_apply_apply_mk h, total_space.eta] },
  right_inv' := λ x h, by { simp_rw [mem_prod, mem_preimage, mem_univ, and_true] at h,
    simp_rw [total_space.proj_mk, pullback.lift_mk, e.apply_mk_symm h, prod.mk.eta] },
  open_source := by { simp_rw [e.source_eq, ← preimage_comp], exact ((map_continuous f).comp $
    pullback.continuous_proj E f).is_open_preimage _ e.open_base_set },
  open_target := ((map_continuous f).is_open_preimage _ e.open_base_set).prod is_open_univ,
  open_base_set := (map_continuous f).is_open_preimage _ e.open_base_set,
  continuous_to_fun := (pullback.continuous_proj E f).continuous_on.prod
    (continuous_snd.comp_continuous_on $
    e.continuous_on.comp (pullback.continuous_lift E f).continuous_on subset.rfl),
  continuous_inv_fun := begin
    dsimp only,
    simp_rw [(inducing_pullback_total_space_embedding E f).continuous_on_iff, function.comp,
      pullback_total_space_embedding, total_space.proj_mk],
    dsimp only [total_space.proj_mk],
    refine continuous_on_fst.prod (e.continuous_on_symm.comp
      ((map_continuous f).prod_map continuous_id).continuous_on subset.rfl)
  end,
  source_eq := by { dsimp only, rw e.source_eq, refl, },
  target_eq := rfl,
  proj_to_fun := λ y h, rfl }

instance fiber_bundle.pullback [∀ x, topological_space (E x)]
  [fiber_bundle F E] (f : K) : fiber_bundle F ((f : B' → B) *ᵖ E) :=
{ total_space_mk_inducing := λ x, inducing_of_inducing_compose
    (pullback.continuous_total_space_mk F E) (pullback.continuous_lift E f)
    (total_space_mk_inducing F E (f x)),
  trivialization_atlas :=
    {ef | ∃ (e : trivialization F (π E)) [mem_trivialization_atlas e], ef = e.pullback f},
  trivialization_at := λ x, (trivialization_at F E (f x)).pullback f,
  mem_base_set_trivialization_at := λ x, mem_base_set_trivialization_at F E (f x),
  trivialization_mem_atlas := λ x, ⟨trivialization_at F E (f x), by apply_instance, rfl⟩ }

end fiber_bundle

section vector_bundle
variables (F) [nontrivially_normed_field 𝕜]
  [normed_add_comm_group F] [normed_space 𝕜 F] [topological_space B]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]

variables {E F} {K : Type*} [continuous_map_class K B' B]

instance trivialization.pullback_linear (e : trivialization F (π E)) [e.is_linear 𝕜] (f : K) :
  (@trivialization.pullback _ _ _ B' _ _ _ _ _ _ _ e f).is_linear 𝕜 :=
{ linear := λ x h, e.linear 𝕜 h }

instance vector_bundle.pullback [∀ x, topological_space (E x)]
  [fiber_bundle F E] [vector_bundle 𝕜 F E] (f : K) : vector_bundle 𝕜 F ((f : B' → B) *ᵖ E) :=
{ trivialization_linear' := begin
    rintro _ ⟨e, he, rfl⟩, resetI,
    apply_instance,
  end,
  continuous_on_coord_change' := begin
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩, resetI,
    refine ((continuous_on_coord_change 𝕜 e e').comp (map_continuous f).continuous_on
      (λ b hb, hb)).congr _,
    rintro b (hb : f b ∈ e.base_set ∩ e'.base_set), ext v,
    show ((e.pullback f).coord_changeL 𝕜 (e'.pullback f) b) v = (e.coord_changeL 𝕜 e' (f b)) v,
    rw [e.coord_changeL_apply e' hb, (e.pullback f).coord_changeL_apply' _],
    exacts [rfl, hb]
  end }

end vector_bundle
