/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.is_locally_homeomorph
import topology.fiber_bundle.basic
import topology.locally_constant.basic
import set_theory.cardinal.basic
import topology.homotopy.basic

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `is_evenly_covered f x I`: A point `x` is evenly coverd by `f : E → X` with fiber `I` if `I` is
  discrete and there is a `trivialization` of `f` at `x` with fiber `I`.
* `is_covering_map f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/

open_locale bundle

variables {E X : Type*} [topological_space E] [topological_space X] (f : E → X) (s : set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def is_evenly_covered (x : X) (I : Type*) [topological_space I] :=
discrete_topology I ∧ ∃ t : trivialization I f, x ∈ t.base_set

namespace is_evenly_covered

variables {f}

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def to_trivialization {x : X} {I : Type*} [topological_space I]
  (h : is_evenly_covered f x I) : trivialization (f ⁻¹' {x}) f :=
(classical.some h.2).trans_fiber_homeomorph ((classical.some h.2).preimage_singleton_homeomorph
  (classical.some_spec h.2)).symm

lemma mem_to_trivialization_base_set {x : X} {I : Type*} [topological_space I]
  (h : is_evenly_covered f x I) : x ∈ h.to_trivialization.base_set :=
classical.some_spec h.2

lemma to_trivialization_apply {x : E} {I : Type*} [topological_space I]
  (h : is_evenly_covered f (f x) I) : (h.to_trivialization x).2 = ⟨x, rfl⟩ :=
let e := classical.some h.2, h := classical.some_spec h.2, he := e.mk_proj_snd' h in
  subtype.ext ((e.to_local_equiv.eq_symm_apply (e.mem_source.mpr h)
    (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr he.symm).symm

protected lemma continuous_at {x : E} {I : Type*} [topological_space I]
  (h : is_evenly_covered f (f x) I) : continuous_at f x :=
let e := h.to_trivialization in
  e.continuous_at_proj (e.mem_source.mpr (mem_to_trivialization_base_set h))

lemma to_is_evenly_covered_preimage {x : X} {I : Type*} [topological_space I]
  (h : is_evenly_covered f x I) : is_evenly_covered f x (f ⁻¹' {x}) :=
let ⟨h1, h2⟩ := h in by exactI ⟨((classical.some h2).preimage_singleton_homeomorph
  (classical.some_spec h2)).embedding.discrete_topology, _, h.mem_to_trivialization_base_set⟩

end is_evenly_covered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def is_covering_map_on :=
∀ x ∈ s, is_evenly_covered f x (f ⁻¹' {x})

namespace is_covering_map_on

lemma mk (F : X → Type*) [Π x, topological_space (F x)] [hF : Π x, discrete_topology (F x)]
  (e : Π x ∈ s, trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).base_set) :
  is_covering_map_on f s :=
λ x hx, is_evenly_covered.to_is_evenly_covered_preimage ⟨hF x, e x hx, h x hx⟩

variables {f} {s}

protected lemma continuous_at (hf : is_covering_map_on f s) {x : E} (hx : f x ∈ s) :
  continuous_at f x :=
(hf (f x) hx).continuous_at

protected lemma continuous_on (hf : is_covering_map_on f s) : continuous_on f (f ⁻¹' s) :=
continuous_at.continuous_on (λ x, hf.continuous_at)

protected lemma is_locally_homeomorph_on (hf : is_covering_map_on f s) :
  is_locally_homeomorph_on f (f ⁻¹' s) :=
begin
  refine is_locally_homeomorph_on.mk f (f ⁻¹' s) (λ x hx, _),
  let e := (hf (f x) hx).to_trivialization,
  have h := (hf (f x) hx).mem_to_trivialization_base_set,
  let he := e.mem_source.2 h,
  refine ⟨e.to_local_homeomorph.trans
  { to_fun := λ p, p.1,
    inv_fun := λ p, ⟨p, x, rfl⟩,
    source := e.base_set ×ˢ ({⟨x, rfl⟩} : set (f ⁻¹' {f x})),
    target := e.base_set,
    open_source := e.open_base_set.prod (singletons_open_iff_discrete.2 (hf (f x) hx).1 ⟨x, rfl⟩),
    open_target := e.open_base_set,
    map_source' := λ p, and.left,
    map_target' := λ p hp, ⟨hp, rfl⟩,
    left_inv' := λ p hp, prod.ext rfl hp.2.symm,
    right_inv' := λ p hp, rfl,
    continuous_to_fun := continuous_fst.continuous_on,
    continuous_inv_fun := (continuous_id'.prod_mk continuous_const).continuous_on },
    ⟨he, by rwa [e.to_local_homeomorph.symm_symm, e.proj_to_fun x he],
      (hf (f x) hx).to_trivialization_apply⟩, λ p h, (e.proj_to_fun p h.1).symm⟩,
end

end is_covering_map_on

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def is_covering_map :=
∀ x, is_evenly_covered f x (f ⁻¹' {x})

variables {f}

lemma is_covering_map_iff_is_covering_map_on_univ :
  is_covering_map f ↔ is_covering_map_on f set.univ :=
by simp only [is_covering_map, is_covering_map_on, set.mem_univ, forall_true_left]

protected lemma is_covering_map.is_covering_map_on (hf : is_covering_map f) :
  is_covering_map_on f set.univ :=
is_covering_map_iff_is_covering_map_on_univ.mp hf

variables (f)

namespace is_covering_map

lemma mk (F : X → Type*) [Π x, topological_space (F x)] [hF : Π x, discrete_topology (F x)]
  (e : Π x, trivialization (F x) f) (h : ∀ x, x ∈ (e x).base_set) : is_covering_map f :=
is_covering_map_iff_is_covering_map_on_univ.mpr
  (is_covering_map_on.mk f set.univ F (λ x hx, e x) (λ x hx, h x))

variables {f}

protected lemma continuous (hf : is_covering_map f) : continuous f :=
continuous_iff_continuous_on_univ.mpr hf.is_covering_map_on.continuous_on

protected lemma is_locally_homeomorph (hf : is_covering_map f) : is_locally_homeomorph f :=
is_locally_homeomorph_iff_is_locally_homeomorph_on_univ.mpr
  hf.is_covering_map_on.is_locally_homeomorph_on

protected lemma is_open_map (hf : is_covering_map f) : is_open_map f :=
hf.is_locally_homeomorph.is_open_map

protected lemma quotient_map (hf : is_covering_map f) (hf' : function.surjective f) :
  quotient_map f :=
hf.is_open_map.to_quotient_map hf.continuous hf'

noncomputable def to_homeomorph (hf : is_covering_map f)
  (h : function.bijective f) : homeomorph E X :=
homeomorph.homeomorph_of_continuous_open (equiv.of_bijective f h) hf.continuous hf.is_open_map

open_locale cardinal

lemma is_locally_constant_card (hf : is_covering_map f) :
  is_locally_constant (λ x, #(f ⁻¹' {x})) :=
(is_locally_constant.iff_exists_open _).2 $ λ x, let ⟨t, ht⟩ := (hf x).2 in
  ⟨_, t.open_base_set, ht, λ y hy, (t.preimage_singleton_homeomorph hy).to_equiv.cardinal_eq⟩

end is_covering_map

variables {f}

protected lemma is_fiber_bundle.is_covering_map {F : Type*} [topological_space F]
  [discrete_topology F] (hf : ∀ x : X, ∃ e : trivialization F f, x ∈ e.base_set) :
  is_covering_map f :=
is_covering_map.mk f (λ x, F) (λ x, classical.some (hf x)) (λ x, classical.some_spec (hf x))

open_locale unit_interval

lemma clopen_set_intersect_connected_components_whole_set (Y: Type*) [topological_space Y]
  (S : set Y) (hS : is_clopen S) (w : ∀ x : Y, ∃ y ∈ connected_component x, y ∈ S) :
  S = set.univ :=
set.eq_univ_of_forall $ λ x, let ⟨y, hy, h⟩ := w x in
  hS.connected_component_subset h (connected_component_eq hy ▸ mem_connected_component)

open_locale topological_space

lemma is_open_inter_of_coe_preim {X : Type*} [topological_space X] (s t : set X) (hs : is_open s)
  (h : is_open ((coe : s → X) ⁻¹' t)) : is_open (t ∩ s) :=
let ⟨a, b, c⟩ := inducing_coe.is_open_iff.mp h in
  subtype.preimage_coe_eq_preimage_coe_iff.mp c ▸ b.inter hs

lemma is_open_of_is_open_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA : ∀ x : Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_open ((coe : U → Y) ⁻¹' A)) : is_open A :=
is_open_iff_forall_mem_open.mpr (λ x hx, let ⟨U, hU1, hU2⟩ := hA x,
  ⟨V, hV1, hV2, hV3⟩ := mem_nhds_iff.mp hU1 in ⟨A ∩ V, set.inter_subset_left A V,
    is_open_inter_of_coe_preim V A hV2 ((continuous_inclusion hV1).is_open_preimage _ hU2), hx, hV3⟩)

lemma is_closed_of_is_closed_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA : ∀ x : Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_closed ((coe : U → Y) ⁻¹' A)) : is_closed A :=
 ⟨ is_open_of_is_open_coe Y Aᶜ (λ x, let ⟨U, hU,hN⟩ := hA x in ⟨ U,  hU , hN.1 ⟩) ⟩

lemma is_clopen_of_is_clopen_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA : ∀ x : Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_clopen ((coe : U → Y) ⁻¹' A)) : is_clopen A :=
⟨is_open_of_is_open_coe  Y A (λ x, let  ⟨ z,hz,hhz⟩:= hA x in ⟨ z,hz,hhz.1⟩  ) ,
 is_closed_of_is_closed_coe  Y A (λ x, let  ⟨ z,hz,hhz⟩:= hA x in ⟨ z,hz,hhz.2⟩  )⟩

theorem clopen_equalizer_of_discrete {X Y : Type*} [topological_space X] [topological_space Y]
  [discrete_topology Y] {f g : X → Y} (hf : continuous f) (hg : continuous g) :
  is_clopen {x : X | f x = g x} := (is_clopen_discrete (set.diagonal Y)).preimage (hf.prod_mk hg)


lemma tautology : true := sorry

theorem uniqueness_of_homotopy_lifting (Y : Type*) [topological_space Y] (hf : is_covering_map f)
  (H₁ H₂ : continuous_map Y E) (h : f ∘ H₁ = f ∘ H₂)
  (hC : ∀ x : Y, ∃ y ∈ connected_component x, H₁ y = H₂ y) :
  H₁ = H₂ :=
begin
  refine fun_like.ext H₁ H₂ (set.eq_univ_iff_forall.mp
    (clopen_set_intersect_connected_components_whole_set _ _
    (is_clopen_of_is_clopen_coe _ _ (λ x, _)) hC)),
  let t := (hf (f (H₁ x))).to_trivialization,
  let U := (f ∘ H₁) ⁻¹' t.base_set,
  refine ⟨U, (t.open_base_set.preimage (hf.continuous.comp H₁.continuous)).mem_nhds
    ((hf (f (H₁ x)))).mem_to_trivialization_base_set, _⟩,
  change is_clopen {y : U | H₁ y = H₂ y},
  have h0 : ∀ y : U, f (H₁ y) = f (H₂ y) := λ y, congr_fun h y,
  have h1 : ∀ y : U, f (H₁ y) ∈ t.base_set := subtype.prop,
  have h2 : ∀ y : U, f (H₂ y) ∈ t.base_set := λ y, h0 y ▸ h1 y,
  have key : ∀ y : U, H₁ y = H₂ y ↔ (t (H₁ y)).2 = (t (H₂ y)).2,
  { refine λ y, ⟨congr_arg (prod.snd ∘ t), λ m, _⟩,
    have h0 : f (H₁ y) = f (H₂ y) := congr_fun h y,
    rw [←t.coe_fst' (h1 y), ←t.coe_fst' (h2 y)] at h0,
    refine t.inj_on (t.mem_source.mpr (h1 y)) (t.mem_source.mpr (h2 y)) (prod.ext h0 m) },
  simp_rw [key],
  haveI := (hf (f (H₁ x))).1,
  simp only [←t.mem_source] at h1 h2,
  refine clopen_equalizer_of_discrete
    (continuous_snd.comp (t.continuous_to_fun.comp_continuous (H₁.2.comp continuous_subtype_coe) h1))
    (continuous_snd.comp (t.continuous_to_fun.comp_continuous (H₂.2.comp continuous_subtype_coe) h2)),
end

  -- is_open.preimage k (connected_component_in r x)
  -- hf.mem_to_trivialization_base_set

#check set.eq_univ_iff_forall
#check fun_like.ext
#check is_open_iff_forall_mem_open
#check connected_component
#check is_open_iff_forall_mem_open

#check is_locally_constant
#check is_locally_constant.apply_eq_of_is_preconnected

#check equiv.of_bijective
#check equiv.to_homeomorph_of_inducing
#check homeomorph.homeomorph_of_continuous_open
