/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.is_locally_homeomorph
import topology.fiber_bundle

/-!
# Local homeomorphisms

This file defines covering maps.

## Main definitions

* `is_covering_map`: A covering map is a continuous function `f : E → X` with discrete
  fibers such that each point of `X` has an evenly covered neighborhood.
-/

lemma inducing.discrete_topology {α β : Type*} [topological_space α] [topological_space β]
  [discrete_topology β] {f : α → β} (h1 : inducing f) (h2 : function.injective f) :
  discrete_topology α :=
⟨by rw [h1.induced, discrete_topology.eq_bot β, induced_bot h2]⟩

variables {E X : Type*} [topological_space E] [topological_space X] (f : E → X)

open topological_fiber_bundle

/-- Each fiber of a trivialization is homeomorphic to the specified fiber. -/
def topological_fiber_bundle.trivialization.preimage_singleton_homeomorph {B F Z : Type*}
  [topological_space B] [topological_space F] [topological_space Z] {f : Z → B}
  (ϕ : trivialization F f) {b : B} (hb : b ∈ ϕ.base_set) : f ⁻¹' {b} ≃ₜ F :=
{ to_fun := λ x, (ϕ x).2,
  inv_fun := λ x, ⟨ϕ.to_local_homeomorph.symm ⟨b, x⟩, ϕ.proj_symm_apply' hb⟩,
  left_inv := by
  { rintros ⟨x, rfl : f x = b⟩;
    exact subtype.ext (ϕ.symm_apply_mk_proj (ϕ.mem_source.mpr hb)) },
  right_inv := λ x, congr_arg prod.snd (ϕ.apply_symm_apply (ϕ.mem_target.mpr (by exact hb))),
  continuous_to_fun := continuous_on_iff_continuous_restrict.mp (continuous_snd.comp_continuous_on
    (ϕ.continuous_to_fun.mono (λ x (hx : f x = b), by rwa [ϕ.source_eq, set.mem_preimage, hx]))),
  continuous_inv_fun := continuous_subtype_mk _
      (ϕ.continuous_inv_fun.comp_continuous (continuous.prod.mk b) (λ x, ϕ.mem_target.mpr hb)) }

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

lemma continuous_at {x : E} {I : Type*} [topological_space I]
  (h : is_evenly_covered f (f x) I) : continuous_at f x :=
h.to_trivialization.continuous_at_proj
  (h.to_trivialization.mem_source.mpr (mem_to_trivialization_base_set h))

lemma to_is_evenly_covered_preimage {x : X} {I : Type*} [topological_space I]
  (h : is_evenly_covered f x I) : is_evenly_covered f x (f ⁻¹' {x}) :=
begin
  let ε := (classical.some h.2).preimage_singleton_homeomorph (classical.some_spec h.2),
  haveI := h.1,
  exact ⟨ε.inducing.discrete_topology ε.injective, _, h.mem_to_trivialization_base_set⟩,
end

end is_evenly_covered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def is_covering_map :=
∀ x, is_evenly_covered f x (f ⁻¹' {x})

namespace is_covering_map

lemma mk (F : X → Type*) [Π x, topological_space (F x)]
  [hF : Π x, discrete_topology (F x)] (e : Π x, trivialization (F x) f)
  (h : ∀ x, x ∈ (e x).base_set) : is_covering_map f :=
λ x, is_evenly_covered.to_is_evenly_covered_preimage ⟨hF x, e x, h x⟩

variables {f}

lemma continuous (hf : is_covering_map f) : continuous f :=
continuous_iff_continuous_at.mpr (λ x, (hf (f x)).continuous_at)

lemma is_locally_homeomorph (hf : is_covering_map f) : is_locally_homeomorph f :=
begin
  refine is_locally_homeomorph.mk f (λ x, _),
  let e := (hf (f x)).to_trivialization,
  have h := (hf (f x)).mem_to_trivialization_base_set,
  refine ⟨e.to_local_homeomorph.trans
  { to_fun := λ p, p.1,
    inv_fun := λ p, ⟨p, x, rfl⟩,
    source := e.base_set ×ˢ ({⟨x, rfl⟩} : set (f ⁻¹' {f x})),
    target := e.base_set,
    open_source := e.open_base_set.prod (singletons_open_iff_discrete.mpr (hf (f x)).1 ⟨x, rfl⟩),
    open_target := e.open_base_set,
    map_source' := λ p, and.left,
    map_target' := λ p hp, ⟨hp, rfl⟩,
    left_inv' := λ p hp, by exact prod.ext rfl hp.2.symm,
    right_inv' := λ p hp, rfl,
    continuous_to_fun := continuous_fst.continuous_on,
    continuous_inv_fun := (continuous_id'.prod_mk continuous_const).continuous_on },
    ⟨e.mem_source.2 h, _, (hf (f x)).to_trivialization_apply⟩, λ p h, (e.proj_to_fun p h.1).symm⟩,
  rwa [e.to_local_homeomorph.symm_symm, e.proj_to_fun],
  rwa e.mem_source,
end

lemma is_open_map (hf : is_covering_map f) : is_open_map f :=
hf.is_locally_homeomorph.is_open_map

lemma quotient_map (hf : is_covering_map f) (hf' : function.surjective f) : quotient_map f :=
hf.is_open_map.to_quotient_map hf.continuous hf'

end is_covering_map

lemma is_topological_fiber_bundle.to_covering_map {B F Z : Type*} [topological_space B]
  [topological_space F] [topological_space Z] [discrete_topology F] {f : Z → B}
  (hf : is_topological_fiber_bundle F f) : is_covering_map f :=
is_covering_map.mk f (λ x, F) (λ x, classical.some (hf x)) (λ x, classical.some_spec (hf x))
