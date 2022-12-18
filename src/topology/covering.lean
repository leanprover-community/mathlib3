/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.is_locally_homeomorph
import topology.fiber_bundle.basic

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

end is_covering_map

variables {f}

protected lemma is_fiber_bundle.is_covering_map {F : Type*} [topological_space F]
  [discrete_topology F] (hf : ∀ x : X, ∃ e : trivialization F f, x ∈ e.base_set) :
  is_covering_map f :=
is_covering_map.mk f (λ x, F) (λ x, classical.some (hf x)) (λ x, classical.some_spec (hf x))

protected lemma fiber_bundle.is_covering_map {F : Type*} {E : X → Type*} [topological_space F]
  [discrete_topology F] [topological_space (bundle.total_space E)] [Π x, topological_space (E x)]
  [hf : fiber_bundle F E] : is_covering_map (π E) :=
is_fiber_bundle.is_covering_map
  (λ x, ⟨trivialization_at F E x, mem_base_set_trivialization_at F E x ⟩)
