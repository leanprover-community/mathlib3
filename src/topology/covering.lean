/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.is_locally_homeomorph
import topology.fiber_bundle
import topology.locally_constant.basic
import set_theory.cardinal.basic
import topology.homotopy.basic

/-!
# Covering Maps
This file defines covering maps.
## Main definitions
* `is_covering_map`: A covering map is a continuous function `f : E → X` with discrete
  fibers such that each point of `X` has an evenly covered neighborhood.
-/

variables {E X : Type*} [topological_space E] [topological_space X] (f : E → X)

open topological_fiber_bundle

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
let e := h.to_trivialization in
  e.continuous_at_proj (e.mem_source.mpr (mem_to_trivialization_base_set h))

lemma to_is_evenly_covered_preimage {x : X} {I : Type*} [topological_space I]
  (h : is_evenly_covered f x I) : is_evenly_covered f x (f ⁻¹' {x}) :=
let ⟨h1, h2⟩ := h in by exactI ⟨((classical.some h2).preimage_singleton_homeomorph
  (classical.some_spec h2)).embedding.discrete_topology, _, h.mem_to_trivialization_base_set⟩

end is_evenly_covered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def is_covering_map :=
∀ x, is_evenly_covered f x (f ⁻¹' {x})

namespace is_covering_map

lemma mk (F : X → Type*) [Π x, topological_space (F x)] [hF : Π x, discrete_topology (F x)]
  (e : Π x, trivialization (F x) f) (h : ∀ x, x ∈ (e x).base_set) : is_covering_map f :=
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
    open_source := e.open_base_set.prod (singletons_open_iff_discrete.2 (hf (f x)).1 ⟨x, rfl⟩),
    open_target := e.open_base_set,
    map_source' := λ p, and.left,
    map_target' := λ p hp, ⟨hp, rfl⟩,
    left_inv' := λ p hp, prod.ext rfl hp.2.symm,
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

lemma is_topological_fiber_bundle.is_covering_map {B Z F : Type*} [topological_space B]
  [topological_space Z] [topological_space F] [discrete_topology F] {f : Z → B}
  (hf : is_topological_fiber_bundle F f) : is_covering_map f :=
is_covering_map.mk f (λ x, F) (λ x, classical.some (hf x)) (λ x, classical.some_spec (hf x))

noncomputable def bijective_covering_map_is_homeomorph (hf : is_covering_map f)
  (h : function.bijective f) : homeomorph E X:=
  homeomorph.homeomorph_of_continuous_open (equiv.of_bijective f h) hf.continuous hf.is_open_map

open_locale cardinal
lemma fiber_cardinality_is_locally_constant (hf : is_covering_map f) :
  is_locally_constant (λ x : X, #(f⁻¹' {x} )):=
  begin
      rw is_locally_constant.iff_exists_open,
      intro x,
      have y:= (hf x).2,
      obtain ⟨t,ht⟩:=y,
      refine ⟨ t.base_set,t.open_base_set,ht,_⟩,
      intros y hy,
      apply equiv.cardinal_eq,
      have:= t.preimage_singleton_homeomorph hy,
      exact homeomorph.to_equiv this,


  end
lemma short_fiber_cardinality_is_locally_constant (hf : is_covering_map f) :
  is_locally_constant (λ x : X, #(f⁻¹' {x} )):=
   (is_locally_constant.iff_exists_open _).2 $ λx, let ⟨t,ht⟩:=(hf x).2
   in ⟨ t.base_set,t.open_base_set,ht,
   λ y hy,(t.preimage_singleton_homeomorph hy).to_equiv.cardinal_eq ⟩
#where

open_locale unit_interval

lemma clopen_set_intersect_connected_components_whole_set (Y: Type*) [topological_space Y](S : set Y)
  (hS:is_clopen S)(w:∀ x: Y, ∃y∈ connected_component x, y∈ S ): S = set.univ:=
  begin
    rw set.eq_univ_iff_forall,
    intro x,
    obtain ⟨y,hy,h⟩ := w x,
    have t:= is_clopen.connected_component_subset hS h,
    rw←   connected_component_eq hy at t,
    exact t mem_connected_component,
  end

#check nhds

open_locale topological_space

lemma is_open_inter_of_coe_preim {X : Type*} [topological_space X] (s t : set X) (hs : is_open s)
  (h : is_open ((coe : s → X) ⁻¹' t)) : is_open (t ∩ s) :=
let ⟨a, b, c⟩ := inducing_coe.is_open_iff.mp h in
  subtype.preimage_coe_eq_preimage_coe_iff.mp c ▸ b.inter hs


lemma is_open_of_is_open_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA: ∀ x:Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_open ((coe : U → Y)⁻¹' A)):is_open A :=
is_open_iff_forall_mem_open.mpr (λ x hx, let ⟨U, hU1, hU2⟩ := hA x,
  ⟨V, hV1, hV2, hV3⟩ := mem_nhds_iff.mp hU1 in ⟨A ∩ V, set.inter_subset_left A V,
    is_open_inter_of_coe_preim V A hV2 ((continuous_inclusion hV1).is_open_preimage _ hU2), hx, hV3⟩)

lemma is_closed_of_is_closed_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA: ∀ x:Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_closed ((coe : U → Y)⁻¹' A)):is_closed A :=
 ⟨ is_open_of_is_open_coe Y Aᶜ (λ x, let ⟨U, hU,hN⟩ := hA x in ⟨ U,  hU , hN.1 ⟩) ⟩

lemma is_clopen_of_is_clopen_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA: ∀ x:Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_clopen ((coe : U → Y)⁻¹' A)):is_clopen A :=
⟨is_open_of_is_open_coe  Y A (λ x, let  ⟨ z,hz,hhz⟩:= hA x in ⟨ z,hz,hhz.1⟩  ) ,
 is_closed_of_is_closed_coe  Y A (λ x, let  ⟨ z,hz,hhz⟩:= hA x in ⟨ z,hz,hhz.2⟩  )⟩

lemma test_false :true:=
begin
  refine ⟨ ⟩,
end



theorem uniqueness_of_homotopy_lifting (Y: Type*)
[topological_space Y](hf: is_covering_map f)
  (H₁ H₂:(continuous_map Y E)) (h: f∘ H₁ = f∘ H₂)
  ( hC: (∀ x : Y, ∃ y∈ connected_component x , H₁ y = H₂ y)):
  H₁ = H₂:=

  begin

    let composition := f∘ H₁,
    have k:continuous composition:=continuous.comp hf.continuous H₁.continuous ,
    have london:=clopen_set_intersect_connected_components_whole_set Y _ _ hC,
    {apply fun_like.ext H₁ H₂ ,
    rw set.eq_univ_iff_forall at london,
    exact london},

      apply is_clopen_of_is_clopen_coe,
      intro x,
      let c:= (hf  $ composition x).to_trivialization,

      have c1 := c.1,
      have c2:=c.2,
      let cbase:= c.base_set,
      let d:= composition⁻¹' c.base_set,
      use d,

      have l:= mem_nhds_iff.2 ⟨ d,subset_rfl ,k.is_open_preimage c.base_set c.open_base_set,
        set.mem_preimage.2 (is_evenly_covered.mem_to_trivialization_base_set _)⟩,
      split,
      exact l,
      apply is_clopen_of_is_clopen_coe,
      intro x,
      let t:= λ j:d,(c1( H₁ j)).2,
      use set.univ,
      refine ⟨↑l,_⟩,



      {sorry,}

  end

  -- is_open.preimage k (connected_component_in r x)
  -- hf.mem_to_trivialization_base_set

#check set.eq_univ_iff_forall
#check fun_like.ext
#check is_open_iff_forall_mem_open
#check connected_component
# is_open_iff_forall_mem_open

#check is_locally_constant
#check is_locally_constant.apply_eq_of_is_preconnected

#check equiv.of_bijective
#check equiv.to_homeomorph_of_inducing
#check homeomorph.homeomorph_of_continuous_open
