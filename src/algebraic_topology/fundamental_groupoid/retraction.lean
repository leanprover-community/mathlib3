/-
Copyright (c) 2022 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import topology.homotopy.equiv
import category_theory.equivalence
import algebraic_topology.fundamental_groupoid.product

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

  - `is_retraction r` A continuous map `r : X → A` (where `A` is a subtype of `X`) is a retraction
    when the restriction of r to A is the identity. Equivalently, composing r with the inclusion
    `i : A → X` is just the identity map on A.

  - `fundamental_groupoid_split_mono_of_top_inclusion` The induced map on `fundamental_groupoid X`
    of the inclusion `i : A → X` is a split mono in the category Groupoid.
  - `fundamental_groupoid_split_epi_of_top_retraction` The induced map on `fundamental_groupoid X`
    of the retraction `r : X → A` is a split epi in the category Groupoid.
-/

noncomputable theory

universe u

open fundamental_groupoid
open category_theory
open fundamental_groupoid_functor

open_locale fundamental_groupoid
open_locale unit_interval


def top_hom_of_continuous_map {X Y : Top.{u}} (f : C(X, Y)) : X ⟶ Y := f


section unbundled

/-- We define `A ⊆ X` to be a topological subspace by defining the property `A_filter` picking
elements of `A` out of `X`. This inherits the topology on `X` via `subtype.topological_space`. -/
variables {X : Top} {A_filter : X → Prop}

def inclusion : C(Top.of (subtype A_filter), X) := ⟨subtype.restrict A_filter id⟩

structure is_top_retraction (r : X → subtype A_filter) extends continuous r : Prop :=
(id_of_retraction_of_inclusion : r ∘ inclusion = id)

lemma is_top_retraction.continuous {r : X → subtype A_filter} (hr : is_top_retraction r) :
  continuous r :=
hr.to_continuous

end unbundled

structure top_retraction (X : Top) (A_filter : X → Prop) :=
(to_fun : X → subtype A_filter)
(top_retraction' : is_top_retraction to_fun)

namespace top_retraction

variables {X : Top} {A_filter : X → Prop}

def to_continuous_map (r : @top_retraction X A_filter) : C(X, Top.of (subtype A_filter)) :=
{ to_fun := r.to_fun,
  continuous_to_fun :=  is_top_retraction.continuous r.top_retraction'}

instance top_retraction.continuous_map_class :
  continuous_map_class (top_retraction X A_filter) X (subtype A_filter) :=
{ coe := top_retraction.to_fun,
  coe_injective' := λr s h, by { cases r, cases s, congr' },
  map_continuous := λr, is_top_retraction.continuous r.top_retraction', }

/-- We show that if a topological retraction `r : X → A` exists, then the inclusion map `i : A → X`
is a split monomorphism in the category Top. -/
def split_mono_of_top_inclusion {r : top_retraction X A_filter} :
  split_mono (top_hom_of_continuous_map inclusion) :=
{ retraction := r.to_continuous_map,
  id' := begin
    rw top_hom_of_continuous_map,
    ext,
    rw [Top.id_app,
        Top.comp_app,
        ← continuous_map.comp_apply,
        continuous_map.coe_comp, -- TODO: fix rws in here
        h_retraction.id_of_retraction_of_inclusion,
        id.def],
  end, }

/-- We show that a topological retraction `r : X → A` is a split epimorphism in the category Top. -/
def split_epi_of_top_retraction {r : top_retraction X A_filter} :
  split_epi (top_hom_of_continuous_map r.to_continuous_map) :=
{ section_ := inclusion,
  id' := begin
    rw top_hom_of_continuous_map,
    ext,
    rw [Top.id_app,
        Top.comp_app,
        ← continuous_map.comp_apply,
        continuous_map.coe_comp, -- TODO: fix rws in here
        h_retraction.id_of_retraction_of_inclusion,
        id.def],
  end, }

/-- We show that if a topological retraction `r : X → A` exists, then the induced arrow between
fundamental groupoids of the inclusion map `i : A → X` is split monomorphism in the category
Groupoid. -/
def fundamental_groupoid_split_mono_of_top_inclusion
  {r : C(X, Top.of (subtype A_filter))} {h_retraction : is_retraction r} :
  split_mono (πₘ (@inclusion X A_filter)) :=
split_mono.map (@split_mono_of_top_inclusion X A_filter r h_retraction) fundamental_groupoid_functor

/-- We show that the induced arrow between fundamental groupoids of the topological retraction
`r : X → A` is a split epimorphism in the category Groupoid. -/
def fundamental_groupoid_split_epi_of_top_retraction
  {r : C(X, Top.of (subtype A_filter))} {h_retraction : is_retraction r} :
  split_epi (πₘ r) :=
split_epi.map (@split_epi_of_top_retraction X A_filter r h_retraction) fundamental_groupoid_functor

/-- We show that the induced arrow of the topological retraction `r : X → A` in the fundamental
groupoid is an epimorphism. -/
def fundamental_groupoid_epi_of_top_retraction
  {r : C(X, Top.of(subtype A_filter))} {h_retraction : is_retraction r} :
  epi (πₘ r) :=
split_epi.epi (@fundamental_groupoid_split_epi_of_top_retraction X A_filter r h_retraction)

end top_retraction
