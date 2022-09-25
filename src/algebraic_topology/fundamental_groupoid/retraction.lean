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

example (X Y : Type*) (f g : X → Y) : (∀(x : X), f x = g x) → f = g :=
begin
  refine funext,
end


def top_hom_of_continuous_map
  {X Y : Type*} [topological_space X] [topological_space Y] (f : C(X, Y)) : Top.of X ⟶ Top.of Y := f


section unbundled

/-- We define `A ⊆ X` to be a topological subspace by defining the property `A_filter` picking
elements of `A` out of `X`. This inherits the topology on `X` via `subtype.topological_space`. -/
variables {X : Type*} {A_filter : X → Prop} [topological_space X]

def inclusion (X : Type*) (A_filter : X → Prop) [topological_space X] :
  C(subtype A_filter, X) := ⟨subtype.restrict A_filter id⟩

structure is_top_retraction (r : X → subtype A_filter) extends continuous r : Prop :=
(id_of_retraction_of_inclusion : r ∘ (inclusion X A_filter) = id)

lemma is_top_retraction.continuous {r : X → subtype A_filter} (hr : is_top_retraction r) :
  continuous r :=
hr.to_continuous

end unbundled


structure top_retraction (X : Type*) (A_filter : X → Prop) [topological_space X] :=
(to_fun : X → subtype A_filter)
(top_retraction' : is_top_retraction to_fun)


namespace top_retraction

variables {X : Type*} {A_filter : X → Prop} [topological_space X]

def to_continuous_map (r : top_retraction X A_filter) : C(X, subtype A_filter) :=
{ to_fun := r.to_fun,
  continuous_to_fun :=  is_top_retraction.continuous r.top_retraction' }

lemma coe_continuous_map_eq_to_fun (r : top_retraction X A_filter) :
  ⇑r.to_continuous_map = r.to_fun := by refl

@[priority 100]
instance top_retraction.continuous_map_class :
  continuous_map_class (top_retraction X A_filter) X (subtype A_filter) :=
{ coe := top_retraction.to_fun,
  coe_injective' := λr s h, by { cases r, cases s, congr' },
  map_continuous := λr, is_top_retraction.continuous r.top_retraction' }


set_option trace.simplify.rewrite true

/-- We show that if a topological retraction `r : X → A` exists, then the inclusion map `i : A → X`
is a split monomorphism in the category Top. -/
def split_mono_of_inclusion (r : top_retraction X A_filter) :
  split_mono (top_hom_of_continuous_map (inclusion X A_filter)) :=
{ retraction := r.to_continuous_map,
  id' := begin
    apply fun_like.ext,
    rw [top_hom_of_continuous_map, Top.top_comp, Top.top_id,
        continuous_map.coe_mk, continuous_map.coe_mk, coe_continuous_map_eq_to_fun,
        r.top_retraction'.id_of_retraction_of_inclusion],
    intro x, refl,
  end, }

/-- We show that a topological retraction `r : X → A` is a split epimorphism in the category Top. -/
def split_epi_of_retraction (r : top_retraction X A_filter) :
  split_epi (top_hom_of_continuous_map r.to_continuous_map) :=
{ section_ := inclusion X A_filter,
  id' := begin
    apply fun_like.ext,
    rw [top_hom_of_continuous_map, Top.top_comp, Top.top_id,
        continuous_map.coe_mk, continuous_map.coe_mk, coe_continuous_map_eq_to_fun,
        r.top_retraction'.id_of_retraction_of_inclusion],
    intro x, refl,
  end, }

/-- We show that if a topological retraction `r : X → A` exists, then the induced arrow between
fundamental groupoids of the inclusion map `i : A → X` is split monomorphism in the category
Groupoid. -/
def fundamental_groupoid_split_mono (r : top_retraction X A_filter) :
  split_mono (πₘ (top_hom_of_continuous_map (inclusion X A_filter))) :=
split_mono.map (split_mono_of_inclusion r) fundamental_groupoid_functor

/-- We show that the induced arrow between fundamental groupoids of the topological retraction
`r : X → A` is a split epimorphism in the category Groupoid. -/
def fundamental_groupoid_split_epi (r : top_retraction X A_filter) :
  split_epi (πₘ (top_hom_of_continuous_map r.to_continuous_map)) :=
split_epi.map (split_epi_of_retraction r) fundamental_groupoid_functor

/-- We show that the induced arrow of the topological retraction `r : X → A` in the fundamental
groupoid is an epimorphism. -/
def fundamental_groupoid_epi_of_top_retraction (r : top_retraction X A_filter) :
  epi (πₘ (top_hom_of_continuous_map r.to_continuous_map)) :=
split_epi.epi (fundamental_groupoid_split_epi r)

end top_retraction
