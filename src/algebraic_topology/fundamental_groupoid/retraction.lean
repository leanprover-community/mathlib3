/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import topology.homotopy.equiv
import category_theory.equivalence
import algebraic_topology.fundamental_groupoid.product

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

  - `retraction X A` A retraction from topological space X to a subspace A is a continuous
    map `f : C(X, A)` such that the restriction of f to A is the identity

  - `split_mono_of_retraction` The induced map on `fundamental_groupoid X` of the inclusion
    `i : A → X` and the retraction form a `split_mono i`.
-/

noncomputable theory

universe u

open fundamental_groupoid
open category_theory
open fundamental_groupoid_functor

open_locale fundamental_groupoid
open_locale unit_interval

section retraction

-- We automatically get the subspace topology for A via `subtype.topological_space`
variables {X : Top} {A_filter : X → Prop}

def inclusion : C(Top.of (subtype A_filter), X) := ⟨subtype.restrict A_filter id⟩

structure retraction (r : C(X, Top.of (subtype A_filter))) : Prop :=
(id_of_retraction_of_inclusion : r ∘ inclusion = id)

theorem split_mono_of_inclusion_retraction
  {r : C(X, Top.of (subtype A_filter))}
  {h_retraction : retraction r} :
  is_split_mono (πₘ (@inclusion X A_filter)) :=
{
  exists_split_mono := ⟨{
    retraction := πₘ r,
    id' := sorry,
  }⟩,
}

end retraction
