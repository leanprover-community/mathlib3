/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import category_theory.category.Groupoid
import category_theory.groupoid
import topology.category.Top.basic
import topology.homotopy.path
import topology.homotopy.fundamental_groupoid

/-!
# Fundamental groupoid of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/
universes u v

noncomputable theory


def fundamental_group (X : Type u) [topological_space X] (x : X) :=
@category_theory.Aut
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  x

namespace fundamental_group

variables {X : Top} {Y : Top}

theorem iso_fundamental_group_of_path_connected [path_connected_space X] (x₀ x₁ : X) :
  (fundamental_group X x₀) ≅ (fundamental_group X x₁) :=
let α := fundamental_groupoid.iso_of_path_conn x₀ x₁ in
{ hom := λγ, ⟨sorry, sorry, sorry, sorry⟩,
  inv := λγ, ⟨sorry, sorry, sorry, sorry⟩, }

end fundamental_group
