/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import category_theory.category.Groupoid
import category_theory.groupoid
import topology.category.Top.basic
import topology.path_connected
import topology.homotopy.path
import algebraic_topology.fundamental_groupoid.basic

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/
universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
variables {x₀ x₁ : X}

noncomputable theory

open category_theory

/-- The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid. -/
@[derive [group,inhabited]]
def fundamental_group (X : Type u) [topological_space X] (x : X) :=
@Aut (fundamental_groupoid X) _ x

namespace fundamental_group

local attribute [instance] path.homotopic.setoid

/-- Get an isomorphism between the fundamental groups at two points given a path -/
def fundamental_group_mul_equiv_of_path (p : path x₀ x₁) :
  fundamental_group X x₀ ≃* fundamental_group X x₁ := Aut.Aut_mul_equiv_of_iso (as_iso ⟦p⟧)

variables (x₀ x₁)

/-- The fundamental group of a path connected space is independent of the choice of basepoint. -/
def fundamental_group_mul_equiv_of_path_connected [path_connected_space X] :
  (fundamental_group X x₀) ≃* (fundamental_group X x₁) :=
fundamental_group_mul_equiv_of_path (path_connected_space.some_path x₀ x₁)

end fundamental_group
