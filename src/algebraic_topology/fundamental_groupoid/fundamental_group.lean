/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import category_theory.groupoid
import topology.category.Top.basic
import topology.path_connected
import topology.homotopy.path
import algebraic_topology.fundamental_groupoid.basic

/-!
# Fundamental group of a space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
local attribute [reducible] fundamental_groupoid

/-- Get an isomorphism between the fundamental groups at two points given a path -/
def fundamental_group_mul_equiv_of_path (p : path x₀ x₁) :
  fundamental_group X x₀ ≃* fundamental_group X x₁ := Aut.Aut_mul_equiv_of_iso (as_iso ⟦p⟧)

variables (x₀ x₁)

/-- The fundamental group of a path connected space is independent of the choice of basepoint. -/
def fundamental_group_mul_equiv_of_path_connected [path_connected_space X] :
  (fundamental_group X x₀) ≃* (fundamental_group X x₁) :=
fundamental_group_mul_equiv_of_path (path_connected_space.some_path x₀ x₁)

/-- An element of the fundamental group as an arrow in the fundamental groupoid. -/
abbreviation to_arrow {X : Top} {x : X} (p : fundamental_group X x) : x ⟶ x :=
p.hom

/-- An element of the fundamental group as a quotient of homotopic paths. -/
abbreviation to_path {X : Top} {x : X} (p : fundamental_group X x) :
  path.homotopic.quotient x x := to_arrow p

/-- An element of the fundamental group, constructed from an arrow in the fundamental groupoid. -/
abbreviation from_arrow {X : Top} {x : X} (p : x ⟶ x) : fundamental_group X x :=
⟨p, category_theory.groupoid.inv p⟩

/-- An element of the fundamental gorup, constructed from a quotient of homotopic paths. -/
abbreviation from_path {X : Top} {x : X} (p : path.homotopic.quotient x x) :
  fundamental_group X x := from_arrow p

end fundamental_group
