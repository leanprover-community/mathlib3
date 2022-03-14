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

/-- The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid.
-/
def fundamental_group (X : Type u) [topological_space X] (x : X) :=
category_theory.Aut (@fundamental_groupoid.from_top (Top.of X) x)

namespace fundamental_group

local attribute [instance] path.homotopic.setoid

instance group (x : X) : group (fundamental_group X x) :=
category_theory.Aut.group x

instance inhabited : inhabited (fundamental_group X x₀) :=
category_theory.Aut.inhabited x₀

@[instance, priority 100]
private def category : category_theory.category X :=
fundamental_groupoid.category_theory.groupoid.to_category

/-- The fundamental group of a path connected space is independent of the choice
of basepoint.
-/
def iso_fundamental_group_of_path_connected [path_connected_space X] :
  (fundamental_group X x₀) ≅ (fundamental_group X x₁) :=
let α := fundamental_groupoid.iso_of_path_conn x₀ x₁ in
{ hom := λγ, ⟨α.inv ≫ γ.hom ≫ α.hom, α.inv ≫ γ.inv ≫ α.hom⟩,
  inv := λγ, ⟨α.hom ≫ γ.hom ≫ α.inv, α.hom ≫ γ.inv ≫ α.inv⟩}

end fundamental_group
