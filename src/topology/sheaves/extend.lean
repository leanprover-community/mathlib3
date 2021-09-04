/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/

import topology.sheaves.sheaf_condition.unique_gluing

/-!

# Extending a sheaf homomorphism from a basis.

TODO

-/

noncomputable theory

open Top
open topological_space
open topological_space.opens
open category_theory
open category_theory.limits
open opposite

universes u v

variables {C : Type u} [category.{v} C] [concrete_category.{v} C] [has_limits C]
variables [reflects_isomorphisms (forget C)] [preserves_limits (forget C)]

variables (X : Top.{v}) (B : set (opens X)) (F G : presheaf C X)
