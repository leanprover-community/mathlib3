/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebraic_geometry.sheafed_space
import algebra.category.CommRing
import algebraic_geometry.stalks
import ring_theory.ideal.basic


universes v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.category category_theory.functor

-- local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

/-- A `RingedSpace` is a topological space equipped with a sheaf of commutative rings.

A morphism of ringed spaces is a morphism of ring-presheafed spaces. -/
@[derive category]
def RingedSpace := SheafedSpace CommRing

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
structure LocallyRingedSpace extends (SheafedSpace CommRing) :=
(local_ring : ∀ x : carrier, local_ring (𝒪.stalk x))

end algebraic_geometry
