/-
Copyright (c) 2022 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/

import algebraic_topology.fundamental_groupoid.basic
import algebraic_topology.fundamental_groupoid.product
import category_theory.thin

/-
# Covering spaces

## Main definitions

  - ...

## References
* [Ronald Brown, *Topology and Groupoids*, Chapter 10][...]
-/

noncomputable theory

universes u v

open fundamental_groupoid
open category_theory
open fundamental_groupoid_functor

open_locale fundamental_groupoid

namespace Groupoid

section unbundled_covering_morphism

-- variables {C X : Type u} [topological_space C] [topological_space X]
variables {C X : Groupoid.{u v}}

/-- A morphism in Groupoid is a covering morphism if   -/
structure is_covering_morphism (p : C ⟶ X) : Prop :=
(iso_of_under_restriction : ∀(x : C), true)
/- TODO: define this here, probably want to deal with category_theory.under -/

end unbundled_covering_morphism

structure covering_morphism (C X : Groupoid.{u v}) :=
(to_morphism : C ⟶ X)
(covering_morphism' : is_covering_morphism to_morphism)

structure covering_groupoid (X : Groupoid.{u}) :=
(to_groupoid : Groupoid.{u v})
(covering_morphism' : covering_morphism to_groupoid X)

end Groupoid


structure is_covering_space
  (C : Type*) (X : Type*) [topological_space C] [topological_space X] : Prop :=
(fundamental_groupoid_is_covering_groupoid : true)
-- TODO: figure out the right condition for a space to be a covering space

/-- A space C is a universal cover for X if it's a covering space whose fundamental groupoid
is thin i.e. there is at most one morphism x ⟶ y for each pair of objects x, y in C. -/
structure is_universal_cover (C : Type*) (X : Type*) [topological_space C] [topological_space X]
  extends is_covering_space C X : Prop :=
(thin_fundamental_groupoid : ∀(x y : πₓ (Top.of C)), subsingleton (x ⟶ y))
