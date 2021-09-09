/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/

import algebra.module.basic

/-!
# Instances on pempty

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/

universes u

@[to_additive]
instance semigroup_pempty : semigroup pempty.{u+1} :=
{ mul := λ x y, by cases x,
  mul_assoc := λ x y z, by cases x }
