/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison.
-/
import algebra.algebra.ordered
import algebra.star.basic

universes u v

/--
A star algebra `A` over a star ring `R` is an algebra which is a star ring,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.
-/
class star_algebra (R : Type u) (A : Type v)
  [comm_semiring R] [star_ring R] [semiring A] [algebra R A] extends star_ring A :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = (@has_star.star R _ r) • star a)

variables {A : Type v}

@[simp] lemma star_smul (R : Type u) (A : Type v)
  [comm_semiring R] [star_ring R] [semiring A] [algebra R A] [star_algebra R A] (r : R) (a : A) :
  star (r • a) = star r • star a :=
star_algebra.star_smul r a
