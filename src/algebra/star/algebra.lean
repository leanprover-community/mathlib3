/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.basic
import algebra.star.basic
import algebra.star.pi

/-!
# Star algebras

Introduces the notion of a star algebra over a star ring.
-/

universes u v w

/--
A star algebra `A` over a star ring `R` is an algebra which is a star ring,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[star_ring R] [star_ring A] [algebra R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_scalar R A]`.
-/
-- Note that we take `has_star A` as a typeclass argument, rather than extending it,
-- to avoid having multiple definitions of the star operation.
class star_algebra (R : Type u) (A : Type v) [has_star R] [has_star A] [has_scalar R A] :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a)

@[simp] lemma star_smul {R : Type u} {A : Type v}
  [has_star R] [has_star A] [has_scalar R A] [star_algebra R A]
  (r : R) (a : A) :
  star (r • a) = star r • star a :=
star_algebra.star_smul r a

namespace pi

variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances

instance {R : Type w}
  [Π i, has_scalar R (f i)] [has_star R] [Π i, has_star (f i)] [Π i, star_algebra R (f i)] :
  star_algebra R (Π i, f i) :=
{ star_smul := λ r x, funext $ λ _, star_smul _ _ }

end pi
