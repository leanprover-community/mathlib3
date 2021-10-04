/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.basic
import algebra.star.basic
import algebra.star.pi

/-!
# Star modules and algebras

Introduces the notion of a star algebra over a star ring.
-/

universes u v w

/--
A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_scalar R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
-- Note that we take `has_star A` as a typeclass argument, rather than extending it,
-- to avoid having multiple definitions of the star operation.
class star_module (R : Type u) (A : Type v) [has_star R] [has_star A] [has_scalar R A] :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a)

export star_module (star_smul)
attribute [simp] star_smul

namespace pi

variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances

instance {R : Type w}
  [Π i, has_scalar R (f i)] [has_star R] [Π i, has_star (f i)] [Π i, star_module R (f i)] :
  star_module R (Π i, f i) :=
{ star_smul := λ r x, funext $ λ i, star_smul r (x i) }

end pi
