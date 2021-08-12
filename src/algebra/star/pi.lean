/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.star.basic
import algebra.ring.pi

/-!
# `star` on pi types

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.

Note that `pi.star_algebra` is in a different file to avoid pulling in everything from
`algebra/algebra/basic`.
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances

namespace pi

instance [Π i, has_star (f i)] : has_star (Π i, f i) :=
{ star := λ x i, star (x i) }

@[simp] lemma star_apply [Π i, has_star (f i)] (x : Π i, f i) (i : I) : star x i = star (x i) := rfl

instance [Π i, has_involutive_star (f i)] : has_involutive_star (Π i, f i) :=
{ star_involutive := λ _, funext $ λ _, star_star _ }

instance [Π i, monoid (f i)] [Π i, star_monoid (f i)] : star_monoid (Π i, f i) :=
{ star_mul := λ _ _, funext $ λ _, star_mul _ _ }

instance [Π i, semiring (f i)] [Π i, star_ring (f i)] : star_ring (Π i, f i) :=
{ star_add := λ _ _, funext $ λ _, star_add _ _,
  ..(by apply_instance : star_monoid (Π i, f i)) }

end pi
