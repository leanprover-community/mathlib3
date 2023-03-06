/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.star.basic
import algebra.ring.prod
import algebra.module.prod

/-!
# `star` on product types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We put a `has_star` structure on product types that operates elementwise.
-/

universes u v w
variables {R : Type u} {S : Type v}

namespace prod

instance [has_star R] [has_star S] : has_star (R × S) :=
{ star := λ x, (star x.1, star x.2) }

@[simp] lemma fst_star [has_star R] [has_star S] (x : R × S) : (star x).1 = star x.1 := rfl
@[simp] lemma snd_star [has_star R] [has_star S] (x : R × S) : (star x).2 = star x.2 := rfl

lemma star_def [has_star R] [has_star S] (x : R × S) : star x = (star x.1, star x.2) := rfl

instance [has_involutive_star R] [has_involutive_star S] : has_involutive_star (R × S) :=
{ star_involutive := λ _, prod.ext (star_star _) (star_star _) }

instance [semigroup R] [semigroup S] [star_semigroup R] [star_semigroup S] :
  star_semigroup (R × S) :=
{ star_mul := λ _ _, prod.ext (star_mul _ _) (star_mul _ _) }

instance [add_monoid R] [add_monoid S] [star_add_monoid R] [star_add_monoid S] :
  star_add_monoid (R × S) :=
{ star_add := λ _ _, prod.ext (star_add _ _) (star_add _ _) }

instance [non_unital_semiring R] [non_unital_semiring S] [star_ring R] [star_ring S] :
  star_ring (R × S) :=
{ ..prod.star_add_monoid, ..(prod.star_semigroup : star_semigroup (R × S)) }

instance {α : Type w} [has_smul α R] [has_smul α S] [has_star α] [has_star R] [has_star S]
  [star_module α R] [star_module α S] :
  star_module α (R × S) :=
{ star_smul := λ r x, prod.ext (star_smul _ _) (star_smul _ _) }

end prod

@[simp] lemma units.embed_product_star [monoid R] [star_semigroup R] (u : Rˣ) :
  units.embed_product R (star u) = star (units.embed_product R u) := rfl
