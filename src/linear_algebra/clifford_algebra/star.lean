/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.conjugation

/-!
# Star structure on `clifford_algebra`

This file defines the "clifford conjugation", equal to `reverse (involute x)`, and assigns it the
`star` notation.

This choice is somewhat non-canonical; a star structure is also possible under `reverse` alone.
However, defining it gives us access to constructions like `unitary`.

Most results about `star` can be obtained by unfolding it via `clifford_algebra.star_def`.

## Main definitions

* `clifford_algebra.star_ring`

-/

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

namespace clifford_algebra

instance : star_ring (clifford_algebra Q) :=
{ star := λ x, reverse (involute x),
  star_involutive := λ x,
    by simp only [reverse_involute_commute.eq, reverse_reverse, involute_involute],
  star_mul := λ x y, by simp only [map_mul, reverse.map_mul],
  star_add := λ x y, by simp only [map_add] }

lemma star_def (x : clifford_algebra Q) : star x = reverse (involute x) := rfl
lemma star_def' (x : clifford_algebra Q) : star x = involute (reverse x) := reverse_involute _

@[simp] lemma star_ι (m : M) : star (ι Q m) = -ι Q m :=
by rw [star_def, involute_ι, map_neg, reverse_ι]

@[simp] lemma star_algebra_map (r : R) :
  star (algebra_map R (clifford_algebra Q) r) = algebra_map R (clifford_algebra Q) r :=
by rw [star_def, involute.commutes, reverse.commutes]

end clifford_algebra
