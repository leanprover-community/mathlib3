/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.hom.non_unital_alg
import algebra.lie.basic

/-!
# Lie algebras as non-unital, non-associative algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The definition of Lie algebras uses the `has_bracket` typeclass for multiplication whereas we have a
separate `has_mul` typeclass used for general algebras.

It is useful to have a special typeclass for Lie algebras because:
 * it enables us to use the traditional notation `⁅x, y⁆` for the Lie multiplication,
 * associative algebras carry a natural Lie algebra structure via the ring commutator and so we need
   them to carry both `has_mul` and `has_bracket` simultaneously,
 * more generally, Poisson algebras (not yet defined) need both typeclasses.

However there are times when it is convenient to be able to regard a Lie algebra as a general
algebra and we provide some basic definitions for doing so here.

## Main definitions

  * `commutator_ring` turns a Lie ring into a `non_unital_non_assoc_semiring` by turning its
    `has_bracket` (denoted `⁅, ⁆`) into a `has_mul` (denoted `*`).
  * `lie_hom.to_non_unital_alg_hom`

## Tags

lie algebra, non-unital, non-associative
-/

universes u v w

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

/-- Type synonym for turning a `lie_ring` into a `non_unital_non_assoc_semiring`.

A `lie_ring` can be regarded as a `non_unital_non_assoc_semiring` by turning its
`has_bracket` (denoted `⁅, ⁆`) into a `has_mul` (denoted `*`). -/
def commutator_ring (L : Type v) : Type v := L

/-- A `lie_ring` can be regarded as a `non_unital_non_assoc_semiring` by turning its
`has_bracket` (denoted `⁅, ⁆`) into a `has_mul` (denoted `*`). -/
instance : non_unital_non_assoc_semiring (commutator_ring L) :=
show non_unital_non_assoc_semiring L, from
{ mul           := has_bracket.bracket,
  left_distrib  := lie_add,
  right_distrib := add_lie,
  zero_mul      := zero_lie,
  mul_zero      := lie_zero,
  .. (infer_instance : add_comm_monoid L) }

namespace lie_algebra

instance (L : Type v) [nonempty L] : nonempty (commutator_ring L) :=
‹nonempty L›

instance (L : Type v) [inhabited L] : inhabited (commutator_ring L) :=
‹inhabited L›

instance : lie_ring (commutator_ring L) :=
show lie_ring L, by apply_instance

instance : lie_algebra R (commutator_ring L) :=
show lie_algebra R L, by apply_instance

/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
reinterpret the `smul_lie` law as an `is_scalar_tower`. -/
instance is_scalar_tower : is_scalar_tower R (commutator_ring L) (commutator_ring L) := ⟨smul_lie⟩

/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
reinterpret the `lie_smul` law as an `smul_comm_class`. -/
instance smul_comm_class : smul_comm_class R (commutator_ring L) (commutator_ring L) :=
⟨λ t x y, (lie_smul t x y).symm⟩

end lie_algebra

namespace lie_hom

variables {R L} {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂]

/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
regard a `lie_hom` as a `non_unital_alg_hom`. -/
@[simps]
def to_non_unital_alg_hom (f : L →ₗ⁅R⁆ L₂) : commutator_ring L →ₙₐ[R] commutator_ring L₂ :=
{ to_fun := f,
  map_zero' := f.map_zero,
  map_mul'  := f.map_lie,
  ..f }

lemma to_non_unital_alg_hom_injective :
  function.injective (to_non_unital_alg_hom : _ → (commutator_ring L →ₙₐ[R] commutator_ring L₂)) :=
λ f g h, ext $ non_unital_alg_hom.congr_fun h

end lie_hom
