/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum_semiring
import ring_theory.subring

/-!
# The ring structure on `⨁ i, M i` when `M i : add_subgroup R`

This module extends `semiring_add_gradation` to work on `ring`s and `comm_ring`s.

## tags

graded ring, filtered ring, direct sum, add_subgroup -/

variables {R : Type*} [ring R] {ι : Type*} [add_monoid ι] [decidable_eq ι]
variables {R' : Type*} [comm_ring R'] {ι' : Type*} [add_comm_monoid ι'] [decidable_eq ι']

namespace direct_sum

/-- A type class to indicate that multiplication is closed within `carriers` under addition of the
indices. -/
class ring_add_gradation (carriers : ι → add_subgroup R) :=
(one_mem : (1 : R) ∈ carriers 0)
(mul_mem : ∀ {i j} (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j))

variables (carriers : ι → add_subgroup R) [ring_add_gradation carriers]
variables (carriers' : ι' → add_subgroup R') [ring_add_gradation carriers']

namespace ring_add_gradation

instance ring_add_gradation.to_semiring_add_gradation :
  semiring_add_gradation (λ i, (carriers i).to_add_submonoid) :=
{ one_mem := one_mem,
  mul_mem := λ i j gi gj, mul_mem gi gj}

open_locale direct_sum

instance semiring : semiring (⨁ i, carriers i) := begin
  haveI : Π i, add_comm_monoid ↥((carriers i).to_add_submonoid) := λ i, infer_instance,
  exact direct_sum.semiring_add_gradation.semiring (λ i, (carriers i).to_add_submonoid),
end

instance comm_semiring : comm_semiring (⨁ i, carriers' i) := begin
  haveI : Π i, add_comm_monoid ↥((carriers' i).to_add_submonoid) := λ i, infer_instance,
  exact direct_sum.semiring_add_gradation.comm_semiring (λ i, (carriers' i).to_add_submonoid),
end

/-- The `ring` derived from `ring_add_gradation carriers`. -/
instance ring : ring (⨁ i, carriers i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.ring_add_gradation.semiring _),
  ..(direct_sum.add_comm_group _), }

/-- The `comm_ring` derived from `ring_add_gradation carriers'`. -/
instance comm_ring : ring (⨁ i, carriers' i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.ring_add_gradation.ring _),
  ..(direct_sum.ring_add_gradation.comm_semiring _), }

end ring_add_gradation

end direct_sum
