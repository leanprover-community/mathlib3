/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum_semiring
import ring_theory.subring

/-!
# The ring structure on `⨁ i, M i` when `M i : add_subgroup S`

This module provides a typeclass `ring_add_gradation M` that shows `M : ι → add_subgroup S` is an
additive gradation of `S`, such that:

* `1 ∈ M 0`
* `x ∈ M i → y ∈ M j → (x * y) ∈ M (i + j)`

When this typeclass is present, it imbues a `ring` structure over `⨁ i, M i`.begin

If the `M i` are disjoint, this is a gradation of `⨆ i, M i : subring S`. If
`i ≤ j → M i ≤ M j`, then this is filtration of `⨆ i, M i : subring S`.

## tags

graded ring, filtered ring, direct sum, add_subgroup -/

variables {S : Type*} [ring S] {ι : Type*} [add_monoid ι] [decidable_eq ι]

namespace direct_sum

/-- A type class to indicate that multiplication is closed within `carriers` under addition of the
indices. -/
class ring_add_gradation (carriers : ι → add_subgroup S) :=
(one_mem : (1 : S) ∈ carriers 0)
(mul_mem : ∀ {i j} (gi : carriers i) (gj : carriers j), (gi * gj : S) ∈ carriers (i + j))

variables (carriers : ι → add_subgroup S) [ring_add_gradation carriers]

namespace ring_add_gradation

instance ring_add_gradation.to_semiring_add_gradation :
  semiring_add_gradation (λ i, (carriers i).to_add_submonoid) :=
{ one_mem := one_mem,
  mul_mem := λ i j gi gj, mul_mem gi gj}


open_locale direct_sum

instance semiring : semiring (⨁ i, carriers i) := begin
  haveI : Π (i : ι), add_comm_monoid ↥((carriers i).to_add_submonoid) := λ i, infer_instance,
  exact direct_sum.semiring_add_gradation.semiring (λ i, (carriers i).to_add_submonoid),
end

/-- The ring structure on `⨁ i, carriers i` in the presence of `ring_add_gradation carriers`. -/
instance ring : ring (⨁ i, carriers i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.ring_add_gradation.semiring _),
  ..(direct_sum.add_comm_group _), }

end ring_add_gradation

end direct_sum
