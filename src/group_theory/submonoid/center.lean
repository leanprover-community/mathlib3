/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.submonoid.basic
/-!
# Centers of magmas and monoids

## Main definitions

* `set.center`
* `submonoid.center`

-/

variables {M : Type*}

namespace set

variables (M)

@[to_additive add_center]
def center [has_mul M] : set M := {z | ∀ m, m * z = z * m}

@[to_additive mem_add_center]
lemma mem_center_iff [has_mul M] {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := iff.rfl

@[simp, to_additive zero_mem_add_center]
lemma one_mem_center [mul_one_class M] : (1 : M) ∈ set.center M := by simp [mem_center_iff]

variables {M}

@[simp, to_additive add_mem_add_center]
lemma mul_mem_center [semigroup M] {a b : M}
  (ha : a ∈ set.center M) (hb : b ∈ set.center M) : a * b ∈ set.center M :=
λ g, by rw [mul_assoc, ←hb g, ← mul_assoc, ha g, mul_assoc]

@[simp, to_additive neg_mem_add_center]
lemma inv_mem_center [group M] {a : M}
  (ha : a ∈ set.center M) : a⁻¹ ∈ set.center M :=
λ g, by by rw [← inv_inj, mul_inv_rev, inv_inv, ← ha, mul_inv_rev, inv_inv]

end set


namespace submonoid
variables (M) [monoid M]

/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive "The center of a monoid `M` is the set of elements that commute with everything in
`M`"]
def center : submonoid M :=
{ carrier := set.center M,
  one_mem' := set.one_mem_center M,
  mul_mem' := λ a b, set.mul_mem_center }

variable {M}

@[to_additive] lemma mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := iff.rfl

end submonoid
