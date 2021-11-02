/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Eric Wieser, Kevin Buzzard, Jujian Zhang
-/

import algebra.direct_sum.algebra

/-!
# Internally graded rings and algebras

This module imbues collections of subobjects with `gsemiring` and `gcomm_semiring` instances
when a `set_like.graded_monoid` instance is available:

* `A : ι → submonoid R`:
  `add_submonoid.gsemiring`, `add_submonoid.gcomm_semiring`.
* `A : ι → subgroup R`:
  `add_subgroup.gsemiring`, `add_subgroup.gcomm_semiring`.
* `A : ι → submodule S R`:
  `submodule.gsemiring`, `submodule.gcomm_semiring`.

If `complete_lattice.independent (set.range A)`, these provide a gradation of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

internally graded ring
-/

variables {ι : Type*} {S R : Type*} [decidable_eq ι]

/-! #### From `add_submonoid`s -/

namespace add_submonoid

/-- Build a `gsemiring` instance for a collection of `add_submonoid`s. -/
instance gsemiring [add_monoid ι] [semiring R]
  (A : ι → add_submonoid R) [set_like.graded_monoid A] :
  direct_sum.gsemiring (λ i, A i) :=
{ mul_zero := λ i j _, subtype.ext (mul_zero _),
  zero_mul := λ i j _, subtype.ext (zero_mul _),
  mul_add := λ i j _ _ _, subtype.ext (mul_add _ _ _),
  add_mul := λ i j _ _ _, subtype.ext (add_mul _ _ _),
  ..set_like.gmonoid A }

/-- Build a `gcomm_semiring` instance for a collection of `add_submonoid`s. -/
instance gcomm_semiring [add_comm_monoid ι] [comm_semiring R]
  (A : ι → add_submonoid R) [set_like.graded_monoid A] :
  direct_sum.gcomm_semiring (λ i, A i) :=
{ ..set_like.gcomm_monoid A,
  ..add_submonoid.gsemiring A, }

end add_submonoid

/-! #### From `add_subgroup`s -/

namespace add_subgroup

/-- Build a `gsemiring` instance for a collection of `add_subgroup`s. -/
instance gsemiring [add_monoid ι] [ring R]
  (A : ι → add_subgroup R) [h : set_like.graded_monoid A] :
  direct_sum.gsemiring (λ i, A i) :=
have i' : set_like.graded_monoid (λ i, (A i).to_add_submonoid) := {..h},
by exactI add_submonoid.gsemiring (λ i, (A i).to_add_submonoid)

/-- Build a `gcomm_semiring` instance for a collection of `add_subgroup`s. -/
instance gcomm_semiring [add_comm_group ι] [comm_ring R]
  (A : ι → add_subgroup R) [h : set_like.graded_monoid A] :
  direct_sum.gsemiring (λ i, A i) :=
have i' : set_like.graded_monoid (λ i, (A i).to_add_submonoid) := {..h},
by exactI add_submonoid.gsemiring (λ i, (A i).to_add_submonoid)

end add_subgroup

/-! #### From `submodules`s -/

namespace submodule

/-- Build a `gsemiring` instance for a collection of `submodule`s. -/
instance submodule.gsemiring [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [h : set_like.graded_monoid A] :
  direct_sum.gsemiring (λ i, A i) :=
have i' : set_like.graded_monoid (λ i, (A i).to_add_submonoid) := {..h},
by exactI add_submonoid.gsemiring (λ i, (A i).to_add_submonoid)

/-- Build a `gsemiring` instance for a collection of `submodule`s. -/
instance submodule.gcomm_semiring [add_comm_monoid ι]
  [comm_semiring S] [comm_semiring R] [algebra S R]
  (A : ι → submodule S R) [h : set_like.graded_monoid A] :
  direct_sum.gcomm_semiring (λ i, A i) :=
have i' : set_like.graded_monoid (λ i, (A i).to_add_submonoid) := {..h},
by exactI add_submonoid.gcomm_semiring (λ i, (A i).to_add_submonoid)

/-- Build a `galgebra` instance for a collection of `submodule`s. -/
instance submodule.galgebra [add_comm_monoid ι]
  [comm_semiring S] [comm_semiring R] [algebra S R]
  (A : ι → submodule S R) [h : set_like.graded_monoid A] :
  direct_sum.galgebra S (λ i, A i) :=
{ to_fun := begin
    refine ((algebra.linear_map S R).cod_restrict (A 0) $ λ r, _).to_add_monoid_hom,
    exact submodule.one_le.mpr set_like.has_graded_one.one_mem (submodule.algebra_map_mem _),
  end,
  map_one := subtype.ext $ by exact (algebra_map S R).map_one,
  map_mul := λ x y, sigma.subtype_ext (add_zero 0).symm $ (algebra_map S R).map_mul _ _,
  commutes := λ r ⟨i, xi⟩,
    sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) $ algebra.commutes _ _,
  smul_def := λ r ⟨i, xi⟩, sigma.subtype_ext (zero_add i).symm $ algebra.smul_def _ _ }

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_graded_monoid
  [comm_semiring S] [semiring R] [algebra S R] (p : submodule S R) :
  set_like.graded_monoid (λ i : ℕ, p ^ i) :=
{ one_mem := by { rw [←one_le, pow_zero], exact le_rfl },
  mul_mem := λ i j p q hp hq, by { rw pow_add, exact submodule.mul_mem_mul hp hq } }

end submodule
