/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/

import algebra.direct_sum.algebra

/-!
# Internally graded rings and algebras

This module provides `gsemiring` and `gcomm_semiring` instances for a collection of subobjects `A`
when a `set_like.graded_monoid` instance is available:

* on `add_submonoid R`s: `add_submonoid.gsemiring`, `add_submonoid.gcomm_semiring`.
* on `add_subgroup R`s: `add_subgroup.gsemiring`, `add_subgroup.gcomm_semiring`.
* on `submodule S R`s: `submodule.gsemiring`, `submodule.gcomm_semiring`.

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `direct_sum.add_submonoid_coe_ring_hom` (a `ring_hom` version of `direct_sum.add_submonoid_coe`)
* `direct_sum.add_subgroup_coe_ring_hom` (a `ring_hom` version of `direct_sum.add_subgroup_coe`)
* `direct_sum.submodule_coe_alg_hom` (an `alg_hom` version of `direct_sum.submodule_coe`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : direct_sum.submodule_is_internal A) [set_like.graded_monoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`direct_sum.submodule_is_internal` for providing an explicit decomposition function.

When `complete_lattice.independent (set.range A)` (a weaker condition than
`direct_sum.submodule_is_internal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

internally graded ring
-/

open_locale direct_sum

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

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
def direct_sum.submonoid_coe_ring_hom [add_monoid ι] [semiring R]
  (A : ι → add_submonoid R) [h : set_like.graded_monoid A] : (⨁ i, A i) →+* R :=
direct_sum.to_semiring (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl)

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp] lemma direct_sum.submonoid_coe_ring_hom_of [add_monoid ι] [semiring R]
  (A : ι → add_submonoid R) [h : set_like.graded_monoid A] (i : ι) (x : A i) :
  direct_sum.submonoid_coe_ring_hom A (direct_sum.of (λ i, A i) i x) = x :=
direct_sum.to_semiring_of _ _ _ _ _

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

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`. -/
def direct_sum.subgroup_coe_ring_hom [add_monoid ι] [ring R]
  (A : ι → add_subgroup R) [set_like.graded_monoid A] : (⨁ i, A i) →+* R :=
direct_sum.to_semiring (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl)

@[simp] lemma direct_sum.subgroup_coe_ring_hom_of [add_monoid ι] [ring R]
  (A : ι → add_subgroup R) [set_like.graded_monoid A] (i : ι) (x : A i) :
  direct_sum.subgroup_coe_ring_hom A (direct_sum.of (λ i, A i) i x) = x :=
direct_sum.to_semiring_of _ _ _ _ _

/-! #### From `submodules`s -/

namespace submodule

/-- Build a `gsemiring` instance for a collection of `submodule`s. -/
instance gsemiring [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [h : set_like.graded_monoid A] :
  direct_sum.gsemiring (λ i, A i) :=
have i' : set_like.graded_monoid (λ i, (A i).to_add_submonoid) := {..h},
by exactI add_submonoid.gsemiring (λ i, (A i).to_add_submonoid)

/-- Build a `gsemiring` instance for a collection of `submodule`s. -/
instance gcomm_semiring [add_comm_monoid ι]
  [comm_semiring S] [comm_semiring R] [algebra S R]
  (A : ι → submodule S R) [h : set_like.graded_monoid A] :
  direct_sum.gcomm_semiring (λ i, A i) :=
have i' : set_like.graded_monoid (λ i, (A i).to_add_submonoid) := {..h},
by exactI add_submonoid.gcomm_semiring (λ i, (A i).to_add_submonoid)

/-- Build a `galgebra` instance for a collection of `submodule`s. -/
instance galgebra [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
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

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def direct_sum.submodule_coe_alg_hom [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [h : set_like.graded_monoid A] : (⨁ i, A i) →ₐ[S] R :=
direct_sum.to_algebra S _ (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl) (λ _, rfl)

@[simp] lemma direct_sum.submodule_coe_alg_hom_of [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [h : set_like.graded_monoid A] (i : ι) (x : A i) :
  direct_sum.submodule_coe_alg_hom A (direct_sum.of (λ i, A i) i x) = x :=
direct_sum.to_semiring_of _ rfl (λ _ _ _ _, rfl) _ _
