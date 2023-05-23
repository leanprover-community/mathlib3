/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum.algebra
import algebra.monoid_algebra.basic
import data.finsupp.to_dfinsupp

/-!
# Conversion between `add_monoid_algebra` and homogenous `direct_sum`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides conversions between `add_monoid_algebra` and `direct_sum`.
The latter is essentially a dependent version of the former.

Note that since `direct_sum.has_mul` combines indices additively, there is no equivalent to
`monoid_algebra`.

## Main definitions

* `add_monoid_algebra.to_direct_sum : add_monoid_algebra M ι → (⨁ i : ι, M)`
* `direct_sum.to_add_monoid_algebra : (⨁ i : ι, M) → add_monoid_algebra M ι`
* Bundled equiv versions of the above:
  * `add_monoid_algebra_equiv_direct_sum : add_monoid_algebra M ι ≃ (⨁ i : ι, M)`
  * `add_monoid_algebra_add_equiv_direct_sum : add_monoid_algebra M ι ≃+ (⨁ i : ι, M)`
  * `add_monoid_algebra_ring_equiv_direct_sum R : add_monoid_algebra M ι ≃+* (⨁ i : ι, M)`
  * `add_monoid_algebra_alg_equiv_direct_sum R : add_monoid_algebra A ι ≃ₐ[R] (⨁ i : ι, A)`

## Theorems

The defining feature of these operations is that they map `finsupp.single` to
`direct_sum.of` and vice versa:

* `add_monoid_algebra.to_direct_sum_single`
* `direct_sum.to_add_monoid_algebra_of`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to
`add_monoid_algebra.to_direct_sum`:

* `add_monoid_algebra_add_equiv_direct_sum_apply`
* `add_monoid_algebra_lequiv_direct_sum_apply`
* `add_monoid_algebra_add_equiv_direct_sum_symm_apply`
* `add_monoid_algebra_lequiv_direct_sum_symm_apply`

## Implementation notes

This file largely just copies the API of `data/finsupp/to_dfinsupp`, and reuses the proofs.
Recall that `add_monoid_algebra M ι` is defeq to `ι →₀ M` and `⨁ i : ι, M` is defeq to
`Π₀ i : ι, M`.

Note that there is no `add_monoid_algebra` equivalent to `finsupp.single`, so many statements
still involve this definition.
-/

variables {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

open_locale direct_sum

/-! ### Basic definitions and lemmas -/
section defs

/-- Interpret a `add_monoid_algebra` as a homogenous `direct_sum`. -/
def add_monoid_algebra.to_direct_sum [semiring M] (f : add_monoid_algebra M ι) : ⨁ i : ι, M :=
finsupp.to_dfinsupp f

section
variables [decidable_eq ι] [semiring M]

@[simp] lemma add_monoid_algebra.to_direct_sum_single (i : ι) (m : M) :
  add_monoid_algebra.to_direct_sum (finsupp.single i m) = direct_sum.of _ i m :=
finsupp.to_dfinsupp_single i m

variables [Π m : M, decidable (m ≠ 0)]

/-- Interpret a homogenous `direct_sum` as a `add_monoid_algebra`. -/
def direct_sum.to_add_monoid_algebra (f : ⨁ i : ι, M) :
  add_monoid_algebra M ι :=
dfinsupp.to_finsupp f

@[simp] lemma direct_sum.to_add_monoid_algebra_of (i : ι) (m : M) :
  (direct_sum.of _ i m : ⨁ i : ι, M).to_add_monoid_algebra = finsupp.single i m :=
dfinsupp.to_finsupp_single i m

@[simp] lemma add_monoid_algebra.to_direct_sum_to_add_monoid_algebra (f : add_monoid_algebra M ι) :
  f.to_direct_sum.to_add_monoid_algebra = f :=
finsupp.to_dfinsupp_to_finsupp f

@[simp] lemma direct_sum.to_add_monoid_algebra_to_direct_sum (f : ⨁ i : ι, M) :
  f.to_add_monoid_algebra.to_direct_sum = f :=
dfinsupp.to_finsupp_to_dfinsupp f

end

end defs

/-! ### Lemmas about arithmetic operations -/
section lemmas

namespace add_monoid_algebra

@[simp] lemma to_direct_sum_zero [semiring M] :
  (0 : add_monoid_algebra M ι).to_direct_sum = 0 := finsupp.to_dfinsupp_zero

@[simp] lemma to_direct_sum_add [semiring M] (f g : add_monoid_algebra M ι) :
  (f + g).to_direct_sum = f.to_direct_sum + g.to_direct_sum := finsupp.to_dfinsupp_add _ _

@[simp] lemma to_direct_sum_mul [decidable_eq ι] [add_monoid ι] [semiring M]
  (f g : add_monoid_algebra M ι) :
  (f * g).to_direct_sum = f.to_direct_sum * g.to_direct_sum :=
begin
  let to_hom : add_monoid_algebra M ι →+ (⨁ i : ι, M) :=
    ⟨to_direct_sum, to_direct_sum_zero, to_direct_sum_add⟩,
  show to_hom (f * g) = to_hom f * to_hom g,
  revert f g,
  rw add_monoid_hom.map_mul_iff,
  ext xi xv yi yv : 4,
  dsimp only [add_monoid_hom.comp_apply, add_monoid_hom.compl₂_apply,
    add_monoid_hom.compr₂_apply, add_monoid_hom.mul_apply, add_equiv.coe_to_add_monoid_hom,
    finsupp.single_add_hom_apply],
  simp only [add_monoid_algebra.single_mul_single, to_hom, add_monoid_hom.coe_mk,
      add_monoid_algebra.to_direct_sum_single, direct_sum.of_mul_of, has_mul.ghas_mul_mul]
end

end add_monoid_algebra

namespace direct_sum
variables [decidable_eq ι]

@[simp] lemma to_add_monoid_algebra_zero [semiring M] [Π m : M, decidable (m ≠ 0)] :
  to_add_monoid_algebra 0 = (0 : add_monoid_algebra M ι) := dfinsupp.to_finsupp_zero

@[simp] lemma to_add_monoid_algebra_add [semiring M] [Π m : M, decidable (m ≠ 0)]
  (f g : ⨁ i : ι, M) :
  (f + g).to_add_monoid_algebra = to_add_monoid_algebra f + to_add_monoid_algebra g :=
dfinsupp.to_finsupp_add _ _

@[simp] lemma to_add_monoid_algebra_mul [add_monoid ι] [semiring M] [Π m : M, decidable (m ≠ 0)]
  (f g : ⨁ i : ι, M) :
  (f * g).to_add_monoid_algebra = to_add_monoid_algebra f * to_add_monoid_algebra g :=
begin
  apply_fun add_monoid_algebra.to_direct_sum,
  { simp },
  { apply function.left_inverse.injective,
    apply add_monoid_algebra.to_direct_sum_to_add_monoid_algebra }
end

end direct_sum

end lemmas

/-! ### Bundled `equiv`s -/

section equivs

/-- `add_monoid_algebra.to_direct_sum` and `direct_sum.to_add_monoid_algebra` together form an
equiv. -/
@[simps {fully_applied := ff}]
def add_monoid_algebra_equiv_direct_sum [decidable_eq ι] [semiring M] [Π m : M, decidable (m ≠ 0)] :
  add_monoid_algebra M ι ≃ (⨁ i : ι, M) :=
{ to_fun := add_monoid_algebra.to_direct_sum, inv_fun := direct_sum.to_add_monoid_algebra,
  ..finsupp_equiv_dfinsupp }

/-- The additive version of `add_monoid_algebra.to_add_monoid_algebra`. Note that this is
`noncomputable` because `add_monoid_algebra.has_add` is noncomputable. -/
@[simps {fully_applied := ff}]
def add_monoid_algebra_add_equiv_direct_sum
  [decidable_eq ι] [semiring M] [Π m : M, decidable (m ≠ 0)] :
  add_monoid_algebra M ι ≃+ (⨁ i : ι, M) :=
{ to_fun := add_monoid_algebra.to_direct_sum, inv_fun := direct_sum.to_add_monoid_algebra,
  map_add' := add_monoid_algebra.to_direct_sum_add,
  .. add_monoid_algebra_equiv_direct_sum}

/-- The ring version of `add_monoid_algebra.to_add_monoid_algebra`. Note that this is
`noncomputable` because `add_monoid_algebra.has_add` is noncomputable. -/
@[simps {fully_applied := ff}]
def add_monoid_algebra_ring_equiv_direct_sum
  [decidable_eq ι] [add_monoid ι] [semiring M]
  [Π m : M, decidable (m ≠ 0)] :
  add_monoid_algebra M ι ≃+* ⨁ i : ι, M :=
{ to_fun := add_monoid_algebra.to_direct_sum, inv_fun := direct_sum.to_add_monoid_algebra,
  map_mul' := add_monoid_algebra.to_direct_sum_mul,
  ..(add_monoid_algebra_add_equiv_direct_sum : add_monoid_algebra M ι ≃+ ⨁ i : ι, M) }

/-- The algebra version of `add_monoid_algebra.to_add_monoid_algebra`. Note that this is
`noncomputable` because `add_monoid_algebra.has_add` is noncomputable. -/
@[simps {fully_applied := ff}]
def add_monoid_algebra_alg_equiv_direct_sum
  [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
  [Π m : A, decidable (m ≠ 0)] :
  add_monoid_algebra A ι ≃ₐ[R] ⨁ i : ι, A :=
{ to_fun := add_monoid_algebra.to_direct_sum, inv_fun := direct_sum.to_add_monoid_algebra,
  commutes' := λ r, add_monoid_algebra.to_direct_sum_single _ _,
  ..(add_monoid_algebra_ring_equiv_direct_sum : add_monoid_algebra A ι ≃+* ⨁ i : ι, A) }

end equivs
