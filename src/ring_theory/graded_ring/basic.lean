/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import algebra.direct_sum.internal

/-! # Typeclass for graded ring
For definition of a ring `R` being graded by `A : ι → add_subgroup R`, see doc string of
`graded_ring`.

- `graded_ring.decompose : R → ⨁ i, A i` and `graded_ring.recompose : ⨁ i, A i → R` are the ring
isomorphism between `R` and `⨁ i, A i` if `R` is graded by `A`.
- `graded_ring.complete_lattice.independent` states that the `A` is independent in the sense that
for any `i : ι`, `A i` and `⨆ (j ≠ i), A j` intersect trivially. The most noticable consequence of
this is that `A i` and `A j` intersects trivally for distinct `i` and `j`.
- `graded_ring.proj R A i r` is the degree `i : ι` component of `r : R`.
- `graded_ring.support R A r` is the `finset ι` containing the `i : ι` such that the degree `i`
component of `r` is not zero.
- `is_homogeneous R A x` states that `x ∈ A i` for some `i : ι`.
- `homogeneous_element R A` is the subtype of `R` of all `x` such that `is_homogeneous R A x`.
- `mv_polynomial_is_graded` provides an instance saying that `mv_polynomial R σ` is ring graded by
its homogeneous components.
-/

open_locale direct_sum big_operators

section graded_ring
variables (R : Type*) [ring R] {ι : Type*} (A : ι → add_subgroup R)
  [decidable_eq ι] [add_comm_monoid ι]

/-- A graded ring is a `ring R` such that `R` can be decomposed into a collection of
  `add_subgroups R` indexed by `ι` such that the connonical map `R → ⨁ i, A i` is a bijective map
  respecting multiplication, i.e. product of an element of degree `i` and an element of degree `j`
  is an element of degree `i + j`.
-/
class graded_ring extends set_like.graded_monoid A :=
( decompose : R → ⨁ i, A i)
( left_inv : function.left_inverse decompose (direct_sum.add_subgroup_coe A) )
( right_inv : function.right_inverse decompose (direct_sum.add_subgroup_coe A) )

lemma graded_ring.is_internal [graded_ring R A] : direct_sum.add_subgroup_is_internal A :=
⟨graded_ring.left_inv.injective, graded_ring.right_inv.surjective⟩

variable [graded_ring R A]

/--If `R` is graded by `ι` with degree `i` component `A i`, then `(⨁ i, A i ≃+* R)`-/
def graded_ring.recompose : (⨁ i, A i) ≃+* R :=
{ to_fun := direct_sum.subgroup_coe_ring_hom A,
  inv_fun := graded_ring.decompose,
  left_inv := graded_ring.left_inv,
  right_inv := graded_ring.right_inv,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _, }

@[simp] lemma graded_ring.decompose_def :
  graded_ring.decompose = (graded_ring.recompose R A).symm := rfl

@[simp] lemma graded_ring.recompose_of {i : ι} (x : A i) :
  graded_ring.recompose R A (direct_sum.of _ i x) = x := dfinsupp.lift_add_hom_apply_single _ _ _

end graded_ring
