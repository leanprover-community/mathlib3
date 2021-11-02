/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra

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
class graded_ring.core :=
( decompose : R → ⨁ i, A i)
( one_degree_zero : (1 : R) ∈ A 0 )
( mul_respect_grading : ∀ {i j : ι} {a b : R}, a ∈ A i → b ∈ A j → a * b ∈ A (i + j))

class graded_ring extends graded_ring.core R A :=
( left_inv : function.left_inverse decompose (direct_sum.add_subgroup_coe A) )
( right_inv : function.right_inverse decompose (direct_sum.add_subgroup_coe A) )

variable [graded_ring R A]

lemma graded_ring.is_internal : direct_sum.add_subgroup_is_internal A :=
⟨graded_ring.left_inv.injective, graded_ring.right_inv.surjective⟩

instance gsemiring.of_ring_is_internally_graded :
  direct_sum.gsemiring (λ i, A i) :=
direct_sum.gsemiring.of_add_subgroups A
  (graded_ring.core.one_degree_zero) (λ i j ai aj, graded_ring.core.mul_respect_grading ai.2 aj.2)

/--If `R` is graded by `ι` with degree `i` component `A i`, then `(⨁ i, A i ≃+* R)`-/
def graded_ring.recompose : (⨁ i, A i) ≃+* R :=
let f : (⨁ i, A i) →+* R :=
  direct_sum.to_semiring (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl) in
{ to_fun := f,
  inv_fun := graded_ring.core.decompose,
  left_inv := graded_ring.left_inv,
  right_inv := graded_ring.right_inv,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _, }

@[simp] lemma graded_ring.decompose_def :
  graded_ring.core.decompose = (graded_ring.recompose R A).symm := rfl

@[simp] lemma graded_ring.recompose_of {i : ι} (x : A i) :
  graded_ring.recompose R A (direct_sum.of _ i x) = x :=
begin
  unfold graded_ring.recompose,
  unfold direct_sum.of,
  simp only [dfinsupp.single_add_hom_apply, direct_sum.to_semiring_apply, ring_equiv.coe_mk],
  erw dfinsupp.lift_add_hom_apply_single _, refl,
end

/-- The projection maps of graded ring-/
def graded_ring.proj (i : ι) : R →+ R :=
(A i).subtype.comp $
  (dfinsupp.eval_add_monoid_hom i).comp $
  (graded_ring.recompose R A).symm.to_add_monoid_hom

lemma graded_ring.proj_apply (i : ι) (r : R) :
  graded_ring.proj _ A i r = (graded_ring.core.decompose r : ⨁ i, A i) i := rfl

lemma graded_ring.proj_mem (i : ι) (r : R) :
  graded_ring.proj R A i r ∈ A i := (@graded_ring.core.decompose R _ ι A _ _ _ r i).2

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def graded_ring.support [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]
  (r : R) : finset ι :=
(@graded_ring.core.decompose R _ ι A _ _ _ r).support

lemma graded_ring.proj_recompose (a : ⨁ i, A i) (i : ι) :
  graded_ring.proj R A i (graded_ring.recompose R A a) =
  graded_ring.recompose R A (direct_sum.of _ i (a i)) :=
begin
  unfold graded_ring.proj,
  simp only [add_monoid_hom.coe_comp, add_subgroup.coe_subtype, function.comp_app,
    graded_ring.recompose_of, set_like.coe_eq_coe],
  erw ring_equiv.symm_apply_apply, refl,
end

end graded_ring
