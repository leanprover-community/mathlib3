/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import algebra.direct_sum.internal

/-!
# Internally-graded algebras

This file defines the typeclass `graded_algebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `graded_algebra 𝒜`: the typeclass, which is a combination of `set_like.graded_monoid`, and
  a constructive version of `direct_sum.submodule_is_internal 𝒜`.
* `graded_algebra.decompose : A ≃ₐ[R] ⨁ i, 𝒜 i`, which breaks apart an element of the algebra into
  its constituent pieces.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → submodule ℕ A` and `𝒜 : ι → submodule ℤ A` respectively, since all
`semiring`s are ℕ-algebras via `algebra_nat`, and all `ring`s are `ℤ`-algebras via `algebra_int`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/

open_locale direct_sum big_operators

section graded_algebra

variables {ι R A : Type*}
variables [decidable_eq ι] [add_comm_monoid ι] [comm_semiring R] [ring A] [algebra R A]
variables (𝒜 : ι → submodule R A)

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `graded_algebra 𝒜`, implies an externally-graded
algebra structure `direct_sum.galgebra R (λ i, ↥(𝒜 i))`, which in turn makes available an
`algebra R (⨁ i, 𝒜 i)` instance.
-/
class graded_algebra extends set_like.graded_monoid 𝒜 :=
(decompose' : A → ⨁ i, 𝒜 i)
(left_inv : function.left_inverse decompose' (direct_sum.submodule_coe 𝒜))
(right_inv : function.right_inverse decompose' (direct_sum.submodule_coe 𝒜))

lemma graded_ring.is_internal [graded_algebra 𝒜] :
  direct_sum.submodule_is_internal 𝒜 :=
⟨graded_algebra.left_inv.injective, graded_algebra.right_inv.surjective⟩

variable [graded_algebra 𝒜]

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
an algebra to a direct sum of components. -/
def graded_algebra.decompose : A ≃ₐ[R] ⨁ i, 𝒜 i := alg_equiv.symm
{ to_fun := direct_sum.submodule_coe_alg_hom 𝒜,
  inv_fun := graded_algebra.decompose',
  left_inv := graded_algebra.left_inv,
  right_inv := graded_algebra.right_inv,
  map_mul' := alg_hom.map_mul _,
  map_add' := alg_hom.map_add _,
  commutes' := alg_hom.commutes _ }

@[simp] lemma graded_algebra.decompose'_def :
  graded_algebra.decompose' = graded_algebra.decompose 𝒜 := rfl

@[simp] lemma graded_algebra.decompose_symm_of {i : ι} (x : 𝒜 i) :
  (graded_algebra.decompose 𝒜).symm (direct_sum.of _ i x) = x :=
direct_sum.submodule_coe_alg_hom_of 𝒜 _ _

/-- The projection maps of graded algebra-/
def graded_algebra.proj (𝒜 : ι → submodule R A) [graded_algebra 𝒜] (i : ι) : A →ₗ[R] A :=
(𝒜 i).subtype.comp $
  (dfinsupp.lapply i).comp $
  (graded_algebra.decompose 𝒜).to_alg_hom.to_linear_map

@[simp] lemma graded_algebra.proj_apply (i : ι) (r : A) :
  graded_algebra.proj 𝒜 i r = (graded_algebra.decompose 𝒜 r : ⨁ i, 𝒜 i) i := rfl

lemma graded_algebra.proj_mem (i : ι) (r : A) :
  graded_algebra.proj 𝒜 i r ∈ 𝒜 i := (graded_algebra.decompose 𝒜 r i).2

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def graded_algebra.support [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]
  (r : A) : finset ι :=
(graded_algebra.decompose 𝒜 r).support

lemma graded_algebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
  graded_algebra.proj 𝒜 i ((graded_algebra.decompose 𝒜).symm a) =
  (graded_algebra.decompose 𝒜).symm (direct_sum.of _ i (a i)) :=
by rw [graded_algebra.proj_apply, graded_algebra.decompose_symm_of, alg_equiv.apply_symm_apply]

variable [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]

lemma graded_ring.mem_support_iff
  (r : A) (i : ι) :
i ∈ graded_algebra.support 𝒜 r ↔ (graded_algebra.proj 𝒜 i r ≠ 0) :=
⟨λ hi, begin
  contrapose! hi,
  unfold graded_algebra.support,
  unfold graded_algebra.proj at hi,
  rw [dfinsupp.mem_support_iff, not_not],
  simp only [submodule.subtype_apply, dfinsupp.lapply_apply, alg_equiv.to_alg_hom_eq_coe,
    function.comp_app, linear_map.coe_comp, alg_equiv.to_alg_hom_to_linear_map,
    alg_equiv.to_linear_map_apply, submodule.coe_eq_zero] at hi,
  exact hi,
end, λ hi, begin
  unfold graded_algebra.proj at hi,
  unfold graded_algebra.support,
  simp only [ne.def, dfinsupp.mem_support_to_fun],
  intro rid,
  simp only [submodule.subtype_apply, dfinsupp.lapply_apply, alg_equiv.to_alg_hom_eq_coe,
    function.comp_app, linear_map.coe_comp, alg_equiv.to_alg_hom_to_linear_map,
    alg_equiv.to_linear_map_apply, submodule.coe_eq_zero] at hi,
  rw rid at hi,
  simp only [eq_self_iff_true, not_true, ne.def, submodule.coe_zero] at hi,
  exact hi,
end⟩

lemma graded_algebra.as_sum (r : A) :
  r = ∑ i in graded_algebra.support 𝒜 r, graded_algebra.proj 𝒜 i r :=
begin
  conv_lhs { rw [←@graded_algebra.right_inv ι R A _ _ _ _ _ 𝒜 _ r,
    graded_algebra.decompose'_def,
    ←direct_sum.sum_support_of _ (graded_algebra.decompose 𝒜 r), linear_map.map_sum] },
  unfold graded_algebra.support,
  apply finset.sum_congr rfl,
  intros i hi,
  rw [direct_sum.submodule_coe_of],
  refl,
end

lemma graded_ring.mul_proj (r r' : A) (i : ι) :
  graded_algebra.proj 𝒜 i (r * r') =
  ∑ ij in finset.filter (λ ij : ι × ι, ij.1 + ij.2 = i)
    ((graded_algebra.support 𝒜 r).product (graded_algebra.support 𝒜 r')),
    (graded_algebra.proj 𝒜 ij.1 r) * (graded_algebra.proj 𝒜 ij.2 r') :=
begin
  have set_eq : (graded_algebra.support 𝒜 r).product (graded_algebra.support 𝒜 r') =
  finset.filter (λ ij : ι × ι, ij.1 + ij.2 = i) _ ∪
  finset.filter (λ ij : ι × ι, ij.1 + ij.2 ≠ i) _ := (finset.filter_union_filter_neg_eq _ _).symm,
  conv_lhs { rw [graded_algebra.as_sum 𝒜 r, graded_algebra.as_sum 𝒜 r', finset.sum_mul_sum,
    linear_map.map_sum, set_eq] },
  rw finset.sum_union,
  suffices : ∑ (x : ι × ι) in finset.filter (λ (ij : ι × ι), ij.fst + ij.snd ≠ i)
    ((graded_algebra.support 𝒜 r).product (graded_algebra.support 𝒜 r')),
  (graded_algebra.proj 𝒜 i) (graded_algebra.proj 𝒜 x.fst r * graded_algebra.proj 𝒜 x.snd r') = 0,
  rw [this, add_zero], apply finset.sum_congr rfl,
  rintros ⟨j, k⟩ h, simp only [finset.mem_filter, finset.mem_product] at h ⊢,
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h,
  rw ←h₃,
  obtain ⟨a, rfl⟩ := (graded_algebra.decompose 𝒜).symm.bijective.surjective r,
  obtain ⟨b, rfl⟩ := (graded_algebra.decompose 𝒜).symm.bijective.surjective r',
  rw [graded_algebra.proj_recompose, graded_algebra.proj_recompose, ←alg_equiv.map_mul,
    direct_sum.of_mul_of, graded_algebra.proj_recompose],
  congr, rw [direct_sum.of_eq_same],

  apply finset.sum_eq_zero, rintros ⟨j, k⟩ h,
  simp only [ne.def, finset.mem_filter, finset.mem_product] at h ⊢,
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h,
  obtain ⟨a, rfl⟩ := (graded_algebra.decompose 𝒜).symm.bijective.surjective r,
  obtain ⟨b, rfl⟩ := (graded_algebra.decompose 𝒜).symm.bijective.surjective r',
  rw [graded_algebra.proj_recompose, graded_algebra.proj_recompose, ←alg_equiv.map_mul,
    direct_sum.of_mul_of, graded_algebra.proj_recompose, direct_sum.of_eq_of_ne],
  simp only [ring_equiv.map_zero, add_monoid_hom.map_zero],
  rw [alg_equiv.map_zero],
  intro rid, exact h₃ rid,

  rw [finset.disjoint_iff_inter_eq_empty, finset.eq_empty_iff_forall_not_mem],
  rintros ⟨j, k⟩ rid,
  simp only [ne.def, finset.mem_filter, finset.mem_inter, finset.mem_product] at rid,
  rcases rid with ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩, exact h₂ h₁,
end

lemma graded_algebra.proj_homogeneous_element {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
  graded_algebra.proj 𝒜 i x = x :=
begin
  rw [graded_algebra.proj_apply, ←subtype.coe_mk x hx, subtype.coe_injective.eq_iff,
    ←graded_algebra.decompose_symm_of, alg_equiv.apply_symm_apply, direct_sum.of_eq_same],
end


lemma graded_ring.proj_homogeneous_element_of_ne {x : A} {i j : ι} (hx : x ∈ 𝒜 i) (hij : i ≠ j):
  graded_algebra.proj 𝒜 j x = 0 :=
begin
  rw ←graded_algebra.proj_homogeneous_element 𝒜 hx,
  obtain ⟨a, rfl⟩ := (graded_algebra.decompose 𝒜).symm.bijective.surjective x,
  rw [graded_algebra.proj_recompose, graded_algebra.proj_recompose, direct_sum.of_eq_of_ne,
    add_monoid_hom.map_zero, alg_equiv.map_zero], exact hij,
end

end graded_algebra
