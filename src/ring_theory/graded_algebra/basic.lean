/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import algebra.direct_sum.internal
import algebra.direct_sum.ring
import group_theory.subgroup.basic

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
* `graded_algebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.
* `graded_algebra.support 𝒜 r` is the `finset ι` containing the `i : ι` such that the degree `i`
  component of `r` is not zero.

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
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
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

lemma graded_algebra.is_internal [graded_algebra 𝒜] :
  direct_sum.submodule_is_internal 𝒜 :=
⟨graded_algebra.left_inv.injective, graded_algebra.right_inv.surjective⟩

/-- A helper to construct a `graded_algebra` when the `set_like.graded_monoid` structure is already
available. This makes the `left_inv` condition easier to prove, and phrases the `right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances]. -/
@[reducible]
def graded_algebra.of_alg_hom [set_like.graded_monoid 𝒜] (decompose : A →ₐ[R] ⨁ i, 𝒜 i)
  (right_inv : (direct_sum.submodule_coe_alg_hom 𝒜).comp decompose = alg_hom.id R A)
  (left_inv : ∀ i (x : 𝒜 i), decompose (x : A) = direct_sum.of (λ i, ↥(𝒜 i)) i x) :
  graded_algebra 𝒜 :=
{ decompose' := decompose,
  right_inv := alg_hom.congr_fun right_inv,
  left_inv := begin
    suffices : decompose.comp (direct_sum.submodule_coe_alg_hom 𝒜) = alg_hom.id _ _,
    from alg_hom.congr_fun this,
    ext i x : 2,
    exact (decompose.congr_arg $ direct_sum.submodule_coe_alg_hom_of _ _ _).trans (left_inv i x),
  end}

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

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def graded_algebra.support [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]
  (r : A) : finset ι :=
(graded_algebra.decompose 𝒜 r).support

lemma graded_algebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
  graded_algebra.proj 𝒜 i ((graded_algebra.decompose 𝒜).symm a) =
  (graded_algebra.decompose 𝒜).symm (direct_sum.of _ i (a i)) :=
by rw [graded_algebra.proj_apply, graded_algebra.decompose_symm_of, alg_equiv.apply_symm_apply]

@[simp] lemma graded_algebra.decompose_coe {i : ι} (x : 𝒜 i) :
  graded_algebra.decompose 𝒜 x = direct_sum.of _ i x :=
by rw [←graded_algebra.decompose_symm_of, alg_equiv.apply_symm_apply]

lemma graded_algebra.decompose_of_mem {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
  graded_algebra.decompose 𝒜 x = direct_sum.of _ i (⟨x, hx⟩ : 𝒜 i) :=
graded_algebra.decompose_coe _ ⟨x, hx⟩

lemma graded_algebra.decompose_of_mem_same {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
  (graded_algebra.decompose 𝒜 x i : A) = x :=
by rw [graded_algebra.decompose_of_mem _ hx, direct_sum.of_eq_same, subtype.coe_mk]

lemma graded_algebra.decompose_of_mem_ne {x : A} {i j : ι} (hx : x ∈ 𝒜 i) (hij : i ≠ j):
  (graded_algebra.decompose 𝒜 x j : A) = 0 :=
by rw [graded_algebra.decompose_of_mem _ hx, direct_sum.of_eq_of_ne _ _ _ _ hij, submodule.coe_zero]


variable [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]

lemma graded_algebra.mem_support_iff (r : A) (i : ι) :
  i ∈ graded_algebra.support 𝒜 r ↔ graded_algebra.proj 𝒜 i r ≠ 0 :=
begin
  rw [graded_algebra.support, dfinsupp.mem_support_iff, graded_algebra.proj_apply],
  simp only [ne.def, submodule.coe_eq_zero],
end

lemma graded_algebra.sum_support_decompose (r : A) :
  ∑ i in graded_algebra.support 𝒜 r, (graded_algebra.decompose 𝒜 r i : A) = r :=
begin
  conv_rhs { rw [←(graded_algebra.decompose 𝒜).symm_apply_apply r,
    ←direct_sum.sum_support_of _ (graded_algebra.decompose 𝒜 r)] },
  rw [alg_equiv.map_sum, graded_algebra.support],
  simp_rw graded_algebra.decompose_symm_of,
end

end graded_algebra
