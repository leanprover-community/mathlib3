/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import algebra.direct_sum.internal

/-! # Typeclass for graded ring
For definition of an `R`-algebra `A` being graded by `𝒜 : ι → submodule R A`, see doc string of
`graded_algebra`.

- `graded_algebra.decompose : A → ⨁ i, 𝒜 i` and `graded_algebra.recompose : ⨁ i, 𝒜 i → A` are
the algebra isomorphism between `A` and `⨁ i, 𝒜 i` if `A` is graded by `𝒜`.
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
(decompose : A → ⨁ i, 𝒜 i)
(left_inv : function.left_inverse decompose (direct_sum.submodule_coe 𝒜))
(right_inv : function.right_inverse decompose (direct_sum.submodule_coe 𝒜))

lemma graded_ring.is_internal [graded_algebra 𝒜] :
  direct_sum.submodule_is_internal 𝒜 :=
⟨graded_algebra.left_inv.injective, graded_algebra.right_inv.surjective⟩

variable [graded_algebra 𝒜]

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then the direct sum of components
is isomorphic to it as an algebra. -/
def graded_algebra.recompose : (⨁ i, 𝒜 i) ≃ₐ[R] A :=
{ to_fun := direct_sum.submodule_coe_alg_hom 𝒜,
  inv_fun := graded_algebra.decompose,
  left_inv := graded_algebra.left_inv,
  right_inv := graded_algebra.right_inv,
  map_mul' := alg_hom.map_mul _,
  map_add' := alg_hom.map_add _,
  commutes' := alg_hom.commutes _ }

@[simp] lemma graded_algebra.decompose_def :
  graded_algebra.decompose = (graded_algebra.recompose 𝒜).symm := rfl

@[simp] lemma graded_algebra.recompose_of {i : ι} (x : 𝒜 i) :
  graded_algebra.recompose 𝒜 (direct_sum.of _ i x) = x :=
direct_sum.submodule_coe_alg_hom_of 𝒜 _ _

end graded_algebra
