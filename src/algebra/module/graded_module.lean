/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.graded_algebra.basic
import algebra.direct_sum.decomposition

/-!
# Graded Module

Given a graded `R`-algebra `A` with grading `𝓐 : ι → submodule R A` and an `A`-module `M` with
decomposition `ι → addsubmonoid M`,
we define the typeclass `graded_module 𝓐 𝓜` for internally graded modules.

## Main definitions

* `graded_module 𝓐 𝓜`: an `A`-module `M` is graded by `𝓜` if and only if the decomposition map
`M → ⨁ i, 𝓜 i` is inverse to the canonical map `⨁ i, 𝓜 i → M`.
* `graded_module.decompose`: `M` and `⨁ i, 𝓜 i` are isomorphic as `add_comm_monoid`.
* `graded_module.is_module`: `⨁ i, 𝓜 i` is an `A`-module.

## Tags

graded module
-/


open_locale direct_sum big_operators

variables {ι R A : Type*}
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → submodule R A) [graded_algebra 𝓐]
variables {M : Type*} [add_comm_monoid M] [module A M]
variables (𝓜 : ι → add_submonoid M)

/--
Given a graded `R`-algebra `A` graded by `𝓐 : ι → submodule R A` and a decomposition of `A`-module
`M` into `𝓜 : ι → add_submonoid M`, we say that `M` is graded by `𝓜` if and only if the
decomposition map `M → ⨁ i, 𝓜 i` is inverse to the canonical map `⨁ i, 𝓜 i → M`.
-/
class graded_module extends direct_sum.decomposition 𝓜, set_like.has_graded_smul 𝓐 𝓜

namespace graded_module


protected lemma is_internal [graded_module 𝓐 𝓜] : direct_sum.is_internal 𝓜 :=
direct_sum.decomposition.is_internal _

/--
If `M` is graded by `𝓜`, then `M` is isomorphic to `⨁ i, 𝓜 i` as `add_comm_monoid`.
-/
def decompose [graded_module 𝓐 𝓜] : M ≃+ ⨁ i, 𝓜 i :=
direct_sum.decompose_add_equiv 𝓜

@[simp] lemma decompose_symm_of [graded_module 𝓐 𝓜] {i : ι} (x : 𝓜 i) :
  (graded_module.decompose 𝓐 𝓜).symm (direct_sum.of _ i x) = x :=
direct_sum.coe_add_monoid_hom_of _ _ _

instance self : graded_module 𝓐 (λ i, (𝓐 i).to_add_submonoid) :=
{ decompose' := direct_sum.decompose 𝓐,
  left_inv := direct_sum.decomposition.left_inv,
  right_inv := direct_sum.decomposition.right_inv,
  smul_mem := λ i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

/--
`⨁ i, 𝓜 i` is also an `A`-module, via `a • z = decompose (a • redecompose z)` where `decompose` and
`recompose` are the cannonical homomorphism `M → ⨁ i, 𝓜 i` and `⨁ i, 𝓜 i → M`.
-/
def is_module [graded_module 𝓐 𝓜] : module A (⨁ i, 𝓜 i) :=
{ smul := λ a z, graded_module.decompose 𝓐 𝓜 (a • (graded_module.decompose 𝓐 𝓜).symm z),
  one_smul := λ b, begin
    change graded_module.decompose 𝓐 𝓜 _ = _,
    rw [one_smul, add_equiv.apply_symm_apply],
  end,
  mul_smul := λ x y z, begin
    have m : ∀ x, x ∈ supr 𝓐,
    from λ x, (graded_algebra.is_internal 𝓐).submodule_supr_eq_top.symm ▸ submodule.mem_top,
    change graded_module.decompose _ _ _ = graded_module.decompose _ _ _,
    rw [mul_smul],
    refine submodule.supr_induction 𝓐 (m x) _ _ _,
    { intros j a hj,
    refine submodule.supr_induction 𝓐 (m y) _ _ _,
      { intros j' b hj',
        unfold has_scalar.smul,
        rw add_equiv.symm_apply_apply, },
      { unfold has_scalar.smul,
        simp only [zero_smul, map_zero, smul_zero], },
      { unfold has_scalar.smul,
        intros b c hb hc,
      simp only [smul_add, add_smul, hb, hc, map_add], }, },
    { simp only [smul_zero, zero_smul, map_zero], },
    { intros b c hb hc,
      simp only [add_smul, smul_add, hb, hc, map_add], }

  end,
  smul_add := λ x y z, begin
    change graded_module.decompose _ _ _ = _,
    simp only [smul_add, map_add],
  end,
  smul_zero := λ r, begin
    change graded_module.decompose _ _ _ = _,
    simp only [map_zero, smul_zero],
  end,
  add_smul := λ x y z, begin
    change graded_module.decompose _ _ _ = _,
    simp only [add_smul, map_add],
  end,
  zero_smul := λ a, begin
    change graded_module.decompose _ _ _ = _,
    simp only [map_zero, zero_smul],
  end }

local attribute [instance] is_module

/--
`M` and `⨁ᵢ 𝓜ᵢ` are linearly equivalent as `A`-module.
-/
def linear_equiv [graded_module 𝓐 𝓜] :
  M ≃ₗ[A] (⨁ i, 𝓜 i) :=
{ to_fun := decompose 𝓐 𝓜,
  map_add' := map_add _,
  map_smul' := λ a m, begin
    change _ = decompose 𝓐 𝓜 (a • _),
    rw [add_equiv.symm_apply_apply],
  end,
  inv_fun := (decompose 𝓐 𝓜).symm,
  left_inv := λ x, by rw [add_equiv.symm_apply_apply],
  right_inv := λ x, by rw [add_equiv.apply_symm_apply] }

end graded_module
