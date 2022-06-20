/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.graded_algebra.basic
import algebra.direct_sum.decomposition

/-!
# Graded Module

Given an `R`-algebra `A` graded by `𝓐`, a graded `A`-module `M` is expressed as
`direct_sum.decomposition 𝓜` and `set_like.has_graded_scalar 𝓐 𝓜`.
Then `⨁ i, 𝓜 i` is an `A`-module and is isomorphic to `M`.

## Tags

graded module
-/


open_locale direct_sum big_operators

variables {ι R A M σ : Type*}
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → submodule R A)
variables [add_comm_monoid M] [module A M]
variables [set_like σ M] [add_submonoid_class σ M] (𝓜 : ι → σ)

namespace graded_module

instance graded_algebra.to_graded_module [graded_algebra 𝓐] :
  set_like.has_graded_scalar 𝓐 (λ i, (𝓐 i).to_add_submonoid) :=
{ smul_mem := λ i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

/--
`⨁ i, 𝓜 i` is also an `A`-module, via `a • z = decompose (a • redecompose z)` where `decompose` and
`recompose` are the cannonical homomorphism `M → ⨁ i, 𝓜 i` and `⨁ i, 𝓜 i → M`.
-/
def is_module [graded_algebra 𝓐] [@direct_sum.decomposition ι M σ _ _ _ _ 𝓜] :
  module A (⨁ i, 𝓜 i) :=
{ smul := λ a z, direct_sum.decompose_add_equiv 𝓜 (a • (direct_sum.decompose_add_equiv 𝓜).symm z),
  one_smul := λ b, begin
    change direct_sum.decompose_add_equiv 𝓜 _ = _,
    rw [one_smul, add_equiv.apply_symm_apply],
  end,
  mul_smul := λ x y z, begin
    have m : ∀ x, x ∈ supr 𝓐,
    from λ x, (graded_algebra.is_internal 𝓐).submodule_supr_eq_top.symm ▸ submodule.mem_top,
    change direct_sum.decompose_add_equiv 𝓜 _ = direct_sum.decompose_add_equiv 𝓜 _,
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
    change direct_sum.decompose_add_equiv 𝓜 _ = _,
    simp only [smul_add, map_add],
  end,
  smul_zero := λ r, begin
    change direct_sum.decompose_add_equiv 𝓜 _ = _,
    simp only [map_zero, smul_zero],
  end,
  add_smul := λ x y z, begin
    change direct_sum.decompose_add_equiv 𝓜 _ = _,
    simp only [add_smul, map_add],
  end,
  zero_smul := λ a, begin
    change direct_sum.decompose_add_equiv 𝓜 _ = _,
    simp only [map_zero, zero_smul],
  end }

local attribute [instance] is_module

/--
`M` and `⨁ᵢ 𝓜ᵢ` are linearly equivalent as `A`-module.
-/
def linear_equiv [graded_algebra 𝓐] [direct_sum.decomposition 𝓜] :
  M ≃ₗ[A] ⨁ i, 𝓜 i :=
{ to_fun := direct_sum.decompose_add_equiv 𝓜,
  map_add' := map_add _,
  map_smul' := λ a m, begin
    change _ = direct_sum.decompose_add_equiv 𝓜 (a • _),
    rw [add_equiv.symm_apply_apply],
  end,
  inv_fun := (direct_sum.decompose_add_equiv 𝓜).symm,
  left_inv := λ x, by rw [add_equiv.symm_apply_apply],
  right_inv := λ x, by rw [add_equiv.apply_symm_apply] }

end graded_module
