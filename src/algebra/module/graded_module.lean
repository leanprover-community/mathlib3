/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.graded_algebra.basic

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
class graded_module :=
(decompose' : M → ⨁ i, 𝓜 i)
(left_inv : function.left_inverse decompose' (direct_sum.coe_add_monoid_hom 𝓜))
(right_inv : function.right_inverse decompose' (direct_sum.coe_add_monoid_hom 𝓜))
(smul_mem : ∀ ⦃i j : ι⦄ {a : A} {m : M} (hi : a ∈ 𝓐 i) (hj : m ∈ 𝓜 j), a • m ∈ 𝓜 (i + j))

namespace graded_module

variables [graded_module 𝓐 𝓜]

protected lemma is_internal : direct_sum.is_internal 𝓜 :=
{ left := (@graded_module.left_inv ι R A _ _ _ _ _ 𝓐 _ M _ _ 𝓜 _).injective,
  right := (@graded_module.right_inv ι R A _ _ _ _ _ 𝓐 _ M _ _ 𝓜 _).surjective }

/--
If `M` is graded by `𝓜`, then `M` is isomorphic to `⨁ i, 𝓜 i` as `add_comm_monoid`.
-/
def decompose : M ≃+ ⨁ i, 𝓜 i := add_equiv.symm
{ to_fun := direct_sum.coe_add_monoid_hom 𝓜,
  inv_fun := graded_module.decompose' 𝓐,
  left_inv := graded_module.left_inv,
  right_inv := graded_module.right_inv,
  map_add' := λ x y, by rw map_add }

@[simp] lemma decompose_symm_of {i : ι} (x : 𝓜 i) :
  (graded_module.decompose 𝓐 𝓜).symm (direct_sum.of _ i x) = x :=
direct_sum.coe_add_monoid_hom_of _ _ _

instance self : graded_module 𝓐 (λ i, (𝓐 i).to_add_submonoid) :=
{ decompose' := graded_algebra.decompose 𝓐,
  left_inv := graded_algebra.left_inv,
  right_inv := graded_algebra.right_inv,
  smul_mem := λ i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

@[simp] lemma decompose_coe {i : ι} (x : 𝓜 i) :
  graded_module.decompose 𝓐 𝓜 x = direct_sum.of _ i x :=
by rw [← decompose_symm_of 𝓐 𝓜, add_equiv.apply_symm_apply]

lemma decompose_of_mem {x : M} {i : ι} (hx : x ∈ 𝓜 i) :
  graded_module.decompose 𝓐 𝓜 x = direct_sum.of _ i (⟨x, hx⟩ : 𝓜 i) :=
graded_module.decompose_coe _ _ ⟨x, hx⟩

lemma decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ 𝓜 i) (hij : i ≠ j):
  (graded_module.decompose 𝓐 𝓜 x j : M) = 0 :=
by rw [decompose_of_mem _ _ hx, direct_sum.of_eq_of_ne _ _ _ _ hij, add_submonoid.coe_zero]

/--
`⨁ i, 𝓜 i` is also an `A`-module, via `a • z = decompose (a • redecompose z)` where `decompose` and
`recompose` are the cannonical homomorphism `M → ⨁ i, 𝓜 i` and `⨁ i, 𝓜 i → M`.
-/
def is_module : module A (⨁ i, 𝓜 i) :=
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

end graded_module
