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
variables [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → submodule R A)
variables [add_comm_monoid M] [module A M]
variables [set_like σ M] [add_submonoid_class σ M] (𝓜 : ι → σ)

namespace graded_module

instance graded_algebra.to_graded_module [decidable_eq ι] [graded_algebra 𝓐] :
  set_like.has_graded_scalar 𝓐 (λ i, (𝓐 i).to_add_submonoid) :=
{ smul_mem := λ i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

lemma ghas_scalar.smul_zero
  [set_like.has_graded_scalar 𝓐 𝓜]
  {i j} (a : 𝓐 i) :
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j a 0 = 0 :=
subtype.ext_iff_val.2 $ (smul_zero _ : (a : A) • 0 = (0 : M))

lemma ghas_scalar.smul_add
  [set_like.has_graded_scalar 𝓐 𝓜]
  {i j} (a : 𝓐 i) (b c : 𝓜 j) :
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j a (b + c) =
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j a b +
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j a c :=
subtype.ext_iff_val.2 $ (smul_add _ _ _ : (a : A) • (b + c : M) = (a : A) • b + (a : A) • c)

lemma ghas_scalar.zero_smul
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  {i j} (b : 𝓜 j) :
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j 0 b = 0 :=
subtype.ext_iff_val.2 $ (zero_smul _ _ : (0 : A) • _ = 0)

lemma ghas_scalar.add_smul
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  {i j} (a b : 𝓐 i) (c : 𝓜 j) :
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j (a + b) c =
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j a c +
  @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j b c :=
subtype.ext_iff_val.2 $ (add_smul _ _ _ : (a + b : A) • _ = (a : A) • _ + (b : A) • _)

def gscalar_hom
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜] {i j} :
  𝓐 i →+ 𝓜 j →+ 𝓜 (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, @graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j a b,
    map_zero' := ghas_scalar.smul_zero 𝓐 𝓜 _,
    map_add' := ghas_scalar.smul_add _ _ _ },
  map_zero' := add_monoid_hom.ext $ ghas_scalar.zero_smul _ _,
  map_add' := λ x y, add_monoid_hom.ext $ ghas_scalar.add_smul _ _ _ _ }

def scalar_hom [decidable_eq ι]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜] :
  (⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i :=
direct_sum.to_add_monoid $ λ i,
  add_monoid_hom.flip $ direct_sum.to_add_monoid $ λ j, add_monoid_hom.flip $
    (direct_sum.of (λ i, 𝓜 i) _).comp_hom.comp $ gscalar_hom 𝓐 𝓜

lemma scalar_hom_of_of [decidable_eq ι]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  {i j} (a : 𝓐 i) (b : 𝓜 j) :
  scalar_hom 𝓐 𝓜 (direct_sum.of _ i a) (direct_sum.of _ j b) =
  direct_sum.of _ (i + j)
    (@graded_monoid.ghas_scalar.smul ι (λ i, 𝓐 i) (λ i, 𝓜 i) _ _ i j a b) :=
begin
  dunfold scalar_hom,
  rw [direct_sum.to_add_monoid_of, add_monoid_hom.flip_apply, direct_sum.to_add_monoid_of,
    add_monoid_hom.flip_apply, add_monoid_hom.comp_apply],
  refl,
end

def has_scalar [decidable_eq ι] [direct_sum.decomposition 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜] :
  has_scalar A (⨁ i, 𝓜 i) :=
{ smul := λ a b,
    (scalar_hom 𝓐 𝓜).comp (direct_sum.decompose_add_equiv 𝓐).to_add_monoid_hom a b }

local attribute [instance] graded_module.has_scalar

lemma one_smul [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  (b : ⨁ i, 𝓜 i) :
  (1 : A) • b = b :=
have of_congr : ∀ {i i' : ι} (h1 : i = i') {x : 𝓜 i} {y : 𝓜 i'} (h2 : x.1 = y.1),
  direct_sum.of _ i x = direct_sum.of _ i' y,
from λ _ _ h1 x y h2,
  direct_sum.of_congr _ h1 $ by subst h1; exact heq_of_eq (subtype.ext_iff_val.2 h2),
have eq0 : direct_sum.decompose_add_equiv 𝓐 (1 : A) = direct_sum.of _ 0 _ :=
  direct_sum.decompose_coe 𝓐 (⟨1, set_like.graded_monoid.one_mem⟩ : 𝓐 0),
suffices h : (scalar_hom 𝓐 𝓜).comp (direct_sum.decompose_add_equiv 𝓐).to_add_monoid_hom 1 b = b,
from h, direct_sum.induction_on b (by rw [map_zero]) (λ i b, begin
    rw [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom, eq0, scalar_hom_of_of],
    refine of_congr (zero_add _) _,
    change (1 : A) • b.1 = _,
    rw one_smul,
  end) $ λ x y hx hy, by rw [map_add, hx, hy]

lemma mul_smul [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  (a b : A) (c : ⨁ i, 𝓜 i) :
  (a * b) • c = a • (b • c) :=
have m : ∀ x, x ∈ supr 𝓐,
from λ x, (graded_algebra.is_internal 𝓐).submodule_supr_eq_top.symm ▸ submodule.mem_top,
have of_congr : ∀ {i i' : ι} (h1 : i = i') {x : 𝓜 i} {y : 𝓜 i'} (h2 : x.1 = y.1),
  direct_sum.of _ i x = direct_sum.of _ i' y,
from λ _ _ h1 x y h2,
  direct_sum.of_congr _ h1 $ by subst h1; exact heq_of_eq (subtype.ext_iff_val.2 h2),
begin
  unfold has_scalar.smul,
  induction c using direct_sum.induction_on with i c x y hx hy,
  { rw [map_zero, map_zero, map_zero] },
  { rw [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom],
    refine submodule.supr_induction 𝓐 (m a) _ _ _,
    { intros k a ha,
      refine submodule.supr_induction 𝓐 (m b) _ _ _,
      { intros j b hb,
        rw [show direct_sum.decompose_add_equiv 𝓐 (a * b) = _, from
          direct_sum.decompose_coe 𝓐 (⟨a * b, set_like.graded_monoid.mul_mem ha hb⟩ : 𝓐 (k + j)),
          scalar_hom_of_of, add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom,
          add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom,
          show direct_sum.decompose_add_equiv 𝓐 b = _, from direct_sum.decompose_coe 𝓐 ⟨b, hb⟩,
          scalar_hom_of_of,
          show direct_sum.decompose_add_equiv 𝓐 a = _, from direct_sum.decompose_coe 𝓐 ⟨a, ha⟩,
          scalar_hom_of_of],
        refine of_congr (add_assoc _ _ _) _,
        change ((a : A) * b) • (c : M) = (a : A) • ((b : A) • c),
        rw mul_smul, },
      { simp only [map_zero, mul_zero, add_monoid_hom.zero_apply], },
      { intros x y hx hy,
        simp only [mul_add, map_add, add_monoid_hom.add_apply, hx, hy], } },
    { simp only [map_zero, zero_mul, add_monoid_hom.zero_apply], },
    { intros x y hx hy,
      simp only [add_mul, map_add, add_monoid_hom.add_apply, hx, hy], }, },
  { simp only [map_add, hx, hy], },
end

lemma smul_add [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  (a : A) (b c : ⨁ i, 𝓜 i) :
  a • (b + c) = a • b + a • c :=
begin
  unfold has_scalar.smul,
  rw [map_add],
end

lemma smul_zero [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  (a : A) :
  a • (0 : ⨁ i, 𝓜 i) = 0 :=
begin
  unfold has_scalar.smul,
  rw [map_zero],
end

def distrib_mul_action [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜] :
  distrib_mul_action A (⨁ i, 𝓜 i) :=
{ smul := (•),
  one_smul := one_smul 𝓐 𝓜,
  mul_smul := mul_smul 𝓐 𝓜,
  smul_add := smul_add 𝓐 𝓜,
  smul_zero := smul_zero 𝓐 𝓜 }

local attribute [instance] graded_module.distrib_mul_action

lemma add_smul [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  (a b : A) (c : ⨁ i, 𝓜 i) :
  (a + b) • c = a • c + b • c :=
begin
  unfold has_scalar.smul,
  simp only [map_add, add_monoid_hom.add_apply],
end

lemma zero_smul [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  (a : ⨁ i, 𝓜 i) :
  (0 : A) • a = 0 :=
begin
  unfold has_scalar.smul,
  simp only [map_zero, add_monoid_hom.zero_apply],
end

def is_module [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜] :
  module A (⨁ i, 𝓜 i) :=
{ add_smul := add_smul 𝓐 𝓜,
  zero_smul := zero_smul 𝓐 𝓜,
  ..(distrib_mul_action 𝓐 𝓜)}

local attribute [instance] graded_module.is_module

def linear_equiv [decidable_eq ι] [graded_algebra 𝓐]
  [@set_like.has_graded_scalar ι _ A _ M _ _ _ _ 𝓐 𝓜]
  [direct_sum.decomposition 𝓜] :
  M ≃ₗ[A] ⨁ i, 𝓜 i :=
have m : ∀ x, x ∈ supr 𝓐,
from λ x, (graded_algebra.is_internal 𝓐).submodule_supr_eq_top.symm ▸ submodule.mem_top,
{ to_fun := direct_sum.decompose_add_equiv 𝓜,
  map_add' := λ x y, map_add _ _ _,
  map_smul' := λ x y, begin
    classical,
    rw [← direct_sum.sum_support_decompose 𝓐 x, map_sum, finset.sum_smul, map_sum,
      finset.sum_smul, finset.sum_congr rfl],
    intros i hi,
    rw [ring_hom.id_apply, ← direct_sum.sum_support_decompose 𝓜 y, map_sum, finset.smul_sum,
      map_sum, finset.smul_sum, finset.sum_congr rfl],
    intros j hj,
    unfold has_scalar.smul,
    rw [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom],
    simp only [direct_sum.decompose_add_equiv_apply, direct_sum.decompose_coe],
    rw [scalar_hom_of_of],
    convert direct_sum.decompose_coe 𝓜 _,
    refl,
  end,
  inv_fun := (direct_sum.decompose_add_equiv 𝓜).symm,
  left_inv := add_equiv.apply_symm_apply _,
  right_inv := add_equiv.symm_apply_apply _ }

end graded_module
