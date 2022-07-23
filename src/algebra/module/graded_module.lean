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
`direct_sum.decomposition 𝓜` and `set_like.has_graded_smul 𝓐 𝓜`.
Then `⨁ i, 𝓜 i` is an `A`-module and is isomorphic to `M`.

## Tags

graded module
-/


section

open_locale direct_sum

variables {ι : Type*} [add_monoid ι] [decidable_eq ι] (A : ι → Type*) (M : ι → Type*)
variables [Π (i : ι), add_comm_monoid (A i)] [Π i, add_comm_monoid $ M i]

class gmul_action [graded_monoid.gmonoid A] extends
  graded_monoid.ghas_smul A M :=
(one_smul (b : graded_monoid M) : (1 : graded_monoid A) • b = b)
(mul_smul (a a' : graded_monoid A) (b : graded_monoid M) : (a * a') • b = a • a' • b)

class gdistrib_mul_action [graded_monoid.gmonoid A] extends
  gmul_action A M :=
(smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c)
(smul_zero {i j} (a : A i) : smul a (0 : M j) = 0)

class gmodule [graded_monoid.gmonoid A] extends
  gdistrib_mul_action A M :=
(add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b)
(zero_smul {i j} (b : M j) : smul (0 : A i) b = 0)

def gmodule.smul_add_monoid_hom
  [graded_monoid.gmonoid A] [gmodule A M] :
  (⨁ i, A i) →+ (⨁ i, M i) →+ (⨁ i, M i) :=
direct_sum.to_add_monoid $ λ i,
{ to_fun := λ a, direct_sum.to_add_monoid $ λ j,
  { to_fun := λ b, direct_sum.of _ (i + j) (graded_monoid.ghas_smul.smul a b),
    map_zero' :=
    begin
      convert map_zero _,
      apply gdistrib_mul_action.smul_zero,
    end,
    map_add' := λ x y,
    begin
      convert map_add _ _ _,
      apply gdistrib_mul_action.smul_add,
    end },
  map_zero' := fun_like.ext _ _ $ λ x,
  begin
    rw [add_monoid_hom.zero_apply],
    induction x using direct_sum.induction_on with j y y₁ y₂ ih₁ ih₂,
    { convert map_zero _, },
    { simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk],
      convert map_zero _,
      apply gmodule.zero_smul, },
    { rw [map_add, ih₁, ih₂, zero_add], },
  end,
  map_add' := λ a₁ a₂, fun_like.ext _ _ $ λ y,
  begin
    induction y using direct_sum.induction_on with j y y₁ y₂ ih₁ ih₂,
    { rw [map_zero, map_zero] },
    { simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk, add_monoid_hom.add_apply],
      rw [←map_add],
      congr,
      apply gmodule.add_smul, },
    { simp only [map_add, ih₁, ih₂] },
  end }

section
variables [graded_monoid.gmonoid A] [gmodule A M]
instance : has_smul (⨁ i, A i) (⨁ i, M i) :=
{ smul := λ x y, gmodule.smul_add_monoid_hom A M x y }

@[simp] lemma gmodule.smul_def
  (x : ⨁ i, A i) (y : ⨁ i, M i) : x • y = gmodule.smul_add_monoid_hom _ _ x y := rfl
@[simp] lemma gmodule.smul_add_monoid_hom_apply_of_of {i j} (x : A i) (y : M j) :
  gmodule.smul_add_monoid_hom A M (direct_sum.of A i x) (direct_sum.of M j y) =
  direct_sum.of M (i + j) (graded_monoid.ghas_smul.smul x y) :=
by simp [gmodule.smul_add_monoid_hom]

@[simp] lemma gmodule.of_smul_of
  {i j} (x : A i) (y : M j) :
  direct_sum.of A i x • direct_sum.of M j y =
  direct_sum.of M (i + j) (graded_monoid.ghas_smul.smul x y) :=
by rw [gmodule.smul_def, gmodule.smul_add_monoid_hom, direct_sum.to_add_monoid_of,
    add_monoid_hom.coe_mk, direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk]
end

instance gmodule.module [direct_sum.gsemiring A] [gmodule A M] : module (⨁ i, A i) (⨁ i, M i) :=
{ smul := (•),
  one_smul :=
  begin
    intros b,
    induction b using direct_sum.induction_on with j b x₁ x₂ ih₁ ih₂,
    { simp, },
    { rw [show (1 : ⨁ i, A i) = direct_sum.of _ _ _, from rfl, gmodule.of_smul_of],
      apply direct_sum.of_eq_of_graded_monoid_eq,
      exact gmul_action.one_smul (⟨_, b⟩ : graded_monoid M) },
    { simp only [gmodule.smul_def] at ih₁ ih₂,
      simp only [gmodule.smul_def, map_add, ih₁, ih₂], },
  end,
  mul_smul := λ x y z,
  begin
    rw [gmodule.smul_def, gmodule.smul_def, gmodule.smul_def],
    induction x using direct_sum.induction_on with i x x₁ x₂ ihx₁ ihx₂,
    { rw [zero_mul, map_zero, add_monoid_hom.zero_apply, add_monoid_hom.zero_apply], },
    { induction y using direct_sum.induction_on with j y y₁ y₂ ihy₁ ihy₂,
      { rw [mul_zero, map_zero, add_monoid_hom.zero_apply, map_zero], },
      { simp only [direct_sum.of_mul_of, gmodule.smul_add_monoid_hom,
          direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk],
        induction z using direct_sum.induction_on with k z z₁ z₂ ihz₁ ihz₂,
        { rw [map_zero, map_zero, map_zero], },
        { simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk],
          apply direct_sum.of_eq_of_graded_monoid_eq,
          exact gmul_action.mul_smul ⟨_, x⟩ ⟨_, y⟩ ⟨_, z⟩, },
        { simp only [map_add, ihz₁, ihz₂], }, },
      { simp only [map_add, ←ihy₁, ←ihy₂, add_monoid_hom.add_apply],
        simp_rw [mul_add, map_add],
        simp only [add_monoid_hom.add_apply], }, },
    { simp only [add_mul, map_add, ihx₁, ihx₂, add_monoid_hom.add_apply], },
  end,
  smul_add := λ r x y,
  begin
    induction r using direct_sum.induction_on with i r r₁ r₂ ihr₁ ihr₂,
    { simp only [gmodule.smul_def, map_zero, add_monoid_hom.zero_apply, add_zero], },
    { simp only [gmodule.smul_def, map_add] },
    { simp only [gmodule.smul_def] at ihr₁ ihr₂ ⊢,
      simp only [map_add, ihr₁, ihr₂], },
  end,
  smul_zero := λ r, by simp only [gmodule.smul_def, map_zero],
  add_smul := λ r s x, by simp only [gmodule.smul_def, map_add, add_monoid_hom.add_apply],
  zero_smul := λ x, by simp only [gmodule.smul_def, map_zero, add_monoid_hom.zero_apply] }

end

open_locale direct_sum big_operators

variables {ι R A M σ σ' : Type*}
variables [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → σ') [set_like σ' A]
variables (𝓜 : ι → σ)

namespace graded_module

include σ' A σ M

variables [add_comm_monoid M] [module A M] [set_like σ M] [add_submonoid_class σ' A]
  [add_submonoid_class σ M] [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜]

instance gmodule [decidable_eq ι] : gmodule (λ i, 𝓐 i) (λ i, 𝓜 i) :=
{ smul := λ i j x y, ⟨(x : A) • (y : M), set_like.has_graded_smul.smul_mem x.2 y.2⟩,
  one_smul := λ ⟨i, m⟩,
  begin
    ext,
    { exact zero_add _, },
    { simp only [←subtype.val_eq_coe],
      change (1 : A) • (m : M) = m,
      rw one_smul, },
  end,
  mul_smul := λ ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩,
  begin
    ext,
    { exact add_assoc _ _ _, },
    { simp only [←subtype.val_eq_coe],
      change (a * a' : A) • ↑b = ↑a • ↑a' • ↑b,
      rw mul_smul },
  end,
  smul_add := λ i j a b c,
  begin
    ext,
    change (a : A) • (b + c : M) = ↑a • ↑b + ↑a • ↑c,
    rw smul_add,
  end,
  smul_zero := λ i j a,
  begin
    ext,
    change (a : A) • (0 : M) = 0,
    exact smul_zero _,
  end,
  add_smul := λ i j a a' b,
  begin
    ext,
    change (↑a + ↑a') • (b : M) = ↑a • b + ↑a' • b,
    rw add_smul,
  end,
  zero_smul := λ i j b,
  begin
    ext,
    change (0 : A) • (b : M) = 0,
    rw zero_smul,
  end }

/--
Since `A ≃+ ⨁ i, 𝓐 i`, the map `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i` defines a smul
multiplication of `A` on `⨁ i, 𝓜 i`
-/
def has_smul [decidable_eq ι]
  [direct_sum.decomposition 𝓐] [set_like.has_graded_smul 𝓐 𝓜] :
  has_smul A (⨁ i, 𝓜 i) :=
{ smul := λ a b, (gmodule.smul_add_monoid_hom (λ i, 𝓐 i) (λ j, 𝓜 j)).comp
    (direct_sum.decompose_add_equiv 𝓐).to_add_monoid_hom a b }

local attribute [instance] graded_module.has_smul

lemma one_smul [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  (b : ⨁ i, 𝓜 i) :
  (1 : A) • b = b :=
begin
  unfold has_smul.smul,
  refine direct_sum.induction_on b (by rw [map_zero]) _ (λ x y hx hy, by rw [map_add, hx, hy]),
  intros i b,
  rw [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom,
    show direct_sum.decompose_add_equiv 𝓐 (1 : A) = direct_sum.of _ 0 _, from
    direct_sum.decompose_coe 𝓐 (⟨1, set_like.graded_monoid.one_mem⟩ : 𝓐 0),
    gmodule.smul_add_monoid_hom_apply_of_of],
  apply direct_sum.of_eq_of_graded_monoid_eq,
  ext,
  { exact zero_add i, },
  { convert (one_smul _ _ : (1 : A) • b.1 = b.1) },
end

lemma mul_smul [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  (a b : A) (c : ⨁ i, 𝓜 i) :
  (a * b) • c = a • (b • c) :=
begin
  let 𝓐' : ι → add_submonoid A :=
      λ i, (⟨𝓐 i, λ _ _, add_mem_class.add_mem, zero_mem_class.zero_mem _⟩ : add_submonoid A),
  letI : graded_ring 𝓐' :=
    { decompose' := (direct_sum.decompose 𝓐 : A → ⨁ i, 𝓐 i),
      left_inv := direct_sum.decomposition.left_inv,
      right_inv := direct_sum.decomposition.right_inv,
      ..(by apply_instance : set_like.graded_monoid 𝓐), },
  have m : ∀ x, x ∈ supr 𝓐',
  { intro x,
    rw direct_sum.is_internal.add_submonoid_supr_eq_top 𝓐'
      (direct_sum.decomposition.is_internal 𝓐'),
    trivial, },
  unfold has_smul.smul,
  induction c using direct_sum.induction_on with i c x y hx hy,
  { rw [map_zero, map_zero, map_zero] },
  { rw [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom],
    refine add_submonoid.supr_induction 𝓐' (m a) _ _ _,
    { intros k a ha,
      refine add_submonoid.supr_induction 𝓐' (m b) _ _ _,
      { intros j b hb,
        rw [show direct_sum.decompose_add_equiv 𝓐 (a * b) = _, from
          direct_sum.decompose_coe 𝓐 (⟨a * b, set_like.graded_monoid.mul_mem ha hb⟩ : 𝓐 (k + j)),
          gmodule.smul_add_monoid_hom_apply_of_of, add_monoid_hom.comp_apply,
          add_equiv.coe_to_add_monoid_hom, add_monoid_hom.comp_apply,
          add_equiv.coe_to_add_monoid_hom,
          show direct_sum.decompose_add_equiv 𝓐 b = _, from direct_sum.decompose_coe 𝓐 ⟨b, hb⟩,
          gmodule.smul_add_monoid_hom_apply_of_of,
          show direct_sum.decompose_add_equiv 𝓐 a = _, from direct_sum.decompose_coe 𝓐 ⟨a, ha⟩,
          gmodule.smul_add_monoid_hom_apply_of_of],
        apply direct_sum.of_eq_of_graded_monoid_eq,
        ext,
        { exact add_assoc _ _ _ },
        { change ((a : A) * b) • (c : M) = (a : A) • ((b : A) • c),
          rw mul_smul, } },
      { simp only [map_zero, mul_zero, add_monoid_hom.zero_apply], },
      { intros x y hx hy,
        simp only [mul_add, map_add, add_monoid_hom.add_apply, hx, hy], } },
    { simp only [map_zero, zero_mul, add_monoid_hom.zero_apply], },
    { intros x y hx hy,
      simp only [add_mul, map_add, add_monoid_hom.add_apply, hx, hy], }, },
  { simp only [map_add, hx, hy], },
end

lemma smul_add [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  (a : A) (b c : ⨁ i, 𝓜 i) :
  a • (b + c) = a • b + a • c :=
by unfold has_smul.smul; simp

lemma smul_zero [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  (a : A) :
  a • (0 : ⨁ i, 𝓜 i) = 0 :=
by unfold has_smul.smul; simp

/--
The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i` is
distributive.
-/
def distrib_mul_action [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜] :
  distrib_mul_action A (⨁ i, 𝓜 i) :=
{ smul := (•),
  one_smul := one_smul 𝓐 𝓜,
  mul_smul := mul_smul 𝓐 𝓜,
  smul_add := smul_add 𝓐 𝓜,
  smul_zero := smul_zero 𝓐 𝓜 }

local attribute [instance] graded_module.distrib_mul_action

lemma add_smul [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  (a b : A) (c : ⨁ i, 𝓜 i) :
  (a + b) • c = a • c + b • c :=
by unfold has_smul.smul; simp

lemma zero_smul [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  (a : ⨁ i, 𝓜 i) :
  (0 : A) • a = 0 :=
by unfold has_smul.smul; simp

/--
The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i`
turns `⨁ i, 𝓜 i` into an `A`-module
-/
def is_module [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜] :
  module A (⨁ i, 𝓜 i) :=
{ add_smul := add_smul 𝓐 𝓜,
  zero_smul := zero_smul 𝓐 𝓜,
  ..(distrib_mul_action 𝓐 𝓜)}

local attribute [instance] graded_module.is_module

/--
`⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
-/
def linear_equiv [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  [direct_sum.decomposition 𝓜] :
  M ≃ₗ[A] ⨁ i, 𝓜 i :=
{ to_fun := direct_sum.decompose_add_equiv 𝓜,
  map_add' := λ x y, map_add _ _ _,
  map_smul' := λ x y, begin
    classical,
    rw [← direct_sum.sum_support_decompose 𝓐 x, map_sum, finset.sum_smul, map_sum,
      finset.sum_smul, finset.sum_congr rfl (λ i hi, _)],
    rw [ring_hom.id_apply, ← direct_sum.sum_support_decompose 𝓜 y, map_sum, finset.smul_sum,
      map_sum, finset.smul_sum, finset.sum_congr rfl (λ j hj, _)],
    unfold has_smul.smul,
    rw [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom],
    simp only [direct_sum.decompose_add_equiv_apply, direct_sum.decompose_coe,
      gmodule.smul_add_monoid_hom_apply_of_of],
    convert direct_sum.decompose_coe 𝓜 _,
    refl,
  end,
  inv_fun := (direct_sum.decompose_add_equiv 𝓜).symm,
  left_inv := add_equiv.apply_symm_apply _,
  right_inv := add_equiv.symm_apply_apply _ }

end graded_module
