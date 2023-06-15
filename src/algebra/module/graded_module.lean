/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.graded_algebra.basic
import algebra.graded_mul_action
import algebra.direct_sum.decomposition
import algebra.module.big_operators

/-!
# Graded Module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given an `R`-algebra `A` graded by `𝓐`, a graded `A`-module `M` is expressed as
`direct_sum.decomposition 𝓜` and `set_like.has_graded_smul 𝓐 𝓜`.
Then `⨁ i, 𝓜 i` is an `A`-module and is isomorphic to `M`.

## Tags

graded module
-/


section

open_locale direct_sum

variables {ι : Type*} (A : ι → Type*) (M : ι → Type*)

namespace direct_sum
open graded_monoid

/-- A graded version of `distrib_mul_action`. -/
class gdistrib_mul_action [add_monoid ι] [gmonoid A] [Π i, add_monoid (M i)]
  extends gmul_action A M :=
(smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c)
(smul_zero {i j} (a : A i) : smul a (0 : M j) = 0)

/-- A graded version of `module`. -/
class gmodule [add_monoid ι] [Π i, add_monoid (A i)] [Π i, add_monoid (M i)]
  [gmonoid A] extends gdistrib_mul_action A M :=
(add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b)
(zero_smul {i j} (b : M j) : smul (0 : A i) b = 0)

/-- A graded version of `semiring.to_module`. -/
instance gsemiring.to_gmodule [decidable_eq ι] [add_monoid ι]
  [Π (i : ι), add_comm_monoid (A i)] [gsemiring A] :
  gmodule A A :=
{ smul_add := λ _ _, gsemiring.mul_add,
  smul_zero := λ i j, gsemiring.mul_zero,
  add_smul := λ i j, gsemiring.add_mul,
  zero_smul := λ i j, gsemiring.zero_mul,
  ..gmonoid.to_gmul_action A }

variables [add_monoid ι] [Π (i : ι), add_comm_monoid (A i)] [Π i, add_comm_monoid (M i)]

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps] def gsmul_hom [gmonoid A] [gmodule A M] {i j} :
  A i →+ M j →+ M (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, ghas_smul.smul a b,
    map_zero' := gdistrib_mul_action.smul_zero _,
    map_add' := gdistrib_mul_action.smul_add _ },
  map_zero' := add_monoid_hom.ext $ λ a, gmodule.zero_smul a,
  map_add' := λ a₁ a₂, add_monoid_hom.ext $ λ b, gmodule.add_smul _ _ _}

namespace gmodule

/-- For graded monoid `A` and a graded module `M` over `A`. `gmodule.smul_add_monoid_hom` is the
`⨁ᵢ Aᵢ`-scalar multiplication on `⨁ᵢ Mᵢ` induced by `gsmul_hom`. -/
def smul_add_monoid_hom
  [decidable_eq ι] [gmonoid A] [gmodule A M] :
  (⨁ i, A i) →+ (⨁ i, M i) →+ (⨁ i, M i) :=
to_add_monoid $ λ i, add_monoid_hom.flip $
  to_add_monoid $ λ j, add_monoid_hom.flip $
    (of M _).comp_hom.comp $ gsmul_hom A M

section

open graded_monoid direct_sum gmodule

instance [decidable_eq ι] [gmonoid A] [gmodule A M] :
  has_smul (⨁ i, A i) (⨁ i, M i) :=
{ smul := λ x y, smul_add_monoid_hom A M x y }

@[simp] lemma smul_def [decidable_eq ι] [gmonoid A] [gmodule A M]
  (x : ⨁ i, A i) (y : ⨁ i, M i) : x • y = smul_add_monoid_hom _ _ x y := rfl

@[simp] lemma smul_add_monoid_hom_apply_of_of [decidable_eq ι] [gmonoid A] [gmodule A M]
  {i j} (x : A i) (y : M j) :
  smul_add_monoid_hom A M (direct_sum.of A i x) (of M j y) =
  of M (i + j) (ghas_smul.smul x y) :=
by simp [smul_add_monoid_hom]

@[simp] lemma of_smul_of [decidable_eq ι] [gmonoid A] [gmodule A M]
  {i j} (x : A i) (y : M j) :
  direct_sum.of A i x • of M j y = of M (i + j) (ghas_smul.smul x y) :=
smul_add_monoid_hom_apply_of_of _ _ _ _

open add_monoid_hom

-- Almost identical to the proof of `direct_sum.one_mul`
private lemma one_smul [decidable_eq ι] [gmonoid A] [gmodule A M] (x : ⨁ i, M i) :
  (1 : ⨁ i, A i) • x = x :=
suffices smul_add_monoid_hom A M 1 = add_monoid_hom.id (⨁ i, M i),
  from add_monoid_hom.congr_fun this x,
begin
  apply direct_sum.add_hom_ext, intros i xi,
  unfold has_one.one,
  rw smul_add_monoid_hom_apply_of_of,
  exact direct_sum.of_eq_of_graded_monoid_eq (one_smul (graded_monoid A) $ graded_monoid.mk i xi),
end

-- Almost identical to the proof of `direct_sum.mul_assoc`
private lemma mul_smul [decidable_eq ι] [gsemiring A] [gmodule A M]
  (a b : ⨁ i, A i) (c : ⨁ i, M i) : (a * b) • c = a • (b • c) :=
suffices (smul_add_monoid_hom A M).comp_hom.comp (direct_sum.mul_hom A)
      -- `λ a b c, (a * b) • c` as a bundled hom
      = (add_monoid_hom.comp_hom add_monoid_hom.flip_hom $
          (smul_add_monoid_hom A M).flip.comp_hom.comp $ smul_add_monoid_hom A M).flip,
      -- `λ a b c, a • (b • c)` as a bundled hom
  from add_monoid_hom.congr_fun (add_monoid_hom.congr_fun (add_monoid_hom.congr_fun this a) b) c,
begin
  ext ai ax bi bx ci cx : 6,
  dsimp only [coe_comp, function.comp_app, comp_hom_apply_apply, flip_apply, flip_hom_apply],
  rw [smul_add_monoid_hom_apply_of_of, smul_add_monoid_hom_apply_of_of,
    direct_sum.mul_hom_of_of, smul_add_monoid_hom_apply_of_of],
  exact direct_sum.of_eq_of_graded_monoid_eq
    (mul_smul (graded_monoid.mk ai ax) (graded_monoid.mk bi bx) (graded_monoid.mk ci cx)),
end

/-- The `module` derived from `gmodule A M`. -/
instance module [decidable_eq ι] [gsemiring A] [gmodule A M] :
  module (⨁ i, A i) (⨁ i, M i) :=
{ smul := (•),
  one_smul := one_smul _ _,
  mul_smul := mul_smul _ _,
  smul_add := λ r, (smul_add_monoid_hom A M r).map_add,
  smul_zero := λ r, (smul_add_monoid_hom A M r).map_zero,
  add_smul := λ r s x, by simp only [smul_def, map_add, add_monoid_hom.add_apply],
  zero_smul := λ x, by simp only [smul_def, map_zero, add_monoid_hom.zero_apply] }

end

end gmodule

end direct_sum

end

open_locale direct_sum big_operators

variables {ι R A M σ σ' : Type*}
variables [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → σ') [set_like σ' A]
variables (𝓜 : ι → σ)

namespace set_like

include σ' A σ M

instance gmul_action [add_monoid M] [distrib_mul_action A M]
  [set_like σ M] [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜] :
  graded_monoid.gmul_action (λ i, 𝓐 i) (λ i, 𝓜 i) :=
{ one_smul := λ ⟨i, m⟩, sigma.subtype_ext (zero_add _) (one_smul _ _),
  mul_smul := λ ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩, sigma.subtype_ext (add_assoc _ _ _) (mul_smul _ _ _),
  ..set_like.ghas_smul 𝓐 𝓜 }

instance gdistrib_mul_action [add_monoid M] [distrib_mul_action A M]
  [set_like σ M] [add_submonoid_class σ M] [set_like.graded_monoid 𝓐]
  [set_like.has_graded_smul 𝓐 𝓜] :
  direct_sum.gdistrib_mul_action (λ i, 𝓐 i) (λ i, 𝓜 i) :=
{ smul_add := λ i j a b c, subtype.ext $ smul_add _ _ _,
  smul_zero := λ i j a, subtype.ext $ smul_zero _,
  ..set_like.gmul_action 𝓐 𝓜 }

variables [add_comm_monoid M] [module A M] [set_like σ M] [add_submonoid_class σ' A]
  [add_submonoid_class σ M] [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜]

/-- `[set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜]` is the internal version of graded
  module, the internal version can be translated into the external version `gmodule`. -/
instance gmodule : direct_sum.gmodule (λ i, 𝓐 i) (λ i, 𝓜 i) :=
{ smul := λ i j x y, ⟨(x : A) • (y : M), set_like.has_graded_smul.smul_mem x.2 y.2⟩,
  add_smul := λ i j a a' b, subtype.ext $ add_smul _ _ _,
  zero_smul := λ i j b, subtype.ext $ zero_smul _ _,
  ..set_like.gdistrib_mul_action 𝓐 𝓜}

end set_like

namespace graded_module

include σ' A σ M

variables [add_comm_monoid M] [module A M] [set_like σ M] [add_submonoid_class σ' A]
  [add_submonoid_class σ M] [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜]

/--
The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i`
turns `⨁ i, 𝓜 i` into an `A`-module
-/
def is_module [decidable_eq ι] [graded_ring 𝓐] :
  module A (⨁ i, 𝓜 i) :=
{ smul := λ a b, direct_sum.decompose 𝓐 a • b,
  .. module.comp_hom _ (direct_sum.decompose_ring_equiv 𝓐 : A ≃+* ⨁ i, 𝓐 i).to_ring_hom }

local attribute [instance] graded_module.is_module

/--
`⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
"The internal version" and "the external version" are isomorphism as `A`-modules.
-/
def linear_equiv [decidable_eq ι] [graded_ring 𝓐]
  [direct_sum.decomposition 𝓜] :
  M ≃ₗ[A] ⨁ i, 𝓜 i :=
{ to_fun := direct_sum.decompose_add_equiv 𝓜,
  map_smul' := λ x y, begin
    classical,
    rw [← direct_sum.sum_support_decompose 𝓐 x, map_sum, finset.sum_smul, map_sum,
      finset.sum_smul, finset.sum_congr rfl (λ i hi, _)],
    rw [ring_hom.id_apply, ← direct_sum.sum_support_decompose 𝓜 y, map_sum, finset.smul_sum,
      map_sum, finset.smul_sum, finset.sum_congr rfl (λ j hj, _)],
    simp only [(•), direct_sum.decompose_add_equiv_apply, direct_sum.decompose_coe,
      direct_sum.gmodule.smul_add_monoid_hom_apply_of_of],
    convert direct_sum.decompose_coe 𝓜 _,
    refl,
  end,
  .. direct_sum.decompose_add_equiv 𝓜 }

end graded_module
