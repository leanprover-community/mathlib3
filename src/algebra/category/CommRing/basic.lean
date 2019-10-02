/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov
-/

import algebra.category.Mon.basic
import category_theory.fully_faithful
import algebra.ring
import data.int.basic

/-!
# Category instances for semiring, ring, comm_semiring, and comm_ring.

We introduce the bundled categories:
* `SemiRing`
* `Ring`
* `CommSemiRing`
* `CommRing`
along with the relevant forgetful functors between them.

## Implementation notes

We make SemiRing (and the other categories) locally reducible in order
to define its instances. This is because writing, for example,

  instance : concrete_category SemiRing := by { delta SemiRing, apply_instance }

results in an instance of the form `id (bundled_hom.concrete_category _)`
and this `id`, not being [reducible], prevents a later instance search
(once SemiRing is no longer reducible) from seeing that the morphisms of
SemiRing are really semiring morphisms (`→+*`), and therefore have a coercion
to functions, for example. It's especially important that the `has_coe_to_sort`
instance not contain an extra `id` as we want the `semiring ↥R` instance to
also apply to `semiring R.α` (it seems to be impractical to guarantee that
we always access `R.α` through the coercion rather than directly).

TODO: Probably @[derive] should be able to create instances of the
required form (without `id`), and then we could use that instead of
this obscure `local attribute [reducible]` method.

-/

universes u v

open category_theory

/-- The category of semirings. -/
def SemiRing : Type (u+1) := bundled semiring

namespace SemiRing

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [semiring R] : SemiRing := bundled.of R

local attribute [reducible] SemiRing

instance : has_coe_to_sort SemiRing := infer_instance

instance (R : SemiRing) : semiring R := R.str

instance bundled_hom : bundled_hom @ring_hom :=
⟨@ring_hom.to_fun, @ring_hom.id, @ring_hom.comp, @ring_hom.coe_inj⟩

instance : concrete_category SemiRing := infer_instance

instance has_forget_to_Mon : has_forget₂ SemiRing Mon :=
bundled_hom.mk_has_forget₂ @semiring.to_monoid (λ R₁ R₂ f, f.to_monoid_hom) (λ _ _ _, rfl)

end SemiRing

/-- The category of rings. -/
def Ring : Type (u+1) := induced_category SemiRing (bundled.map @ring.to_semiring)

namespace Ring

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [ring R] : Ring := bundled.of R

local attribute [reducible] Ring

instance : has_coe_to_sort Ring := infer_instance

instance (R : Ring) : ring R := R.str

instance : concrete_category Ring := infer_instance

instance has_forget_to_SemiRing : has_forget₂ Ring SemiRing := infer_instance

end Ring

/-- The category of commutative semirings. -/
def CommSemiRing : Type (u+1) := induced_category SemiRing (bundled.map comm_semiring.to_semiring)

namespace CommSemiRing

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_semiring R] : CommSemiRing := bundled.of R

local attribute [reducible] CommSemiRing

instance : has_coe_to_sort CommSemiRing := infer_instance

instance (R : CommSemiRing) : comm_semiring R := R.str

instance : concrete_category CommSemiRing := infer_instance

instance has_forget_to_SemiRing : has_forget₂ CommSemiRing SemiRing := infer_instance

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommMon : has_forget₂ CommSemiRing CommMon :=
has_forget₂.mk'
  (λ R : CommSemiRing, CommMon.of R) (λ R, rfl)
  (λ R₁ R₂ f, f.to_monoid_hom) (by tidy)

end CommSemiRing

/-- The category of commutative rings. -/
def CommRing : Type (u+1) := induced_category Ring (bundled.map comm_ring.to_ring)

namespace CommRing

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_ring R] : CommRing := bundled.of R

local attribute [reducible] CommRing

instance : has_coe_to_sort CommRing := infer_instance

instance (R : CommRing) : comm_ring R := R.str

instance : concrete_category CommRing := infer_instance

instance has_forget_to_Ring : has_forget₂ CommRing Ring := infer_instance

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommSemiRing : has_forget₂ CommRing CommSemiRing :=
has_forget₂.mk' (λ R : CommRing, CommSemiRing.of R) (λ R, rfl) (λ R₁ R₂ f, f) (by tidy)

end CommRing
