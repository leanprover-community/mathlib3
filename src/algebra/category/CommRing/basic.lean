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
-/

universes u v

open category_theory

/-- The category of semirings. -/
@[reducible] def SemiRing : Type (u+1) := bundled semiring

namespace SemiRing

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [semiring R] : SemiRing := bundled.of R

instance bundled_hom : bundled_hom @ring_hom :=
⟨@ring_hom.to_fun, @ring_hom.id, @ring_hom.comp, @ring_hom.ext⟩

instance (R : SemiRing) : semiring R := R.str

instance has_forget_to_Mon : has_forget₂ SemiRing.{u} Mon.{u} :=
bundled_hom.mk_has_forget₂ @semiring.to_monoid (λ R₁ R₂ f, f.to_monoid_hom) (λ _ _ _, rfl)

end SemiRing

/-- The category of rings. -/
@[reducible] def Ring : Type (u+1) := induced_category SemiRing (bundled.map @ring.to_semiring.{u})

namespace Ring

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [ring R] : Ring := bundled.of R

instance (R : Ring) : ring R := R.str

-- These examples verify that we have successfully provided the expected instances.
example : concrete_category Ring.{u} := infer_instance
example : has_forget₂ Ring.{u} SemiRing.{u} := infer_instance

end Ring

/-- The category of commutative semirings. -/
@[reducible] def CommSemiRing : Type (u+1) := induced_category SemiRing (bundled.map comm_semiring.to_semiring.{u})

namespace CommSemiRing

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_semiring R] : CommSemiRing := bundled.of R

instance (R : CommSemiRing) : comm_semiring R := R.str

-- These examples verify that we have successfully provided the expected instances.
example : concrete_category CommSemiRing.{u} := infer_instance
example : has_forget₂ CommSemiRing.{u} SemiRing.{u} := infer_instance

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommMon : has_forget₂ CommSemiRing.{u} CommMon.{u} :=
has_forget₂.mk'
  (λ R : CommSemiRing.{u}, CommMon.of R) (λ R, rfl)
  (λ R₁ R₂ f, f.to_monoid_hom) (by tidy)

end CommSemiRing

/-- The category of commutative rings. -/
-- TODO experiment with making @[reducible] local
@[reducible] def CommRing : Type (u+1) := induced_category Ring (bundled.map comm_ring.to_ring.{u})

namespace CommRing

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_ring R] : CommRing := bundled.of R

instance (R : CommRing) : comm_ring R := R.str

-- These examples verify that we have successfully provided the expected instances.
example : concrete_category CommRing.{u} := infer_instance
example : has_forget₂ CommRing.{u} Ring.{u} := infer_instance

/-- The forgetful functor from commutative rings to commutative semirings. -/
instance has_forget_to_CommSemiRing : has_forget₂ CommRing.{u} CommSemiRing.{u} :=
has_forget₂.mk' (λ R : CommRing.{u}, CommSemiRing.of R) (λ R, rfl) (λ R₁ R₂ f, f) (by tidy)

end CommRing
