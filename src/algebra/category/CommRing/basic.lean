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
@[reducible] def Ring : Type (u+1) := bundled ring

namespace Ring

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [ring R] : Ring := bundled.of R

instance bundled_hom : bundled_hom _ :=
SemiRing.bundled_hom.induced_category @ring.to_semiring

instance (R : Ring) : ring R := R.str

instance has_forget_to_SemiRing : has_forget₂ Ring.{u} SemiRing.{u} :=
SemiRing.bundled_hom.induced_category_has_forget₂ _

end Ring

/-- The category of commutative semirings. -/
@[reducible] def CommSemiRing : Type (u+1) := bundled comm_semiring

namespace CommSemiRing

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_semiring R] : CommSemiRing := bundled.of R

instance bundled_hom : bundled_hom _ :=
SemiRing.bundled_hom.induced_category @comm_semiring.to_semiring

instance (R : CommSemiRing) : comm_semiring R := R.str

instance has_forget_to_SemiRing : has_forget₂ CommSemiRing.{u} SemiRing.{u} :=
bundled_hom.induced_category_has_forget₂ _ _

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommMon : has_forget₂ CommSemiRing.{u} CommMon.{u} :=
bundled_hom.mk_has_forget₂
  @comm_semiring.to_comm_monoid
  (λ R₁ R₂ f, f.to_monoid_hom)
  (by intros; refl)

end CommSemiRing

/-- The category of commutative rings. -/
@[reducible] def CommRing : Type (u+1) := bundled comm_ring

namespace CommRing

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_ring R] : CommRing := bundled.of R

instance bundled_hom : bundled_hom _ :=
Ring.bundled_hom.induced_category @comm_ring.to_ring

instance (R : CommRing) : comm_ring R := R.str

@[simp] lemma id_eq (R : CommRing) : 𝟙 R = ring_hom.id R := rfl
@[simp] lemma comp_eq {R₁ R₂ R₃ : CommRing} (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) :
  f ≫ g = g.comp f := rfl

@[simp] lemma forget_obj_eq_coe {R : CommRing} : (forget CommRing).obj R = R := rfl
@[simp] lemma forget_map_eq_coe {R₁ R₂ : CommRing} (f : R₁ ⟶ R₂) :
  (forget CommRing).map f = f :=
rfl

instance has_forget_to_Ring : has_forget₂ CommRing.{u} Ring.{u} :=
by apply bundled_hom.induced_category_has_forget₂

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommSemiRing : has_forget₂ CommRing.{u} CommSemiRing.{u} :=
bundled_hom.mk_has_forget₂
  @comm_ring.to_comm_semiring
  (λ _ _, id)
  (by intros; refl)

end CommRing
