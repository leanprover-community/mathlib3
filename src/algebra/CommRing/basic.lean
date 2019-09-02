/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.
-/

import algebra.Mon.basic
import category_theory.fully_faithful
import algebra.ring
import data.int.basic

universes u v

open category_theory

/-- The category of semirings. -/
@[reducible] def SemiRing : Type (u+1) := bundled semiring

namespace SemiRing

def of (R : Type u) [semiring R] : SemiRing := bundled.of R

instance (R : SemiRing) : semiring R := R.str

instance bundled_category : bundled_category @ring_hom :=
⟨@ring_hom.to_fun, @ring_hom.ext, @ring_hom.id, by intros; refl,
 @ring_hom.comp, by intros; refl⟩

instance has_forget_to_Mon : has_forget SemiRing.{u} Mon.{u} :=
bundled_has_forget @semiring.to_monoid (λ R₁ R₂ f, f.to_monoid_hom) (by intros; refl)

end SemiRing

/-- The category of rings. -/
@[reducible] def Ring : Type (u+1) := bundled ring

namespace Ring

instance (x : Ring) : ring x := x.str

def of (R : Type u) [ring R] : Ring := bundled.of R

instance bundled_category : bundled_category _ :=
SemiRing.bundled_category.restrict_str @ring.to_semiring

instance has_forget_to_SemiRing : has_forget Ring.{u} SemiRing.{u} :=
by apply bundled_category.restrict_str_has_forget

end Ring

/-- The category of commutative semirings. -/
@[reducible] def CommSemiRing : Type (u+1) := bundled comm_semiring

namespace CommSemiRing

instance (x : CommSemiRing) : comm_semiring x := x.str

def of (R : Type u) [comm_semiring R] : CommSemiRing := bundled.of R

instance bundled_category : bundled_category _ :=
SemiRing.bundled_category.restrict_str @comm_semiring.to_semiring

instance has_forget_to_SemiRing : has_forget CommSemiRing.{u} SemiRing.{u} :=
by apply bundled_category.restrict_str_has_forget

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommMon : has_forget CommSemiRing.{u} CommMon.{u} :=
bundled_has_forget
  @comm_semiring.to_comm_monoid
  (λ R₁ R₂ f, f.to_monoid_hom)
  (by intros; refl)

end CommSemiRing

/-- The category of commutative rings. -/
@[reducible] def CommRing : Type (u+1) := bundled comm_ring

namespace CommRing

instance (x : CommRing) : comm_ring x := x.str

def of (R : Type u) [comm_ring R] : CommRing := bundled.of R

instance bundled_category : bundled_category _ :=
Ring.bundled_category.restrict_str @comm_ring.to_ring

@[simp] lemma id_eq (R : CommRing) : 𝟙 R = ring_hom.id R := rfl
@[simp] lemma comp_eq {R₁ R₂ R₃ : CommRing} (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) :
  f ≫ g = g.comp f := rfl


@[simp] lemma forget_obj_eq_coe {R : CommRing} : (forget CommRing).obj R = R := rfl
@[simp] lemma forget_map_eq_coe {R₁ R₂ : CommRing} (f : R₁ ⟶ R₂) :
  (forget CommRing).map f = f :=
rfl

instance has_forget_to_Ring : has_forget CommRing.{u} Ring.{u} :=
by apply bundled_category.restrict_str_has_forget

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommSemiRing : has_forget CommRing.{u} CommSemiRing.{u} :=
bundled_has_forget
  @comm_ring.to_comm_semiring
  (λ _ _, id)
  (by intros; refl)

end CommRing
