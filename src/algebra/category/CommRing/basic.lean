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

@[simp] lemma id_eq (R : Ring) : 𝟙 R = ring_hom.id R := rfl
@[simp] lemma comp_eq {R₁ R₂ R₃ : Ring} (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) :
  f ≫ g = g.comp f := rfl

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

namespace ring_equiv

variables {X Y : Type u}

section
variables [ring X] [ring Y]

def to_Ring_iso (e : X ≃r Y) : Ring.of X ≅ Ring.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

@[simp] lemma to_Ring_iso_hom {e : X ≃r Y} : e.to_Ring_iso.hom = e.to_ring_hom := rfl
@[simp] lemma to_Ring_iso_inv {e : X ≃r Y} : e.to_Ring_iso.inv = e.symm.to_ring_hom := rfl
end

section
variables [comm_ring X] [comm_ring Y]

def to_CommRing_iso (e : X ≃r Y) : CommRing.of X ≅ CommRing.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

@[simp] lemma to_CommRing_iso_hom {e : X ≃r Y} : e.to_CommRing_iso.hom = e.to_ring_hom := rfl
@[simp] lemma to_CommRing_iso_inv {e : X ≃r Y} : e.to_CommRing_iso.inv = e.symm.to_ring_hom := rfl
end

end ring_equiv

namespace category_theory.iso

def Ring_iso_to_ring_equiv {X Y : Ring.{u}} (i : X ≅ Y) : X ≃r Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  hom       := by apply_instance }.

def CommRing_iso_to_ring_equiv {X Y : CommRing.{u}} (i : X ≅ Y) : X ≃r Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  hom       := by apply_instance  }.

end category_theory.iso

/-- ring equivalences are the same as (isomorphic to) isomorphisms of rings -/
def ring_equiv_iso_Ring_iso {X Y : Type u} [ring X] [ring Y] :
  (X ≃r Y) ≅ (Ring.of X ≅ Ring.of Y) :=
{ hom := λ e, e.to_Ring_iso,
  inv := λ i, i.Ring_iso_to_ring_equiv, }

def ring_equiv_iso_CommRing_iso {X Y : Type u} [comm_ring X] [comm_ring Y] :
  (X ≃r Y) ≅ (CommRing.of X ≅ CommRing.of Y) :=
{ hom := λ e, e.to_CommRing_iso,
  inv := λ i, i.CommRing_iso_to_ring_equiv, }
