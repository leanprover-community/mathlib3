/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov
-/

import algebra.category.Group
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

See the note [locally reducible category instances].

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
bundled_hom.mk_has_forget₂ @semiring.to_monoid (λ R₁ R₂, ring_hom.to_monoid_hom) (λ _ _ _, rfl)
instance has_forget_to_AddCommMon : has_forget₂ SemiRing AddCommMon :=
-- can't use bundled_hom.mk_has_forget₂, since AddCommMon is an induced category
{ forget₂ :=
  { obj := λ R, AddCommMon.of R,
    map := λ R₁ R₂ f, ring_hom.to_add_monoid_hom f } }

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
instance has_forget_to_AddCommGroup : has_forget₂ Ring AddCommGroup :=
-- can't use bundled_hom.mk_has_forget₂, since AddCommGroup is an induced category
{ forget₂ :=
  { obj := λ R, AddCommGroup.of R,
    map := λ R₁ R₂ f, ring_hom.to_add_monoid_hom f } }

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


namespace ring_equiv

variables {X Y : Type u}

section
variables [ring X] [ring Y]

/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
def to_Ring_iso (e : X ≃+* Y) : Ring.of X ≅ Ring.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

@[simp] lemma to_Ring_iso_hom {e : X ≃+* Y} : e.to_Ring_iso.hom = e.to_ring_hom := rfl
@[simp] lemma to_Ring_iso_inv {e : X ≃+* Y} : e.to_Ring_iso.inv = e.symm.to_ring_hom := rfl
end

section
variables [comm_ring X] [comm_ring Y]

/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
def to_CommRing_iso (e : X ≃+* Y) : CommRing.of X ≅ CommRing.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

@[simp] lemma to_CommRing_iso_hom {e : X ≃+* Y} : e.to_CommRing_iso.hom = e.to_ring_hom := rfl
@[simp] lemma to_CommRing_iso_inv {e : X ≃+* Y} : e.to_CommRing_iso.inv = e.symm.to_ring_hom := rfl
end

end ring_equiv

namespace category_theory.iso

/-- Build a `ring_equiv` from an isomorphism in the category `Ring`. -/
def Ring_iso_to_ring_equiv {X Y : Ring.{u}} (i : X ≅ Y) : X ≃+* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_mul'  := by tidy }.

/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def CommRing_iso_to_ring_equiv {X Y : CommRing.{u}} (i : X ≅ Y) : X ≃+* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_mul'  := by tidy }.

end category_theory.iso

/-- ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ring_equiv_iso_Ring_iso {X Y : Type u} [ring X] [ring Y] :
  (X ≃+* Y) ≅ (Ring.of X ≅ Ring.of Y) :=
{ hom := λ e, e.to_Ring_iso,
  inv := λ i, i.Ring_iso_to_ring_equiv, }

/-- ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms in `CommRing`. -/
def ring_equiv_iso_CommRing_iso {X Y : Type u} [comm_ring X] [comm_ring Y] :
  (X ≃+* Y) ≅ (CommRing.of X ≅ CommRing.of Y) :=
{ hom := λ e, e.to_CommRing_iso,
  inv := λ i, i.CommRing_iso_to_ring_equiv, }
