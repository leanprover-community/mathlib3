/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov
-/
import algebra.category.Group.basic
import category_theory.concrete_category.reflects_isomorphisms
import algebra.ring.equiv

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
def SemiRing : Type (u+1) := bundled semiring

namespace SemiRing

/-- `ring_hom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. We use the same trick in `category_theory.Mon.assoc_monoid_hom`. -/
abbreviation assoc_ring_hom (M N : Type*) [semiring M] [semiring N] := ring_hom M N

instance bundled_hom : bundled_hom assoc_ring_hom :=
⟨λ M N [semiring M] [semiring N], by exactI @ring_hom.to_fun M N _ _,
 λ M [semiring M], by exactI @ring_hom.id M _,
 λ M N P [semiring M] [semiring N] [semiring P], by exactI @ring_hom.comp M N P _ _ _,
 λ M N [semiring M] [semiring N], by exactI @ring_hom.coe_inj M N _ _⟩

attribute [derive [large_category, concrete_category]] SemiRing

instance : has_coe_to_sort SemiRing Type* := bundled.has_coe_to_sort

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [semiring R] : SemiRing := bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `SemiRing`. -/
def of_hom {R S : Type u} [semiring R] [semiring S] (f : R →+* S) : of R ⟶ of S := f

@[simp] lemma of_hom_apply {R S : Type u} [semiring R] [semiring S] (f : R →+* S) (x : R) :
  of_hom f x = f x := rfl

instance : inhabited SemiRing := ⟨of punit⟩

instance (R : SemiRing) : semiring R := R.str

@[simp] lemma coe_of (R : Type u) [semiring R] : (SemiRing.of R : Type u) = R := rfl

instance has_forget_to_Mon : has_forget₂ SemiRing Mon :=
bundled_hom.mk_has_forget₂
  (λ R hR, @monoid_with_zero.to_monoid R (@semiring.to_monoid_with_zero R hR))
  (λ R₁ R₂, ring_hom.to_monoid_hom) (λ _ _ _, rfl)

instance has_forget_to_AddCommMon : has_forget₂ SemiRing AddCommMon :=
-- can't use bundled_hom.mk_has_forget₂, since AddCommMon is an induced category
{ forget₂ :=
  { obj := λ R, AddCommMon.of R,
    map := λ R₁ R₂ f, ring_hom.to_add_monoid_hom f } }

end SemiRing

/-- The category of rings. -/
def Ring : Type (u+1) := bundled ring

namespace Ring

instance : bundled_hom.parent_projection @ring.to_semiring := ⟨⟩

attribute [derive [(λ Ring, has_coe_to_sort Ring Type*), large_category, concrete_category]] Ring

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [ring R] : Ring := bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `Ring`. -/
def of_hom {R S : Type u} [ring R] [ring S] (f : R →+* S) : of R ⟶ of S := f

@[simp] lemma of_hom_apply {R S : Type u} [ring R] [ring S] (f : R →+* S) (x : R) :
  of_hom f x = f x := rfl

instance : inhabited Ring := ⟨of punit⟩

instance (R : Ring) : ring R := R.str

@[simp] lemma coe_of (R : Type u) [ring R] : (Ring.of R : Type u) = R := rfl

instance has_forget_to_SemiRing : has_forget₂ Ring SemiRing := bundled_hom.forget₂ _ _
instance has_forget_to_AddCommGroup : has_forget₂ Ring AddCommGroup :=
-- can't use bundled_hom.mk_has_forget₂, since AddCommGroup is an induced category
{ forget₂ :=
  { obj := λ R, AddCommGroup.of R,
    map := λ R₁ R₂ f, ring_hom.to_add_monoid_hom f } }

end Ring

/-- The category of commutative semirings. -/
def CommSemiRing : Type (u+1) := bundled comm_semiring

namespace CommSemiRing

instance : bundled_hom.parent_projection @comm_semiring.to_semiring := ⟨⟩

attribute [derive [large_category, concrete_category]] CommSemiRing

instance : has_coe_to_sort CommSemiRing Type* := bundled.has_coe_to_sort

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_semiring R] : CommSemiRing := bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `CommSemiRing`. -/
def of_hom {R S : Type u} [comm_semiring R] [comm_semiring S] (f : R →+* S) : of R ⟶ of S := f

@[simp]
lemma of_hom_apply {R S : Type u} [comm_semiring R] [comm_semiring S] (f : R →+* S) (x : R) :
  of_hom f x = f x := rfl

instance : inhabited CommSemiRing := ⟨of punit⟩

instance (R : CommSemiRing) : comm_semiring R := R.str

@[simp] lemma coe_of (R : Type u) [comm_semiring R] : (CommSemiRing.of R : Type u) = R := rfl

instance has_forget_to_SemiRing : has_forget₂ CommSemiRing SemiRing := bundled_hom.forget₂ _ _

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommMon : has_forget₂ CommSemiRing CommMon :=
has_forget₂.mk'
  (λ R : CommSemiRing, CommMon.of R) (λ R, rfl)
  (λ R₁ R₂ f, f.to_monoid_hom) (by tidy)

end CommSemiRing

/-- The category of commutative rings. -/
def CommRing : Type (u+1) := bundled comm_ring

namespace CommRing

instance : bundled_hom.parent_projection @comm_ring.to_ring := ⟨⟩

attribute [derive [large_category, concrete_category]] CommRing

instance : has_coe_to_sort CommRing Type* := bundled.has_coe_to_sort

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_ring R] : CommRing := bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `CommRing`. -/
def of_hom {R S : Type u} [comm_ring R] [comm_ring S] (f : R →+* S) : of R ⟶ of S := f

@[simp] lemma of_hom_apply {R S : Type u} [comm_ring R] [comm_ring S] (f : R →+* S) (x : R) :
  of_hom f x = f x := rfl

instance : inhabited CommRing := ⟨of punit⟩

instance (R : CommRing) : comm_ring R := R.str

@[simp] lemma coe_of (R : Type u) [comm_ring R] : (CommRing.of R : Type u) = R := rfl

instance has_forget_to_Ring : has_forget₂ CommRing Ring := bundled_hom.forget₂ _ _

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommSemiRing : has_forget₂ CommRing CommSemiRing :=
has_forget₂.mk' (λ R : CommRing, CommSemiRing.of R) (λ R, rfl) (λ R₁ R₂ f, f) (by tidy)

instance : full (forget₂ CommRing CommSemiRing) :=
{ preimage := λ X Y f, f, }

end CommRing

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `add_ring_hom.map_zero` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
example {R S : CommRing} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 :=
by simp [h]

namespace ring_equiv

variables {X Y : Type u}

/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
@[simps] def to_Ring_iso [ring X] [ring Y] (e : X ≃+* Y) : Ring.of X ≅ Ring.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
@[simps] def to_CommRing_iso [comm_ring X] [comm_ring Y] (e : X ≃+* Y) :
  CommRing.of X ≅ CommRing.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

end ring_equiv

namespace category_theory.iso

/-- Build a `ring_equiv` from an isomorphism in the category `Ring`. -/
def Ring_iso_to_ring_equiv {X Y : Ring} (i : X ≅ Y) : X ≃+* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_mul'  := by tidy }.

/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def CommRing_iso_to_ring_equiv {X Y : CommRing} (i : X ≅ Y) : X ≃+* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_mul'  := by tidy }.

@[simp]
lemma CommRing_iso_to_ring_equiv_to_ring_hom {X Y : CommRing} (i : X ≅ Y) :
  i.CommRing_iso_to_ring_equiv.to_ring_hom = i.hom := by { ext, refl }

@[simp]
lemma CommRing_iso_to_ring_equiv_symm_to_ring_hom {X Y : CommRing} (i : X ≅ Y) :
  i.CommRing_iso_to_ring_equiv.symm.to_ring_hom = i.inv := by { ext, refl }

end category_theory.iso

/-- Ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ring_equiv_iso_Ring_iso {X Y : Type u} [ring X] [ring Y] :
  (X ≃+* Y) ≅ (Ring.of X ≅ Ring.of Y) :=
{ hom := λ e, e.to_Ring_iso,
  inv := λ i, i.Ring_iso_to_ring_equiv, }

/-- Ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms
in `CommRing`. -/
def ring_equiv_iso_CommRing_iso {X Y : Type u} [comm_ring X] [comm_ring Y] :
  (X ≃+* Y) ≅ (CommRing.of X ≅ CommRing.of Y) :=
{ hom := λ e, e.to_CommRing_iso,
  inv := λ i, i.CommRing_iso_to_ring_equiv, }

instance Ring.forget_reflects_isos : reflects_isomorphisms (forget Ring.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget Ring).map f),
    let e : X ≃+* Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_Ring_iso).1⟩,
  end }

instance CommRing.forget_reflects_isos : reflects_isomorphisms (forget CommRing.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CommRing).map f),
    let e : X ≃+* Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CommRing_iso).1⟩,
  end }

-- It would be nice if we could have the following,
-- but it requires making `reflects_isomorphisms_forget₂` an instance,
-- which can cause typeclass loops:

local attribute [priority 50,instance] reflects_isomorphisms_forget₂
example : reflects_isomorphisms (forget₂ Ring AddCommGroup) := by apply_instance
