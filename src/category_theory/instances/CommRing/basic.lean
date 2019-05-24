/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.
-/

import category_theory.instances.Mon.basic
import category_theory.fully_faithful
import algebra.ring
import data.int.basic

universes u v

open category_theory

/-- The category of rings. -/
@[reducible] def Ring : Type (u+1) := bundled ring

/-- The category of commutative rings. -/
@[reducible] def CommRing : Type (u+1) := bundled comm_ring

namespace Ring

instance (x : Ring) : ring x := x.str

instance concrete_is_ring_hom : concrete_category @is_ring_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (α : Type u) [ring α] : Ring := ⟨α⟩

instance hom_is_ring_hom {R S : Ring} (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

end Ring

namespace CommRing

instance (x : CommRing) : comm_ring x := x.str

@[reducible] def is_comm_ring_hom {α β} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
is_ring_hom f

instance concrete_is_comm_ring_hom : concrete_category @is_comm_ring_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (α : Type u) [comm_ring α] : CommRing := ⟨α⟩

instance hom_is_ring_hom {R S : CommRing} (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

variables {R S T : CommRing.{u}}

-- TODO need to kill these
@[simp] lemma id_val : subtype.val (𝟙 R) = id := rfl
@[simp] lemma comp_val (f : R ⟶ S) (g : S ⟶ T) :
  (f ≫ g).val = g.val ∘ f.val := rfl

-- TODO rename the next three lemmas?
def Int.cast {R : CommRing} : CommRing.of ℤ ⟶ R := { val := int.cast, property := by apply_instance }

def Int.hom_unique {R : CommRing} : unique (CommRing.of ℤ ⟶ R) :=
{ default := Int.cast,
  uniq := λ f, subtype.ext.mpr $ funext $ int.eq_cast f f.2.map_one f.2.map_add }

/-- The forgetful functor commutative rings to Type. -/
def forget : CommRing.{u} ⥤ Type u :=
{ obj := λ R, R,
  map := λ _ _ f, f }

instance forget.faithful : faithful (forget) := {}

instance forget_comm_ring (R : CommRing) : comm_ring (forget.obj R) := R.str
instance forget_is_ring_hom {R S : CommRing} (f : R ⟶ S) : is_ring_hom (forget.map f) := f.property

/-- The functor from commutative rings to rings. -/
def to_Ring : CommRing.{u} ⥤ Ring.{u} :=
{ obj := λ X, { α := X.1 },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance to_Ring.faithful : faithful (to_Ring) := {}

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
def forget_to_CommMon : CommRing.{u} ⥤ CommMon.{u} :=
{ obj := λ X, { α := X.1 },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance forget_to_CommMon.faithful : faithful (forget_to_CommMon) := {}

example : faithful (forget_to_CommMon ⋙ CommMon.forget_to_Mon) := by apply_instance

end CommRing
